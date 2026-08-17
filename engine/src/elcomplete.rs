//! ELK-style EL++ completion over the frontend's normalised DL-clauses.
//!
//! Rust port of `engine/py/el_route.py` (`to_nf` + `classify`) and
//! `moose.elpp.completion` (the worklist saturation of Kazakov–Krötzsch–Simančík,
//! *The Incredible ELK*, JAR 2014, §4). The Python EL fast path is exact but its
//! interpreter overhead times out on the large EL ontologies that ELK/Konclude
//! classify in seconds (e.g. ore_ont_1559 375MB, ore_ont_13482 170MB). This
//! module is the same algorithm, compiled and with concept/role names interned to
//! `u32`, so the worklist runs over integer-keyed arrays instead of Python dicts.
//!
//! Entry point: [`classify`] takes the JSON clause set and returns either the
//! engine-shaped subsumption result (when the whole clause set lies in EL++) or
//! `None` (caller must fall back to the disjunctive context engine). The
//! EL-membership test is `to_nf`: it fires only when *every* clause maps onto one
//! of the EL++ normal forms NF1–NF7, exactly as the Python router does.

use std::collections::VecDeque;
use std::hash::{BuildHasherDefault, Hasher};

use rayon::prelude::*;

use crate::json_io::{JAtom, JClause, JTerm};

// ---------------------------------------------------------------------------
// Fast hashing for the integer-keyed saturation state
// ---------------------------------------------------------------------------
//
// The saturation is dominated by membership/lookup on `u32` (concept/role id)
// and `(u32,u32)` keys. std's default SipHash is cryptographic and far too slow
// for that hot path; an FxHash-style multiply-rotate hasher (the rustc-hash
// algorithm) is ~an order of magnitude faster on small integer keys and needs no
// extra dependency.

#[derive(Default)]
struct FxHasher {
    hash: u64,
}

const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

impl FxHasher {
    #[inline]
    fn add(&mut self, i: u64) {
        self.hash = (self.hash.rotate_left(5) ^ i).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.add(b as u64);
        }
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

type FxBuild = BuildHasherDefault<FxHasher>;
type HashMap<K, V> = std::collections::HashMap<K, V, FxBuild>;
type HashSet<T> = std::collections::HashSet<T, FxBuild>;

// ---------------------------------------------------------------------------
// String interning
// ---------------------------------------------------------------------------

/// Maps concept/role/individual names to dense `u32` ids. `⊤` and `⊥` get the
/// first two ids so the saturation can branch on them by integer compare.
#[derive(Clone)]
struct Interner {
    map: HashMap<String, u32>,
    names: Vec<String>,
}

const TOP: u32 = 0;
const BOTTOM: u32 = 1;

impl Interner {
    fn new() -> Self {
        let mut i = Interner {
            map: HashMap::default(),
            names: Vec::new(),
        };
        i.intern("\u{22a4}"); // ⊤ -> 0
        i.intern("\u{22a5}"); // ⊥ -> 1
        i
    }

    fn intern(&mut self, s: &str) -> u32 {
        if let Some(&id) = self.map.get(s) {
            return id;
        }
        let id = self.names.len() as u32;
        self.names.push(s.to_string());
        self.map.insert(s.to_string(), id);
        id
    }

    fn name(&self, id: u32) -> &str {
        &self.names[id as usize]
    }

    /// Non-creating lookup (P1 hoisting reads ids of already-seen concepts only).
    fn id(&self, s: &str) -> Option<u32> {
        self.map.get(s).copied()
    }

    fn len(&self) -> usize {
        self.names.len()
    }
}

// ---------------------------------------------------------------------------
// Normal forms (interned)
// ---------------------------------------------------------------------------

struct Nf1 {
    sub: u32,
    sup: u32,
}
struct Nf2 {
    sub1: u32,
    sub2: u32,
    sup: u32,
}
struct Nf3 {
    sub: u32,
    role: u32,
    filler: u32,
}
struct Nf4 {
    role: u32,
    filler: u32,
    sup: u32,
}
struct Nf6 {
    sub: u32,
    sup: u32,
}
struct Nf7 {
    r1: u32,
    r2: u32,
    sup: u32,
}

/// Collected EL++ normal forms plus the concept/role signatures.
struct Nfs {
    nf1: Vec<Nf1>,
    nf2: Vec<Nf2>,
    nf3: Vec<Nf3>,
    nf4: Vec<Nf4>,
    nf5: Vec<u32>, // A ⊑ ⊥, by sub
    nf6: Vec<Nf6>,
    nf7: Vec<Nf7>,
    // EL++ reflexive roles (ReflexiveObjectProperty), parsed from the frontend
    // fact `[] -> R(x,x)`. Closed up the role hierarchy in `build_idx` and
    // materialised as self-edges in `classify_inner`.
    reflexive_roles: HashSet<u32>,
    concept_names: HashSet<u32>,
    role_names: HashSet<u32>,
    /// Exact source-prefix identity of every generated conjunction concept.
    conjunction_origins: HashMap<u32, Vec<u32>>,
}

/// Set view of direct normal forms. Most addition transactions extend this set
/// monotonically. The exception is a Skolem role half that was initially read
/// as `A ⊑ ∃R.⊤` and later receives its filler half: `to_nf` then replaces
/// that NF3 with `A ⊑ ∃R.B`. An incremental session detects that rewrite and
/// falls back to a fresh completion instead of retaining facts from a rule that
/// is no longer present.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum NormalFormKey {
    Nf1(u32, u32),
    Nf2(u32, u32, u32),
    Nf3(u32, u32, u32),
    Nf4(u32, u32, u32),
    Nf5(u32),
    Nf6(u32, u32),
    Nf7(u32, u32, u32),
    Reflexive(u32),
}

fn normal_form_keys(nfs: &Nfs) -> HashSet<NormalFormKey> {
    let mut keys = HashSet::default();
    keys.extend(nfs.nf1.iter().map(|a| NormalFormKey::Nf1(a.sub, a.sup)));
    keys.extend(
        nfs.nf2
            .iter()
            .map(|a| NormalFormKey::Nf2(a.sub1, a.sub2, a.sup)),
    );
    keys.extend(
        nfs.nf3
            .iter()
            .map(|a| NormalFormKey::Nf3(a.sub, a.role, a.filler)),
    );
    keys.extend(
        nfs.nf4
            .iter()
            .map(|a| NormalFormKey::Nf4(a.role, a.filler, a.sup)),
    );
    keys.extend(nfs.nf5.iter().map(|&sub| NormalFormKey::Nf5(sub)));
    keys.extend(nfs.nf6.iter().map(|a| NormalFormKey::Nf6(a.sub, a.sup)));
    keys.extend(
        nfs.nf7
            .iter()
            .map(|a| NormalFormKey::Nf7(a.r1, a.r2, a.sup)),
    );
    keys.extend(
        nfs.reflexive_roles
            .iter()
            .map(|&role| NormalFormKey::Reflexive(role)),
    );
    keys
}

// ---------------------------------------------------------------------------
// to_nf: map frontend DL-clauses to EL++ normal forms
// ---------------------------------------------------------------------------

/// Term kind, matching `el_route._tk`. The `&str` borrows live only within the
/// per-clause scan.
enum Tk<'a> {
    Var(&'a str),
    /// existential filler term `f(x)`: function and exact argument variable.
    Fun(&'a str, &'a str),
    /// `ind` / `aux`: not an EL normal-form tree term.
    Other,
}

fn tk(t: &JTerm) -> Tk<'_> {
    match t {
        JTerm::Var { name } => Tk::Var(name),
        JTerm::Fun { function, arg } => match arg.as_ref() {
            JTerm::Var { name } => Tk::Fun(function, name),
            _ => Tk::Other,
        },
        _ => Tk::Other,
    }
}

/// Variable name of a term, if it is a variable. The `&str` borrows the
/// underlying `JTerm`, so it outlives the transient `Tk`.
fn vname<'a>(t: &Tk<'a>) -> Option<&'a str> {
    match t {
        Tk::Var(n) => Some(n),
        _ => None,
    }
}

/// Concept name / term of a concept atom; helper for readability.
fn concept_of(a: &JAtom) -> Option<(&str, &JTerm)> {
    if let JAtom::Concept { concept, term } = a {
        Some((concept.as_str(), term))
    } else {
        None
    }
}

fn var_name(term: &JTerm) -> Option<&str> {
    if let JTerm::Var { name } = term {
        Some(name)
    } else {
        None
    }
}

fn fun_parts(term: &JTerm) -> Option<(&str, &str)> {
    if let JTerm::Fun { function, arg } = term {
        Some((function, var_name(arg)?))
    } else {
        None
    }
}

/// Zero-copy membership screen for the cert-off EL worker.
///
/// This deliberately mirrors every accepted branch of [`to_nf`], including
/// its exact variable-wiring checks and its asymmetric existential halves. It
/// borrows names from the already-built JSON clauses and allocates only the
/// small pending-half table. The automatic router uses it after normalisation:
/// a source-profile leaf may propose ELC, but only this exact clause-level test
/// may authorize that worker.
pub(crate) fn is_pure_el_shape(clauses: &[JClause]) -> bool {
    // (sub concept, skolem function) -> (role half, filler half). A role half
    // without a filler is A⊑∃R.⊤ and is accepted by `to_nf`; a filler without a
    // role is the one orphan shape for which `to_nf` returns None.
    let mut pending_ex: HashMap<(&str, &str), (bool, bool)> = HashMap::default();

    for clause in clauses {
        if clause
            .body
            .iter()
            .chain(clause.head.iter())
            .any(|atom| matches!(atom, JAtom::Eq { .. }))
        {
            return false;
        }

        if clause.head.is_empty() {
            // Mirror `to_nf`: every body concept on ONE shared variable.
            let shared = clause.body.first().and_then(|atom| match atom {
                JAtom::Concept { term, .. } => var_name(term),
                _ => None,
            });
            if clause.body.is_empty()
                || shared.is_none()
                || !clause.body.iter().all(|atom| {
                    matches!(
                        atom,
                        JAtom::Concept { term, .. } if var_name(term) == shared
                    )
                })
            {
                return false;
            }
            continue;
        }
        if clause.head.len() != 1 {
            return false;
        }

        match &clause.head[0] {
            JAtom::Concept { term, .. } if var_name(term).is_some() => {
                let head_var = var_name(term);
                // NF1/NF2 (including top and n-ary conjunction): every body
                // atom is a variable concept ON THE HEAD VARIABLE. As in
                // `to_nf`, a variable mismatch (`A(x) ∧ B(y) → C(x)`) is not
                // a conjunction axiom and must be rejected to the residual.
                if clause.body.iter().all(|atom| {
                    matches!(
                        atom,
                        JAtom::Concept { term, .. } if var_name(term) == head_var
                    )
                }) {
                    continue;
                }

                // Domain axiom `∃R.⊤ ⊑ B`: a lone role body atom with the head
                // on its SOURCE. `to_nf` accepts this as NF4 with filler ⊤
                // under exactly this wiring, so the screen must too.
                if let [JAtom::Role { source, target, .. }] = clause.body.as_slice() {
                    if var_name(source).is_some()
                        && var_name(target).is_some()
                        && var_name(source) == head_var
                        && var_name(source) != var_name(target)
                    {
                        continue;
                    }
                    return false;
                }

                // NF4: R(x,y) ∧ A(y) -> B(x). Match the same wiring that
                // `to_nf` checks: filler variable equals the role target, the
                // head sits on the role source, and source ≠ target (a head on
                // the target or a self-loop body is NOT ∃R.A ⊑ B — reading it
                // so is unsound).
                if clause.body.len() == 2 {
                    let mut role = None;
                    let mut filler = None;
                    for atom in &clause.body {
                        match atom {
                            JAtom::Role { source, target, .. } if role.is_none() => {
                                role = Some((source, target));
                            }
                            JAtom::Concept { term, .. } if filler.is_none() => {
                                filler = Some(term);
                            }
                            _ => return false,
                        }
                    }
                    if let (Some((source, target)), Some(filler)) = (role, filler) {
                        if var_name(source).is_some()
                            && var_name(target).is_some()
                            && var_name(target) == var_name(filler)
                            && var_name(source) == head_var
                            && var_name(source) != var_name(target)
                        {
                            continue;
                        }
                    }
                }
                return false;
            }
            JAtom::Concept { term, .. } => {
                // Existential filler half: A(x) -> B(f(x)).
                let Some((function, argument)) = fun_parts(term) else {
                    return false;
                };
                let [JAtom::Concept {
                    concept: sub,
                    term: sub_term,
                }] = clause.body.as_slice()
                else {
                    return false;
                };
                if var_name(sub_term) != Some(argument) {
                    return false;
                }
                pending_ex.entry((sub, function)).or_default().1 = true;
            }
            JAtom::Role { source, target, .. } => {
                // Reflexive role fact: [] -> R(x,x).
                if clause.body.is_empty()
                    && var_name(source).is_some()
                    && var_name(source) == var_name(target)
                {
                    continue;
                }

                // Existential role half: A(x) -> R(x,f(x)).
                if let Some((function, argument)) = fun_parts(target) {
                    if var_name(source) == Some(argument) {
                        if let [JAtom::Concept {
                            concept: sub,
                            term: sub_term,
                        }] = clause.body.as_slice()
                        {
                            if var_name(sub_term) == Some(argument) {
                                pending_ex.entry((sub, function)).or_default().0 = true;
                                continue;
                            }
                        }
                    }
                    return false;
                }

                // Forward role inclusion: R(x,y) -> S(x,y), with exact head
                // and body orientation (inverse bridges must not pass).
                if let [JAtom::Role {
                    source: body_source,
                    target: body_target,
                    ..
                }] = clause.body.as_slice()
                {
                    if var_name(body_source).is_some()
                        && var_name(body_target).is_some()
                        && var_name(body_source) != var_name(body_target)
                        && var_name(body_source) == var_name(source)
                        && var_name(body_target) == var_name(target)
                    {
                        continue;
                    }
                }

                // Connected two-role chain in either body order.
                if let [JAtom::Role {
                    source: a0,
                    target: a1,
                    ..
                }, JAtom::Role {
                    source: b0,
                    target: b1,
                    ..
                }] = clause.body.as_slice()
                {
                    let ordered = var_name(a0) != var_name(a1)
                        && var_name(a1) != var_name(b1)
                        && var_name(a0) != var_name(b1)
                        && var_name(a1) == var_name(b0)
                        && var_name(source) == var_name(a0)
                        && var_name(target) == var_name(b1);
                    let reversed = var_name(b0) != var_name(b1)
                        && var_name(b1) != var_name(a1)
                        && var_name(b0) != var_name(a1)
                        && var_name(b1) == var_name(a0)
                        && var_name(source) == var_name(b0)
                        && var_name(target) == var_name(a1);
                    let all_variables = [a0, a1, b0, b1, source, target]
                        .into_iter()
                        .all(|term| var_name(term).is_some());
                    if all_variables && (ordered || reversed) {
                        continue;
                    }
                }
                return false;
            }
            JAtom::Eq { .. } => return false,
        }
    }

    pending_ex.values().all(|(role, _filler)| *role)
}

// ---------------------------------------------------------------------------
// Inverse-role bridge preprocessing
// ---------------------------------------------------------------------------
//
// A frontend that clausifies `InverseObjectProperties(R S)` emits the pair of
// *bridge* clauses `R(x,y) → S(y,x)` and `S(x,y) → R(y,x)`. Neither is an EL
// normal form, so both land in the residual and the certificate has to satisfy
// them over the canonical model — which means mirroring the whole role graph.
// On a role with tens of millions of edges that is the dominant cost.
//
// Two exact rewrites are applied here, and one tempting rewrite is deliberately
// NOT applied.
//
// 1. VACUOUS-ROLE ELIMINATION. If a role `R` occurs in no clause head, then no
//    completion rule and no assertion can ever put a pair into `R`. Setting
//    `R^I = ∅` therefore satisfies every clause that mentions `R` only in its
//    body, and it satisfies them under *any* interpretation of the rest. So all
//    such clauses may be deleted outright: `O` and the pruned `O'` have the same
//    concept-name entailments (see `prune_vacuous_role_clauses`). This removes
//    one-way bridges `R(x,y) → S(y,x)` whose `R` is otherwise unused, and with
//    them the range/domain clauses those roles carry.
//
// 2. MUTUAL-INVERSE SUBSTITUTION. Both bridges together pin `S = R⁻` in every
//    model, so replacing each atom `S(a,b)` by `R(b,a)` is model-preserving:
//    from a model of the rewritten set, defining `S^I := (R^I)⁻` recovers a
//    model of the original with identical concept extensions, and conversely.
//    The bridges then read `R(x,y) → R(x,y)` and are dropped as tautologies.
//    Applied ONLY when the substitution leaves no EL completion rule reversed
//    (`inverse_substitution_is_exact`); otherwise the pair is left alone and the
//    residual keeps both bridges, so the certificate still has to discharge them
//    and fails closed if it cannot.
//
// 3. NOT APPLIED: extending the completion with reverse-oriented NF3/NF4 so that
//    a pair can always be oriented. That is unsound in this calculus, and
//    `reverse_oriented_inverse_nf4_would_be_unsound` is the countermodel. A node
//    here denotes *the* generic instance of a concept name and every
//    `X ⊑ ∃R.D` shares the one successor node `D`, so a reverse-oriented rule
//    concludes at that shared successor from one of its predecessors and asserts
//    of all `D` instances what holds only of the `D` instances that have such a
//    predecessor. Making it sound requires the successor to carry `∃R⁻.X` as
//    part of its identity, i.e. a context (concept-set) calculus, which is the
//    CB engine and not this completion.

fn atom_eq(a: &JAtom, b: &JAtom) -> bool {
    fn term_eq(a: &JTerm, b: &JTerm) -> bool {
        match (a, b) {
            (JTerm::Var { name: x }, JTerm::Var { name: y }) => x == y,
            (JTerm::Ind { name: x }, JTerm::Ind { name: y }) => x == y,
            (
                JTerm::Fun {
                    function: f,
                    arg: x,
                },
                JTerm::Fun {
                    function: g,
                    arg: y,
                },
            ) => f == g && term_eq(x, y),
            (JTerm::Aux { root: r1, label: l1 }, JTerm::Aux { root: r2, label: l2 }) => {
                r1 == r2 && l1 == l2
            }
            _ => false,
        }
    }
    match (a, b) {
        (
            JAtom::Concept {
                concept: c1,
                term: t1,
            },
            JAtom::Concept {
                concept: c2,
                term: t2,
            },
        ) => c1 == c2 && term_eq(t1, t2),
        (
            JAtom::Role {
                role: r1,
                source: s1,
                target: t1,
            },
            JAtom::Role {
                role: r2,
                source: s2,
                target: t2,
            },
        ) => r1 == r2 && term_eq(s1, s2) && term_eq(t1, t2),
        (JAtom::Eq { left: l1, right: r1 }, JAtom::Eq { left: l2, right: r2 }) => {
            term_eq(l1, l2) && term_eq(r1, r2)
        }
        _ => false,
    }
}

/// A clause with a head disjunct that already appears in its body holds in every
/// interpretation and can be deleted.
fn is_tautology(c: &JClause) -> bool {
    c.head.iter().any(|h| c.body.iter().any(|b| atom_eq(b, h)))
}

fn mentions_role(c: &JClause, role: &str) -> bool {
    c.body
        .iter()
        .chain(c.head.iter())
        .any(|a| matches!(a, JAtom::Role { role: r, .. } if r == role))
}

/// Delete every clause whose body mentions a role that occurs in no clause head.
///
/// Soundness. Let `R` occur in no head of `O`, and let `O'` be `O` minus the
/// clauses whose body mentions `R`. Every clause of `O'` is `R`-free (a clause
/// keeping `R` would have it in a head, and there are none). Given `I' ⊨ O'`,
/// let `I` agree with `I'` everywhere except `R^I = ∅`. Then `I ⊨ O'` still, and
/// every deleted clause has an unsatisfiable body under `I`, so `I ⊨ O`. `I` and
/// `I'` agree on all concept names, so `O` and `O'` entail exactly the same
/// concept-name subsumptions and are equiconsistent. Iterated to a fixpoint,
/// since deleting a clause can leave a further role head-free.
///
/// This also keeps the certificate honest rather than merely cheaper: no rule
/// can add an `R` edge either, so the canonical model already has `R^I = ∅` and
/// satisfies every deleted clause.
fn prune_vacuous_role_clauses(clauses: &mut Vec<JClause>) -> (usize, usize) {
    let mut removed_clauses = 0usize;
    let mut removed_roles: HashSet<String> = HashSet::default();
    loop {
        let mut head_roles: HashSet<&str> = HashSet::default();
        for c in clauses.iter() {
            for a in &c.head {
                if let JAtom::Role { role, .. } = a {
                    head_roles.insert(role.as_str());
                }
            }
        }
        let vacuous: HashSet<String> = clauses
            .iter()
            .flat_map(|c| c.body.iter())
            .filter_map(|a| match a {
                JAtom::Role { role, .. } if !head_roles.contains(role.as_str()) => {
                    Some(role.clone())
                }
                _ => None,
            })
            .collect();
        if vacuous.is_empty() {
            break;
        }
        let before = clauses.len();
        clauses.retain(|c| {
            !c.body
                .iter()
                .any(|a| matches!(a, JAtom::Role { role, .. } if vacuous.contains(role)))
        });
        removed_clauses += before - clauses.len();
        removed_roles.extend(vacuous);
    }
    (removed_clauses, removed_roles.len())
}

/// The bridge shape `R(x,y) → S(y,x)` over two distinct roles and two distinct
/// variables, returned as `(R, S)`.
fn as_inverse_bridge(c: &JClause) -> Option<(&str, &str)> {
    let ([b], [h]) = (c.body.as_slice(), c.head.as_slice()) else {
        return None;
    };
    let (
        JAtom::Role {
            role: r,
            source: rs,
            target: rt,
        },
        JAtom::Role {
            role: s,
            source: ss,
            target: st,
        },
    ) = (b, h)
    else {
        return None;
    };
    let (
        JTerm::Var { name: rx },
        JTerm::Var { name: ry },
        JTerm::Var { name: sx },
        JTerm::Var { name: sy },
    ) = (rs, rt, ss, st)
    else {
        return None;
    };
    (r != s && rx != ry && rx == sy && ry == sx).then_some((r.as_str(), s.as_str()))
}

/// Pairs `(R, S)` for which BOTH bridges are present, so `S = R⁻` holds in every
/// model. Fails closed on an ambiguous inverse graph: a role with more than one
/// reciprocal partner is skipped rather than quotiented, because collapsing a
/// whole signed component is a different (and order-sensitive) rewrite.
fn mutual_inverse_pairs(clauses: &[JClause]) -> Vec<(String, String)> {
    let mut implies: HashMap<&str, HashSet<&str>> = HashMap::default();
    for c in clauses {
        if let Some((r, s)) = as_inverse_bridge(c) {
            implies.entry(r).or_default().insert(s);
        }
    }
    let mut pairs = Vec::new();
    for (&r, partners) in &implies {
        if partners.len() != 1 {
            continue;
        }
        let s = *partners.iter().next().unwrap();
        if r >= s {
            continue; // emit each pair once, from its lexicographically smaller side
        }
        if implies
            .get(s)
            .is_some_and(|back| back.len() == 1 && back.contains(r))
        {
            pairs.push((r.to_string(), s.to_string()));
        }
    }
    pairs.sort();
    pairs
}

/// Would `to_nf` file this clause as an EL completion rule (as opposed to a
/// residual constraint)? Conservative in the safe direction: it may say `true`
/// for a clause `to_nf` would actually residualise, never the converse.
///
/// The shapes that matter are the ones whose meaning depends on the ORIENTATION
/// of a role atom, because that is exactly what the inverse substitution flips:
/// a role atom in the head (NF3 `A ⊑ ∃R.f(x)`, a role inclusion, a chain
/// conclusion), and a single-role body with a single concept head (NF4
/// `∃R.C ⊑ D`, and the domain form with an implicit `⊤` filler). Everything else
/// is checked as a first-order constraint over the finished model, where a
/// swapped role atom is evaluated, not fired, and the rewrite is exact.
fn clause_is_orientation_sensitive(c: &JClause) -> bool {
    let head_roles = c
        .head
        .iter()
        .filter(|a| matches!(a, JAtom::Role { .. }))
        .count();
    if head_roles > 0 {
        return true;
    }
    let body_roles = c
        .body
        .iter()
        .filter(|a| matches!(a, JAtom::Role { .. }))
        .count();
    body_roles == 1 && c.head.len() == 1 && matches!(c.head[0], JAtom::Concept { .. })
}

/// May every `victim` atom be replaced by a `canonical` atom with swapped
/// endpoints?
///
/// The rewrite itself is model-preserving for any proven mutual pair. The extra
/// condition here is about what the rewritten clauses are then USED for: a
/// swapped role atom inside an EL normal form turns that normal form into a
/// reverse-oriented rule, which this completion cannot run soundly (see the
/// module note and `reverse_oriented_inverse_nf4_would_be_unsound`). So the
/// substitution is admitted only when no clause mentioning `victim` — other
/// than the two bridges, which become tautologies — is orientation-sensitive.
fn inverse_substitution_is_exact(clauses: &[JClause], victim: &str) -> bool {
    clauses.iter().all(|c| {
        !mentions_role(c, victim)
            || as_inverse_bridge(c).is_some_and(|(r, s)| r == victim || s == victim)
            || !clause_is_orientation_sensitive(c)
    })
}

fn substitute_inverse(clauses: &mut [JClause], victim: &str, canonical: &str) {
    for c in clauses.iter_mut() {
        for a in c.body.iter_mut().chain(c.head.iter_mut()) {
            if let JAtom::Role {
                role,
                source,
                target,
            } = a
            {
                if role == victim {
                    *role = canonical.to_string();
                    std::mem::swap(source, target);
                }
            }
        }
    }
}

/// Apply the two exact rewrites above, to a fixpoint. Returns
/// `(clauses_removed, roles_eliminated)` for diagnostics.
fn prepare_inverse_bridges(clauses: &mut Vec<JClause>, debug: bool) -> (usize, usize) {
    let start = clauses.len();
    let (mut pruned, mut vacuous_roles) = prune_vacuous_role_clauses(clauses);
    let mut eliminated: Vec<(String, String)> = Vec::new();
    for (r, s) in mutual_inverse_pairs(clauses) {
        // Either side may be the one eliminated; prefer whichever keeps the
        // completion forward-oriented. Both, neither, or exactly one may work.
        let victim = if inverse_substitution_is_exact(clauses, &s) {
            Some((s.clone(), r.clone()))
        } else if inverse_substitution_is_exact(clauses, &r) {
            Some((r.clone(), s.clone()))
        } else {
            None
        };
        let Some((victim, canonical)) = victim else {
            if debug {
                eprintln!(
                    "KM_ELC_CERT inverse pair {r}/{s}: neither orientation is exact \
                     (both sides carry EL rules); bridges kept in the residual"
                );
            }
            continue;
        };
        substitute_inverse(clauses, &victim, &canonical);
        eliminated.push((victim, canonical));
    }
    if !eliminated.is_empty() {
        let before = clauses.len();
        clauses.retain(|c| !is_tautology(c));
        pruned += before - clauses.len();
        let (again, roles) = prune_vacuous_role_clauses(clauses);
        pruned += again;
        vacuous_roles += roles;
    }
    if debug && (pruned > 0 || !eliminated.is_empty()) {
        eprintln!(
            "KM_ELC_CERT bridge prep: {} clause(s) removed ({} -> {}), {} head-free role(s), \
             {} inverse pair(s) oriented{}",
            pruned,
            start,
            clauses.len(),
            vacuous_roles,
            eliminated.len(),
            eliminated
                .iter()
                .map(|(v, c)| format!(" [{v} := {c}⁻]"))
                .collect::<String>()
        );
    }
    (pruned, eliminated.len())
}

/// Map the clause set onto EL++ normal forms. Clauses outside EL++
/// (disjunctive head, equality/number atom, nominal `ind` term, unsupported
/// shape) are collected into the returned *residual* list instead of aborting:
/// the caller saturates the EL subset and then checks the residual clauses
/// against the canonical model (the completeness certificate). Returns `None`
/// only for an orphan existential-filler half-clause (a shape we don't model
/// at all).
/// Collision-free internal name for a conjunction prefix. Length prefixes make
/// component boundaries unambiguous even when source IRIs contain `/`, `:`, or
/// decimal digits. Source names that use KM's reserved prefix are escaped by
/// the frontend; the certificate wire additionally validates distinct IDs.
fn conjunction_aux_name(names: &[String]) -> String {
    let mut out = String::from("__conj__");
    for name in names {
        out.push_str(&name.len().to_string());
        out.push(':');
        out.push_str(name);
    }
    out
}

fn to_nf(
    clauses: &[JClause],
    it: &mut Interner,
) -> Option<(Nfs, Vec<JClause>, HashMap<u32, (u32, u32, u32)>)> {
    let mut nf1 = Vec::new();
    let mut nf2 = Vec::new();
    let mut nf3 = Vec::new();
    let mut nf4 = Vec::new();
    let mut nf5 = Vec::new();
    let mut nf6 = Vec::new();
    let mut nf7 = Vec::new();
    let mut reflexive_roles: HashSet<u32> = HashSet::default();
    let mut concept_names: HashSet<u32> = HashSet::default();
    let mut role_names: HashSet<u32> = HashSet::default();
    let mut conjunction_origins: HashMap<u32, Vec<u32>> = HashMap::default();

    // (sub_concept, skolem_fn) -> (role, filler) halves of an A ⊑ ∃R.B axiom.
    let mut pending_ex: HashMap<(u32, u32), (Option<u32>, Option<u32>)> = HashMap::default();
    // Clauses outside the EL++ normal forms, kept for the certificate check.
    let mut residual: Vec<JClause> = Vec::new();

    // Helpers that intern + record the signature as a side effect.
    macro_rules! addc {
        ($v:expr) => {{
            let id = it.intern($v);
            concept_names.insert(id);
            id
        }};
    }
    macro_rules! addr {
        ($v:expr) => {{
            let id = it.intern($v);
            role_names.insert(id);
            id
        }};
    }

    for c in clauses {
        let b = &c.body;
        let h = &c.head;
        // equality / inequality atoms (number restrictions, nominal merge) -> not EL
        if b.iter()
            .chain(h.iter())
            .any(|a| matches!(a, JAtom::Eq { .. }))
        {
            residual.push(c.clone());
            continue;
        }
        let bc: Vec<&JAtom> = b.iter().filter(|a| concept_of(a).is_some()).collect();
        let br: Vec<&JAtom> = b
            .iter()
            .filter(|a| matches!(a, JAtom::Role { .. }))
            .collect();
        let hc: Vec<&JAtom> = h.iter().filter(|a| concept_of(a).is_some()).collect();
        let hr: Vec<&JAtom> = h
            .iter()
            .filter(|a| matches!(a, JAtom::Role { .. }))
            .collect();

        // empty head => ⊥ (NF5 / disjointness). Every body concept must sit on
        // ONE shared variable: `A(x) ∧ B(y) → ⊥` is a global constraint (A
        // empty or B empty), not `A ⊓ B ⊑ ⊥` — misreading it is incomplete,
        // so a variable mismatch falls to `residual` (cert-off: defer).
        if h.is_empty() {
            let shared = bc
                .first()
                .and_then(|a| vname(&tk(concept_of(a).unwrap().1)));
            let all_var = shared.is_some()
                && bc.iter().all(
                    |a| matches!(tk(concept_of(a).unwrap().1), Tk::Var(v) if Some(v) == shared),
                );
            if br.is_empty() && !bc.is_empty() && all_var {
                if bc.len() == 1 {
                    let s = addc!(concept_of(bc[0]).unwrap().0);
                    nf5.push(s);
                    continue;
                }
                // A1⊓…⊓Ak ⊑ ⊥ : binary-decompose (k>=2)
                let mut names: Vec<String> = bc
                    .iter()
                    .map(|a| concept_of(a).unwrap().0.to_string())
                    .collect();
                names.sort();
                let mut acc = names[0].clone();
                for j in 1..names.len() - 1 {
                    let aux = conjunction_aux_name(&names[..=j]);
                    let s1 = addc!(&acc);
                    let s2 = addc!(&names[j]);
                    let sup = addc!(&aux);
                    let prefix_ids = names[..=j]
                        .iter()
                        .map(|name| addc!(name))
                        .collect::<Vec<_>>();
                    conjunction_origins.insert(sup, prefix_ids);
                    nf2.push(Nf2 {
                        sub1: s1,
                        sub2: s2,
                        sup,
                    });
                    acc = aux;
                }
                let s1 = addc!(&acc);
                let s2 = addc!(&names[names.len() - 1]);
                nf2.push(Nf2 {
                    sub1: s1,
                    sub2: s2,
                    sup: BOTTOM,
                });
                concept_names.insert(BOTTOM);
                continue;
            }
            residual.push(c.clone());
            continue;
        }
        // disjunctive head => not EL (Horn only)
        if h.len() != 1 {
            residual.push(c.clone());
            continue;
        }

        // ---- concept head ----
        if !hc.is_empty() {
            let (hd_name, hd_term) = concept_of(hc[0]).unwrap();
            match tk(hd_term) {
                Tk::Var(hv) => {
                    // NF1/NF2 require every body concept on the HEAD variable:
                    // `A(x) ∧ B(y) → C(x)` is NOT `A ⊓ B ⊑ C` (reading it so is
                    // incomplete), so a variable mismatch must fall to
                    // `residual` (cert-off: defer to the CB engine) instead of
                    // being silently misread. The frontend's normalized shapes
                    // always share the central variable, so this rejects only
                    // out-of-contract input.
                    let all_var = bc
                        .iter()
                        .all(|a| matches!(tk(concept_of(a).unwrap().1), Tk::Var(v) if v == hv));
                    if br.is_empty() && all_var {
                        match bc.len() {
                            0 => {
                                let hd = addc!(hd_name);
                                concept_names.insert(TOP);
                                nf1.push(Nf1 { sub: TOP, sup: hd });
                            }
                            1 => {
                                let s = addc!(concept_of(bc[0]).unwrap().0);
                                let hd = addc!(hd_name);
                                nf1.push(Nf1 { sub: s, sup: hd });
                            }
                            2 => {
                                let s1 = addc!(concept_of(bc[0]).unwrap().0);
                                let s2 = addc!(concept_of(bc[1]).unwrap().0);
                                let hd = addc!(hd_name);
                                nf2.push(Nf2 {
                                    sub1: s1,
                                    sub2: s2,
                                    sup: hd,
                                });
                            }
                            _ => {
                                // n-ary conjunction (k>2): binary-decompose with
                                // deterministic fresh aux concepts (so identical
                                // conjunctions share them).
                                let mut names: Vec<String> = bc
                                    .iter()
                                    .map(|a| concept_of(a).unwrap().0.to_string())
                                    .collect();
                                names.sort();
                                let mut acc = names[0].clone();
                                for j in 1..names.len() - 1 {
                                    let aux = conjunction_aux_name(&names[..=j]);
                                    let s1 = addc!(&acc);
                                    let s2 = addc!(&names[j]);
                                    let sup = addc!(&aux);
                                    let prefix_ids = names[..=j]
                                        .iter()
                                        .map(|name| addc!(name))
                                        .collect::<Vec<_>>();
                                    conjunction_origins.insert(sup, prefix_ids);
                                    nf2.push(Nf2 {
                                        sub1: s1,
                                        sub2: s2,
                                        sup,
                                    });
                                    acc = aux;
                                }
                                let s1 = addc!(&acc);
                                let s2 = addc!(&names[names.len() - 1]);
                                let hd = addc!(hd_name);
                                nf2.push(Nf2 {
                                    sub1: s1,
                                    sub2: s2,
                                    sup: hd,
                                });
                            }
                        }
                        continue;
                    }
                    // NF4:  R(x,y) ∧ A(y) ⊑ B(x). The head must sit on the
                    // role SOURCE and the source/target must be distinct:
                    // `R(x,y) ∧ A(y) → B(y)` is `A ⊓ ∃R⁻.⊤ ⊑ B` and
                    // `R(x,x) ∧ A(x) → B(x)` is a self-restriction — reading
                    // either as `∃R.A ⊑ B` is UNSOUND. Mismatches fall to
                    // `residual` (cert-off: defer). The frontend's NF4 shape
                    // always has the head on the central source variable.
                    //
                    // With NO body concept the filler is ⊤: `R(x,y) → B(x)` is
                    // `∃R.⊤ ⊑ B`, the clause form of ObjectPropertyDomain.
                    // `init_state` seeds ⊤ into every satisfiable node's label,
                    // so the same NF4 propagation decides it exactly — no new
                    // rule, and the axiom is inside EL++. The same shape with
                    // the head on the role TARGET is `∃R⁻.⊤ ⊑ B`, which the
                    // wiring check below still sends to `residual`.
                    if br.len() == 1 && bc.len() <= 1 {
                        if let JAtom::Role {
                            role,
                            source,
                            target,
                        } = br[0]
                        {
                            if let (Tk::Var(sv), Tk::Var(ty)) = (tk(source), tk(target)) {
                                let filler_on_target = match bc.first() {
                                    None => true,
                                    Some(a) => {
                                        matches!(tk(concept_of(a).unwrap().1), Tk::Var(cv) if cv == ty)
                                    }
                                };
                                if filler_on_target && hv == sv && sv != ty {
                                    let r = addr!(role);
                                    let f = match bc.first() {
                                        None => {
                                            concept_names.insert(TOP);
                                            TOP
                                        }
                                        Some(a) => addc!(concept_of(a).unwrap().0),
                                    };
                                    let hd = addc!(hd_name);
                                    nf4.push(Nf4 {
                                        role: r,
                                        filler: f,
                                        sup: hd,
                                    });
                                    continue;
                                }
                            }
                        }
                    }
                    residual.push(c.clone());
                    continue;
                }
                Tk::Fun(fname, argument) => {
                    // existential filler: A(x) -> B(f(x))
                    if bc.len() == 1
                        && br.is_empty()
                        && matches!(tk(concept_of(bc[0]).unwrap().1), Tk::Var(body) if body == argument)
                    {
                        let sub = addc!(concept_of(bc[0]).unwrap().0);
                        let fnid = it.intern(fname);
                        let hd = addc!(hd_name);
                        pending_ex.entry((sub, fnid)).or_insert((None, None)).1 = Some(hd);
                        continue;
                    }
                    residual.push(c.clone());
                    continue;
                }
                Tk::Other => {
                    residual.push(c.clone());
                    continue;
                }
            }
        }

        // ---- role head ----
        if !hr.is_empty() {
            if let JAtom::Role {
                role,
                source,
                target,
            } = hr[0]
            {
                let st = tk(target);
                let sxs = tk(source);
                // reflexive role: `[] -> R(x,x)` (empty body, R relating one
                // variable to itself). The frontend emits this for
                // ReflexiveObjectProperty. Handled natively by seeding self-edges,
                // so it stays out of the residual. (IrreflexiveObjectProperty is
                // `R(x,x) -> ⊥`: non-empty body, empty head -- it never reaches
                // here and still goes to the residual certificate.)
                if b.is_empty() && h.len() == 1 {
                    if let (Tk::Var(sv), Tk::Var(tv)) = (&sxs, &st) {
                        if sv == tv {
                            let r = addr!(role);
                            reflexive_roles.insert(r);
                            continue;
                        }
                    }
                }
                // existential role: A(x) -> R(x, f(x))
                if let Tk::Fun(fname, argument) = st {
                    if matches!(sxs, Tk::Var(source) if source == argument)
                        && bc.len() == 1
                        && br.is_empty()
                        && matches!(tk(concept_of(bc[0]).unwrap().1), Tk::Var(body) if body == argument)
                    {
                        let sub = addc!(concept_of(bc[0]).unwrap().0);
                        let fnid = it.intern(fname);
                        let r = addr!(role);
                        pending_ex.entry((sub, fnid)).or_insert((None, None)).0 = Some(r);
                        continue;
                    }
                }
                // role inclusion: R(x,y) -> S(x,y). The head wiring must match
                // the body EXACTLY: a swapped head `R(x,y) -> S(y,x)` is an
                // inverse-role bridge (emitted by the frontend for
                // InverseObjectProperties / ObjectInverseOf), which EL cannot
                // express -- reading it as a forward inclusion would be unsound.
                if matches!(st, Tk::Var(_)) && br.len() == 1 && bc.is_empty() {
                    if let JAtom::Role {
                        role: br0,
                        source: bs,
                        target: bt,
                    } = br[0]
                    {
                        let fwd = match (vname(&tk(bs)), vname(&tk(bt)), vname(&sxs), vname(&st)) {
                            (Some(a), Some(b), Some(c), Some(d)) => a != b && a == c && b == d,
                            _ => false,
                        };
                        if !fwd {
                            residual.push(c.clone());
                            continue;
                        }
                        let sub = addr!(br0);
                        let sup = addr!(role);
                        nf6.push(Nf6 { sub, sup });
                        continue;
                    }
                }
                // role chain: R(x,y) ∧ S(y,z) -> T(x,z), with the chain wiring
                // checked explicitly (either body order). Anything else
                // (swapped orientation, fan-out) is not EL.
                if matches!(st, Tk::Var(_)) && br.len() == 2 && bc.is_empty() {
                    if let (
                        JAtom::Role {
                            role: ra,
                            source: as_,
                            target: at,
                        },
                        JAtom::Role {
                            role: rb,
                            source: bs,
                            target: bt,
                        },
                    ) = (br[0], br[1])
                    {
                        let (hs, ht) = match (vname(&sxs), vname(&st)) {
                            (Some(a), Some(b)) => (a, b),
                            _ => {
                                residual.push(c.clone());
                                continue;
                            }
                        };
                        let w = (
                            vname(&tk(as_)),
                            vname(&tk(at)),
                            vname(&tk(bs)),
                            vname(&tk(bt)),
                        );
                        let ordered = if let (Some(a0), Some(a1), Some(b0), Some(b1)) = w {
                            if a0 != a1 && a1 != b1 && a0 != b1 && a1 == b0 && hs == a0 && ht == b1
                            {
                                Some((ra, rb)) // R=br0, S=br1
                            } else if b0 != b1
                                && b1 != a1
                                && b0 != a1
                                && b1 == a0
                                && hs == b0
                                && ht == a1
                            {
                                Some((rb, ra)) // R=br1, S=br0
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        let (first, second) = match ordered {
                            Some(p) => p,
                            None => {
                                residual.push(c.clone());
                                continue;
                            }
                        };
                        let r1 = addr!(first);
                        let r2 = addr!(second);
                        let sup = addr!(role);
                        nf7.push(Nf7 { r1, r2, sup });
                        continue;
                    }
                }
            }
            residual.push(c.clone());
            continue;
        }
        residual.push(c.clone());
    }

    // assemble NF3 (A ⊑ ∃R.B) from its two half-clauses; record each skolem
    // function's filler concept for the residual certificate. The certificate
    // later gives every distinct function its own EL-closed witness node. A skolem reused
    // with conflicting fillers (never emitted by the frontend) is dropped
    // from the map, so residuals mentioning it bail conservatively.
    let mut skolem_target: HashMap<u32, (u32, u32, u32)> = HashMap::default();
    let mut skolem_ambiguous: HashSet<u32> = HashSet::default();
    for ((sub, fnid), (role, filler)) in pending_ex.into_iter() {
        match role {
            Some(r) => {
                let f = filler.unwrap_or(TOP);
                role_names.insert(r);
                concept_names.insert(sub);
                concept_names.insert(f);
                nf3.push(Nf3 {
                    sub,
                    role: r,
                    filler: f,
                });
                let target = (sub, r, f);
                match skolem_target.entry(fnid) {
                    std::collections::hash_map::Entry::Occupied(e) if *e.get() != target => {
                        skolem_ambiguous.insert(fnid);
                    }
                    std::collections::hash_map::Entry::Occupied(_) => {}
                    std::collections::hash_map::Entry::Vacant(v) => {
                        v.insert(target);
                    }
                }
            }
            None => return None, // filler with no role edge: shape we don't model
        }
    }
    for fnid in skolem_ambiguous {
        skolem_target.remove(&fnid);
    }

    Some((
        Nfs {
            nf1,
            nf2,
            nf3,
            nf4,
            nf5,
            nf6,
            nf7,
            reflexive_roles,
            concept_names,
            role_names,
            conjunction_origins,
        },
        residual,
        skolem_target,
    ))
}

// ---------------------------------------------------------------------------
// Saturation
// ---------------------------------------------------------------------------

/// Worklist item, mirroring the Python `("sub", ...)` / `("edge", ...)` tuples.
enum Item {
    Sub(u32, u32),
    Edge(u32, u32, u32),
    /// This edge frontier did not have enough NF4 join density to amortize a
    /// parallel batch. Process it with the ordinary edge-side NF4 rule without
    /// reconsidering the same frontier on every pop.
    EdgeSerial(u32, u32, u32),
    /// The edge-side NF4 join was already discharged by a frontier batch. The
    /// remaining edge rules still run in the original queue order.
    EdgeAfterNf4(u32, u32, u32),
}

/// Read-only indexes over the normal forms; built once, never mutated during the
/// loop, so the hot path can iterate their slices directly (no per-item clone).
struct Idx {
    nf1_by_sub: HashMap<u32, Vec<u32>>,        // sub -> [sup]
    nf2_by_sub: HashMap<u32, Vec<(u32, u32)>>, // key -> [(other, sup)]
    nf3_by_sub: HashMap<u32, Vec<(u32, u32)>>, // sub -> [(role, filler)]
    // NF4 (∃R.D⊑E) indexed by FILLER only: `filler D -> [(role R, sup E)]`. Both
    // the propagation-registration (Sub rule) and the join (Edge rule, via the
    // `prop` store) need only this view; the old `(role,filler)->[sup]` index is
    // gone with the per-edge label rescan it served.
    nf4_by_filler: HashMap<u32, Vec<(u32, u32)>>, // filler -> [(role, sup)]
    nf5_subs: HashSet<u32>,
    nf7_by_pair: HashMap<(u32, u32), Vec<u32>>, // (r1,r2) -> [sup]
    role_sub: Vec<HashSet<u32>>,                // role -> {super roles} (computed once)
    // Reflexive roles closed up the hierarchy: every super-role of a declared
    // reflexive role is also reflexive (R(x,x) ∧ R⊑S ⟹ S(x,x)).
    reflexive_closed: HashSet<u32>,
}

impl Idx {
    /// Super-roles of `r` (always includes `r`, since every role in the signature
    /// is pre-seeded with itself and every edge role lies in that signature).
    fn role_supers(&self, r: u32) -> &HashSet<u32> {
        &self.role_sub[r as usize]
    }
}

/// Mutable saturation state. Kept separate from `Idx` so a rule can iterate an
/// index immutably while pushing conclusions here mutably.
struct State {
    sub_super: Vec<HashSet<u32>>,
    edges: Vec<HashSet<(u32, u32)>>,
    // Backward links indexed by EXACT role: `in_by_role[(d, r)]` lists the
    // parents of `d` along `r`, in edge-creation order. A `Vec`, not a
    // `HashSet`: duplicates are already excluded because a parent is appended
    // only inside the `edges[parent].insert(...)` success branch of `add_edge`,
    // which fires at most once per distinct edge.
    //
    // The Sub-NF4 rule wants exactly one role at a time (the role of the axiom
    // `∃r.d ⊑ e` it is firing), so a flat `target -> [(parent, role)]` list made
    // it scan every predecessor and reject the ones whose role does not match.
    // Keying by the pair turns that scan into one lookup per axiom role. The map
    // stays small because backward links concentrate (1194's saturated structure
    // holds 43.9M links over ~203k distinct `(node, role)` keys), and the flat
    // form's `(u32, u32)` pairs become bare `u32` parents.
    in_by_role: HashMap<(u32, u32), Vec<u32>>,
    // The roles a node actually has backward links along (first-arrival order),
    // so the rules that need EVERY predecessor (⊥ back-propagation, role
    // composition, repair merges) can still enumerate them without scanning the
    // role signature. Append-only alongside `in_by_role`; a merge clears both
    // for the merged-away node.
    in_roles: Vec<Vec<u32>>,
    // ELK-style backward-link PROPAGATION store. `prop[(d, r)]` holds the NF4
    // conclusions `E` such that some filler `X ∈ label[d]` has an axiom
    // `∃r.X ⊑ E` with `r` the EXACT edge role. Role-subsumption is handled by the
    // edge-lift (every super-role edge is materialised as its own worklist item),
    // so an exact-role key suffices. An R-edge `(c,r,d)` then fires `prop[(d,r)]`
    // into `c` with a single hashmap lookup, replacing the per-edge rescan of the
    // whole filler label crossed with the role closure (`role_supers(r) ×
    // nf4_label[d]`). This is the ELK join: each (backward link, propagation)
    // pair fires exactly once -- whichever of the two is created second triggers
    // it. Keyed globally (one map, sparse) rather than a Vec-per-context so a
    // 400k-node giant pays only for the contexts that actually carry fillers.
    prop: HashMap<(u32, u32), Vec<u32>>,
    worklist: VecDeque<Item>,
    // ----- certificate-repair bookkeeping (inert during base saturation) -----
    // Journal of the `sub_super` entries added since it was last drained, so the
    // certificate's enumeration index can be refreshed from the delta instead of
    // rescanning every label. `None` (the base-saturation setting) records
    // nothing: the journal is switched on only for the duration of a repair pass,
    // where the per-round delta is four orders of magnitude smaller than the
    // saturated state. Capped at [`SUB_JOURNAL_CAP`] so a runaway round cannot
    // turn the journal into a second copy of the label relation; a full journal
    // reads back as "no delta", i.e. one full rescan.
    sub_journal: Option<Vec<(u32, u32)>>,
    // Bumped on every structural change to `edges` (a successful insert, the
    // explicit removals in `merge_nodes`, and a witness-mirror re-sync that
    // actually changes the target's iteration sequence). Equal epochs therefore
    // certify that every `edges[c]` iterates exactly as it did before, which is
    // what the certificate's role-keyed edge index is built from.
    edge_epoch: u64,
}

// ---------------------------------------------------------------------------
// Lean ELC certificate wire model
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanElStep {
    Refl { a: u32 },
    Top { a: u32 },
    Nf1 { a: u32, sub: u32, sup: u32 },
    Nf2 { a: u32, left: u32, right: u32, sup: u32 },
    Nf5 { a: u32, sub: u32 },
    Nf4 { a: u32, target: u32, filler: u32, sup: u32, role: u32 },
    BottomEdge { a: u32, target: u32, role: u32 },
    Nf3 { a: u32, sub: u32, filler: u32, role: u32 },
    Nf6 { a: u32, target: u32, sub: u32, sup: u32 },
    Nf7 {
        a: u32,
        middle: u32,
        target: u32,
        first: u32,
        second: u32,
        sup: u32,
    },
    Reflexive { a: u32, role: u32 },
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanElClause {
    Nf1 { sub: u32, sup: u32 },
    Nf2 { left: u32, right: u32, sup: u32 },
    Nf3 { sub: u32, role: u32, filler: u32 },
    Nf4 { role: u32, filler: u32, sup: u32 },
    Nf5 { sub: u32 },
    Nf6 { sub: u32, sup: u32 },
    Nf7 { first: u32, second: u32, sup: u32 },
    Reflexive { role: u32 },
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanRawTerm {
    Var { name: u32 },
    Fun { function: u32, argument: Box<LeanRawTerm> },
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanRawAtom {
    Concept { concept: u32, term: LeanRawTerm },
    Role { role: u32, source: LeanRawTerm, target: LeanRawTerm },
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanResidualAtom {
    Concept { concept: u32, term: LeanRawTerm },
    Role { role: u32, source: LeanRawTerm, target: LeanRawTerm },
    Eq { left: LeanRawTerm, right: LeanRawTerm },
}

#[derive(Clone, Debug, serde::Serialize)]
struct LeanResidualClause {
    body: Vec<LeanResidualAtom>,
    head: Vec<LeanResidualAtom>,
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanResidualOrigin {
    Source { name: usize },
    Function { function: u32, witness: u32 },
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanCompiledResidualAtom {
    Concept { concept: u32, slot: usize },
    Role { role: u32, source: usize, target: usize },
    Eq { left: usize, right: usize },
}

#[derive(Clone, Debug, serde::Serialize)]
struct LeanResidualCompilation {
    variable_count: usize,
    origins: Vec<LeanResidualOrigin>,
    raw: LeanResidualClause,
    body: Vec<LeanCompiledResidualAtom>,
    head: Vec<LeanCompiledResidualAtom>,
    pins: Vec<(usize, u32)>,
}

#[derive(Clone, Debug, serde::Serialize)]
struct LeanRawClause {
    body: Vec<LeanRawAtom>,
    head: Vec<LeanRawAtom>,
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanConceptOrigin {
    Source,
    Conjunction { prefix_ids: Vec<u32> },
}

#[derive(Clone, Debug, serde::Serialize)]
struct LeanElCertificate {
    version: u32,
    symbol_count: u32,
    top: u32,
    bottom: u32,
    variable_count: u32,
    raw_ontology: Vec<LeanRawClause>,
    residual_compilations: Vec<LeanResidualCompilation>,
    concept_origins: Vec<LeanConceptOrigin>,
    ontology: Vec<LeanElClause>,
    /// Reverse dependency order, as required by Lean's `checkTrace`.
    trace: Vec<LeanElStep>,
    active_concepts: Vec<u32>,
    rust_subsumptions: Vec<LeanElSubFact>,
    rust_edges: Vec<LeanElEdgeFact>,
    /// The exact ID-level relation materialised by the public output loop.
    /// Names are a presentation concern; Lean checks the semantic filtering.
    public_subsumptions: Vec<LeanElSubFact>,
    symbols: Vec<String>,
    public_named_subsumptions: Vec<LeanElNamedSubFact>,
    public_inconsistent: bool,
}

#[derive(Clone, Debug, serde::Serialize)]
struct LeanElSubFact {
    sub: u32,
    sup: u32,
}

#[derive(Clone, Debug, serde::Serialize)]
struct LeanElEdgeFact {
    source: u32,
    role: u32,
    target: u32,
}

#[derive(Clone, Debug, serde::Serialize)]
struct LeanElNamedSubFact {
    sub: String,
    sup: String,
}

impl LeanElCertificate {
    /// Materialize exactly the named result checked by Lean. Checker-enabled
    /// publication returns this value directly, so no unchecked conversion can
    /// intervene between acceptance and the worker's public result.
    fn verified_result(&self) -> ElResult {
        let mut subsumptions = std::collections::BTreeMap::<String, Vec<String>>::new();
        for fact in &self.public_named_subsumptions {
            subsumptions
                .entry(fact.sub.clone())
                .or_default()
                .push(fact.sup.clone());
        }
        ElResult {
            unresolved: Vec::new(),
            subsumptions,
            inconsistent: self.public_inconsistent,
        }
    }
}

/// Reconstruct the unoptimised formal NF1–NF7 closure and record one proof for
/// every fact. This path is intentionally separate from the indexed production
/// worklist: Lean checks the resulting derivations, and equality against `State`
/// detects either implementation disagreeing with the formal closure.
fn build_lean_el_certificate(
    nfs: &Nfs,
    st: &State,
    interner: &Interner,
    raw_clauses: &[JClause],
    residual_compilations: Vec<LeanResidualCompilation>,
) -> Result<LeanElCertificate, String> {
    use std::collections::BTreeSet;

    let symbol_count = interner.len();

    let mut subs: BTreeSet<(u32, u32)> = BTreeSet::new();
    let mut edges: BTreeSet<(u32, u32, u32)> = BTreeSet::new();
    let mut steps = Vec::new();
    let mut add_sub = |fact: (u32, u32), step: LeanElStep| {
        if subs.insert(fact) {
            steps.push(step);
            true
        } else {
            false
        }
    };
    for a in 0..symbol_count as u32 {
        add_sub((a, a), LeanElStep::Refl { a });
        add_sub((a, TOP), LeanElStep::Top { a });
    }
    drop(add_sub);

    let mut changed = true;
    while changed {
        changed = false;
        let sub_snapshot: Vec<_> = subs.iter().copied().collect();
        let edge_snapshot: Vec<_> = edges.iter().copied().collect();

        for &(a, known) in &sub_snapshot {
            for nf in &nfs.nf1 {
                if known == nf.sub && subs.insert((a, nf.sup)) {
                    steps.push(LeanElStep::Nf1 { a, sub: nf.sub, sup: nf.sup });
                    changed = true;
                }
            }
            for nf in &nfs.nf2 {
                if known == nf.sub1 && subs.contains(&(a, nf.sub2))
                    || known == nf.sub2 && subs.contains(&(a, nf.sub1))
                {
                    if subs.insert((a, nf.sup)) {
                        steps.push(LeanElStep::Nf2 {
                            a,
                            left: nf.sub1,
                            right: nf.sub2,
                            sup: nf.sup,
                        });
                        changed = true;
                    }
                }
            }
            if nfs.nf5.contains(&known) && subs.insert((a, BOTTOM)) {
                steps.push(LeanElStep::Nf5 { a, sub: known });
                changed = true;
            }
            for nf in &nfs.nf3 {
                if known == nf.sub && edges.insert((a, nf.role, nf.filler)) {
                    steps.push(LeanElStep::Nf3 {
                        a,
                        sub: nf.sub,
                        filler: nf.filler,
                        role: nf.role,
                    });
                    changed = true;
                }
            }
        }

        for &(a, role, target) in &edge_snapshot {
            if subs.contains(&(target, BOTTOM)) && subs.insert((a, BOTTOM)) {
                steps.push(LeanElStep::BottomEdge { a, target, role });
                changed = true;
            }
            for nf in &nfs.nf4 {
                if role == nf.role && subs.contains(&(target, nf.filler))
                    && subs.insert((a, nf.sup))
                {
                    steps.push(LeanElStep::Nf4 {
                        a,
                        target,
                        filler: nf.filler,
                        sup: nf.sup,
                        role,
                    });
                    changed = true;
                }
            }
            for nf in &nfs.nf6 {
                if role == nf.sub && edges.insert((a, nf.sup, target)) {
                    steps.push(LeanElStep::Nf6 {
                        a,
                        target,
                        sub: nf.sub,
                        sup: nf.sup,
                    });
                    changed = true;
                }
            }
            for &(middle, second, end) in &edge_snapshot {
                if middle != target {
                    continue;
                }
                for nf in &nfs.nf7 {
                    if role == nf.r1 && second == nf.r2
                        && edges.insert((a, nf.sup, end))
                    {
                        steps.push(LeanElStep::Nf7 {
                            a,
                            middle,
                            target: end,
                            first: nf.r1,
                            second: nf.r2,
                            sup: nf.sup,
                        });
                        changed = true;
                    }
                }
            }
        }

        for a in 0..symbol_count as u32 {
            for &role in &nfs.reflexive_roles {
                if edges.insert((a, role, a)) {
                    steps.push(LeanElStep::Reflexive { a, role });
                    changed = true;
                }
            }
        }
    }

    // Every production fact must have a formal derivation. For active concept
    // contexts other than bottom, production must also contain every formal
    // fact. Role-only ids and bottom receive formal initialization facts but are
    // intentionally not allocated as Rust completion contexts.
    for (a, rust_supers) in st.sub_super.iter().enumerate() {
        for &sup in rust_supers {
            if !subs.contains(&(a as u32, sup)) {
                return Err(format!("Rust-only subsumption ({a},{sup})"));
            }
        }
    }
    for (a, rust_edges) in st.edges.iter().enumerate() {
        for &(role, target) in rust_edges {
            if !edges.contains(&(a as u32, role, target)) {
                return Err(format!("Rust-only edge ({a},{role},{target})"));
            }
        }
    }
    for &a in &nfs.concept_names {
        if a == BOTTOM {
            continue;
        }
        let formal_subs: BTreeSet<u32> = subs
            .range((a, 0)..=(a, u32::MAX))
            .map(|&(_, sup)| sup)
            .collect();
        let rust_subs: BTreeSet<u32> = st.sub_super[a as usize].iter().copied().collect();
        if formal_subs != rust_subs {
            return Err(format!("subsumption closure mismatch at context {a}"));
        }
        let formal_edges: BTreeSet<(u32, u32)> = edges
            .range((a, 0, 0)..=(a, u32::MAX, u32::MAX))
            .map(|&(_, role, target)| (role, target))
            .collect();
        let rust_edges: BTreeSet<(u32, u32)> = st.edges[a as usize].iter().copied().collect();
        if formal_edges != rust_edges {
            return Err(format!("edge closure mismatch at context {a}"));
        }
    }

    let mut ontology = Vec::new();
    ontology.extend(nfs.nf1.iter().map(|x| LeanElClause::Nf1 { sub: x.sub, sup: x.sup }));
    ontology.extend(nfs.nf2.iter().map(|x| LeanElClause::Nf2 {
        left: x.sub1, right: x.sub2, sup: x.sup,
    }));
    ontology.extend(nfs.nf3.iter().map(|x| LeanElClause::Nf3 {
        sub: x.sub, role: x.role, filler: x.filler,
    }));
    ontology.extend(nfs.nf4.iter().map(|x| LeanElClause::Nf4 {
        role: x.role, filler: x.filler, sup: x.sup,
    }));
    ontology.extend(nfs.nf5.iter().map(|&sub| LeanElClause::Nf5 { sub }));
    ontology.extend(nfs.nf6.iter().map(|x| LeanElClause::Nf6 { sub: x.sub, sup: x.sup }));
    ontology.extend(nfs.nf7.iter().map(|x| LeanElClause::Nf7 {
        first: x.r1, second: x.r2, sup: x.sup,
    }));
    ontology.extend(nfs.reflexive_roles.iter().map(|&role| LeanElClause::Reflexive { role }));
    steps.reverse();
    let mut active_concepts: Vec<u32> = nfs
        .concept_names
        .iter()
        .copied()
        .filter(|&a| a != BOTTOM)
        .collect();
    // TOP is queried for the ontology inconsistency result even when it does
    // not occur in an input normal form, so it is always an active context at
    // the certificate boundary.
    active_concepts.push(TOP);
    active_concepts.sort_unstable();
    active_concepts.dedup();
    let mut rust_subsumptions = Vec::new();
    let mut rust_edges = Vec::new();
    for &sub in &active_concepts {
        rust_subsumptions.extend(st.sub_super[sub as usize].iter().map(|&sup| {
            LeanElSubFact { sub, sup }
        }));
        rust_edges.extend(st.edges[sub as usize].iter().map(|&(role, target)| {
            LeanElEdgeFact { source: sub, role, target }
        }));
    }
    rust_subsumptions.sort_unstable_by_key(|fact| (fact.sub, fact.sup));
    rust_edges.sort_unstable_by_key(|fact| (fact.source, fact.role, fact.target));
    let mut public_subsumptions: Vec<_> = rust_subsumptions
        .iter()
        .filter(|fact| {
            fact.sub != TOP
                && fact.sub != BOTTOM
                && fact.sup != fact.sub
                && fact.sup != TOP
        })
        .cloned()
        .collect();
    public_subsumptions.sort_unstable_by_key(|fact| (fact.sub, fact.sup));
    let public_named_subsumptions = public_subsumptions
        .iter()
        .map(|fact| LeanElNamedSubFact {
            sub: interner.name(fact.sub).to_string(),
            sup: if fact.sup == BOTTOM {
                "owl:Nothing".to_string()
            } else {
                interner.name(fact.sup).to_string()
            },
        })
        .collect();
    let mut variables: HashMap<String, u32> = HashMap::default();
    fn raw_term(
        term: &JTerm,
        interner: &Interner,
        variables: &mut HashMap<String, u32>,
    ) -> Result<LeanRawTerm, String> {
        match term {
            JTerm::Var { name } => {
                let next = variables.len() as u32;
                let id = *variables.entry(name.clone()).or_insert(next);
                Ok(LeanRawTerm::Var { name: id })
            }
            JTerm::Fun { function, arg } => Ok(LeanRawTerm::Fun {
                function: interner.id(function).ok_or_else(|| format!("uninterned function {function}"))?,
                argument: Box::new(raw_term(arg, interner, variables)?),
            }),
            JTerm::Ind { .. } | JTerm::Aux { .. } => Err("non-EL raw term in Lean certificate".into()),
        }
    }
    fn raw_atom(
        atom: &JAtom,
        interner: &Interner,
        variables: &mut HashMap<String, u32>,
    ) -> Result<LeanRawAtom, String> {
        match atom {
            JAtom::Concept { concept, term } => Ok(LeanRawAtom::Concept {
                concept: interner.id(concept).ok_or_else(|| format!("uninterned concept {concept}"))?,
                term: raw_term(term, interner, variables)?,
            }),
            JAtom::Role { role, source, target } => Ok(LeanRawAtom::Role {
                role: interner.id(role).ok_or_else(|| format!("uninterned role {role}"))?,
                source: raw_term(source, interner, variables)?,
                target: raw_term(target, interner, variables)?,
            }),
            JAtom::Eq { .. } => Err("equality atom in Lean ELC certificate".into()),
        }
    }
    let mut raw_ontology = Vec::with_capacity(raw_clauses.len());
    for clause in raw_clauses {
        raw_ontology.push(LeanRawClause {
            body: clause.body.iter().map(|a| raw_atom(a, interner, &mut variables)).collect::<Result<_, _>>()?,
            head: clause.head.iter().map(|a| raw_atom(a, interner, &mut variables)).collect::<Result<_, _>>()?,
        });
    }
    let mut concept_origins = vec![LeanConceptOrigin::Source; symbol_count];
    for (&id, prefix_ids) in &nfs.conjunction_origins {
        let slot = concept_origins.get_mut(id as usize).ok_or_else(|| format!("origin id {id} out of bounds"))?;
        *slot = LeanConceptOrigin::Conjunction { prefix_ids: prefix_ids.clone() };
    }
    Ok(LeanElCertificate {
        version: 4,
        symbol_count: symbol_count as u32,
        top: TOP,
        bottom: BOTTOM,
        variable_count: variables.len() as u32,
        raw_ontology,
        residual_compilations,
        concept_origins,
        ontology,
        trace: steps,
        active_concepts,
        rust_subsumptions,
        rust_edges,
        public_subsumptions,
        symbols: interner.names.clone(),
        public_named_subsumptions,
        public_inconsistent: st.sub_super[TOP as usize].contains(&BOTTOM),
    })
}

/// Ceiling on `State::sub_journal`. Above it the delta is no cheaper to merge
/// than the labels are to rescan, so the journal stops recording and the
/// certificate index falls back to a full rebuild.
const SUB_JOURNAL_CAP: usize = 8_000_000;

impl State {
    /// Body of `add_sub` over the fields it actually touches, so a rule can add
    /// conclusions while another field of the state (e.g. `prop`) is still
    /// immutably borrowed.
    #[inline]
    fn add_sub_parts(
        sub_super: &mut [HashSet<u32>],
        worklist: &mut VecDeque<Item>,
        journal: &mut Option<Vec<(u32, u32)>>,
        c: u32,
        d: u32,
    ) {
        if sub_super[c as usize].insert(d) {
            worklist.push_back(Item::Sub(c, d));
            if let Some(j) = journal {
                // A round that adds more than this is cheaper to re-index by a
                // full rescan than by a merge, so the journal stops at the cap
                // and the reader treats a full journal as "rebuild".
                if j.len() < SUB_JOURNAL_CAP {
                    j.push((c, d));
                }
            }
        }
    }

    #[inline]
    fn add_sub(&mut self, c: u32, d: u32) {
        Self::add_sub_parts(
            &mut self.sub_super,
            &mut self.worklist,
            &mut self.sub_journal,
            c,
            d,
        );
    }

    /// Edge-side NF4 join, in place: fire the propagations `prop[(d,r)]` into
    /// `c` while iterating the stored slice directly. Safe without a snapshot
    /// copy because a new subsumption only inserts into `sub_super` and pushes
    /// a Sub item onto the worklist; `prop` is extended only when that Sub item
    /// is later PROCESSED (the registration in the Sub arm of `run`), so
    /// `prop[(d,r)]` cannot grow or move during this loop -- including for a
    /// self-edge `c == d`. Conclusions are added in the same slice order as
    /// before, so the creation order of derived facts is unchanged. Returns the
    /// number of conclusions scanned (for KM_ELC_PROFILE).
    #[inline]
    fn fire_edge_nf4(&mut self, c: u32, r: u32, d: u32) -> u64 {
        let Some(es) = self.prop.get(&(d, r)) else {
            return 0;
        };
        for &sup in es {
            Self::add_sub_parts(
                &mut self.sub_super,
                &mut self.worklist,
                &mut self.sub_journal,
                c,
                sup,
            );
        }
        es.len() as u64
    }

    #[inline]
    fn add_edge(&mut self, c: u32, r: u32, d: u32) {
        if self.edges[c as usize].insert((r, d)) {
            self.edge_epoch += 1;
            let parents = self.in_by_role.entry((d, r)).or_default();
            if parents.is_empty() {
                self.in_roles[d as usize].push(r);
            }
            parents.push(c);
            self.worklist.push_back(Item::Edge(c, r, d));
        }
    }

    /// Deep copy for a certificate-repair pass. Only valid at fixpoint (empty
    /// worklist): the copy starts with nothing queued.
    fn fork(&self) -> State {
        debug_assert!(self.worklist.is_empty());
        State {
            sub_super: self.sub_super.clone(),
            edges: self.edges.clone(),
            in_by_role: self.in_by_role.clone(),
            in_roles: self.in_roles.clone(),
            prop: self.prop.clone(),
            worklist: VecDeque::new(),
            sub_journal: None,
            edge_epoch: self.edge_epoch,
        }
    }

    /// Start journalling `sub_super` additions, for the duration of one repair
    /// pass. Off everywhere else, including in the base saturation this forks.
    fn start_journal(&mut self) {
        self.sub_journal = Some(Vec::new());
    }

    /// Take the additions journalled since the last drain, leaving journalling
    /// on. `None` means "no usable delta" — journalling is off, or the round
    /// overran [`SUB_JOURNAL_CAP`] and the journal is no longer complete.
    fn drain_journal(&mut self) -> Option<Vec<(u32, u32)>> {
        self.sub_journal
            .replace(Vec::new())
            .filter(|j| j.len() < SUB_JOURNAL_CAP)
    }
}

/// Build the read-only rule indexes (including the role-hierarchy closure).
fn build_idx(nfs: &Nfs, n: usize) -> Idx {
    // ----- build indexes -----
    let mut nf1_by_sub: HashMap<u32, Vec<u32>> = HashMap::default();
    for a in &nfs.nf1 {
        nf1_by_sub.entry(a.sub).or_default().push(a.sup);
    }
    let mut nf2_by_sub: HashMap<u32, Vec<(u32, u32)>> = HashMap::default();
    for a in &nfs.nf2 {
        // indexed by both sides; store the *other* side + the conclusion
        nf2_by_sub.entry(a.sub1).or_default().push((a.sub2, a.sup));
        nf2_by_sub.entry(a.sub2).or_default().push((a.sub1, a.sup));
    }
    let mut nf3_by_sub: HashMap<u32, Vec<(u32, u32)>> = HashMap::default();
    for a in &nfs.nf3 {
        nf3_by_sub
            .entry(a.sub)
            .or_default()
            .push((a.role, a.filler));
    }
    // NF4 (∃R.D⊑E) indexed by filler D -> [(role R, sup E)]. The Sub rule reads
    // it to register propagations; the Edge rule consults the `prop` store the
    // Sub rule fills, so no `(role,filler)` index is needed.
    let mut nf4_by_filler: HashMap<u32, Vec<(u32, u32)>> = HashMap::default();
    for a in &nfs.nf4 {
        nf4_by_filler
            .entry(a.filler)
            .or_default()
            .push((a.role, a.sup));
    }
    // Keep each filler bucket ordered by role. The Sub-NF4 rule can then visit
    // only the exact-role range for a backward link instead of scanning and
    // rejecting every axiom attached to the filler. This changes index order,
    // not the set of axioms or conclusions.
    for axs in nf4_by_filler.values_mut() {
        axs.sort_unstable();
    }
    let nf5_subs: HashSet<u32> = nfs.nf5.iter().copied().collect();
    let mut nf7_by_pair: HashMap<(u32, u32), Vec<u32>> = HashMap::default();
    for a in &nfs.nf7 {
        nf7_by_pair.entry((a.r1, a.r2)).or_default().push(a.sup);
    }

    // ----- role hierarchy: reflexive-transitive closure of NF6 -----
    let mut role_sub: Vec<HashSet<u32>> = vec![HashSet::default(); n];
    for &r in &nfs.role_names {
        role_sub[r as usize].insert(r);
    }
    let mut nf6_by_sub: HashMap<u32, Vec<u32>> = HashMap::default();
    for a in &nfs.nf6 {
        nf6_by_sub.entry(a.sub).or_default().push(a.sup);
    }
    let roles: Vec<u32> = nfs.role_names.iter().copied().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &r in &roles {
            let sups: Vec<u32> = nf6_by_sub.get(&r).cloned().unwrap_or_default();
            for sup in sups {
                if role_sub[r as usize].insert(sup) {
                    changed = true;
                    let trans: Vec<u32> = role_sub[sup as usize].iter().copied().collect();
                    for s in trans {
                        if role_sub[r as usize].insert(s) {
                            changed = true;
                        }
                    }
                }
            }
        }
    }

    // Reflexive-role closure: a reflexive role's super-roles are reflexive too.
    let mut reflexive_closed: HashSet<u32> = HashSet::default();
    for &r in &nfs.reflexive_roles {
        for &sup in &role_sub[r as usize] {
            reflexive_closed.insert(sup);
        }
    }

    Idx {
        nf1_by_sub,
        nf2_by_sub,
        nf3_by_sub,
        nf4_by_filler,
        nf5_subs,
        nf7_by_pair,
        role_sub,
        reflexive_closed,
    }
}

/// Fresh state seeded with the Init rule R₀: C ⊑ C and C ⊑ ⊤ for every concept.
fn init_state(nfs: &Nfs, n: usize) -> State {
    let mut st = State {
        sub_super: vec![HashSet::default(); n],
        edges: vec![HashSet::default(); n],
        in_by_role: HashMap::default(),
        in_roles: vec![Vec::new(); n],
        prop: HashMap::default(),
        worklist: VecDeque::new(),
        sub_journal: None,
        edge_epoch: 0,
    };
    for &c in &nfs.concept_names {
        if c == BOTTOM {
            continue;
        }
        st.add_sub(c, c);
        st.add_sub(c, TOP);
    }
    st
}

/// Per-rule scan counters (KM_ELC_PROFILE). Plain u64s, single-threaded, so the
/// increments are negligible vs the work they measure.
#[derive(Default)]
struct Prof {
    sub_items: u64,
    edge_items: u64,
    nf1_scan: u64,
    nf2_scan: u64,
    nf3_scan: u64,
    nf4_sub_scan: u64,  // exact-role (backward link, axiom) pairs fired sub-side
    nf4_edge_scan: u64, // (super_role, d_super) lookups in the Edge-NF4 rule
    nf7_scan: u64,      // out-edges scanned in the NF7 rule
    botback: u64,
    nf4_batch_calls: u64,
    nf4_batch_edges: u64,
    nf4_batch_groups: u64,
    nf4_batch_missing: u64,
}

const PAR_NF4_MIN_EDGES: usize = 256;
const PAR_NF4_MAX_EDGES: usize = 65_536;

/// Discharge the edge-side NF4 join for one consecutive edge frontier.
///
/// Edges are grouped by parent because all conclusions of the join land in the
/// parent's label. Each group is independent and can therefore be computed in
/// parallel without synchronizing the authoritative state. A local set removes
/// the confluence duplicates produced when several targets carry the same
/// propagation. Conclusions are sorted before insertion, making the schedule
/// deterministic. Every emitted conclusion is exactly one that the ordinary
/// edge-side NF4 rule would attempt; delaying and deduplicating attempts does
/// not change the finite monotone closure.
fn fire_edge_nf4_batch(
    idx: &Idx,
    st: &mut State,
    prof: &mut Prof,
    parallel_nf4: bool,
) -> bool {
    if !parallel_nf4 || idx.nf4_by_filler.is_empty() {
        return false;
    }
    let edge_count = st
        .worklist
        .iter()
        .take(PAR_NF4_MAX_EDGES)
        .take_while(|item| matches!(item, Item::Edge(..)))
        .count();
    if edge_count < PAR_NF4_MIN_EDGES {
        return false;
    }

    let mut edges = Vec::with_capacity(edge_count);
    for _ in 0..edge_count {
        let Some(Item::Edge(c, r, d)) = st.worklist.pop_front() else {
            unreachable!("the measured consecutive edge frontier changed")
        };
        edges.push((c, r, d));
    }

    // A batch pays for grouping and local deduplication. Sparse propagation
    // frontiers are faster through the ordinary direct join. Measure the exact
    // immutable slices this frontier would scan, then mark a declined frontier
    // so it is not measured repeatedly as each edge is popped.
    let estimated_scan: usize = edges
        .iter()
        .map(|&(_, r, d)| st.prop.get(&(d, r)).map_or(0, Vec::len))
        .sum();
    if estimated_scan < edge_count.saturating_mul(128) {
        for (c, r, d) in edges.into_iter().rev() {
            st.worklist.push_front(Item::EdgeSerial(c, r, d));
        }
        return true;
    }

    let mut by_parent: HashMap<u32, Vec<(u32, u32)>> = HashMap::default();
    for &(c, r, d) in &edges {
        by_parent.entry(c).or_default().push((r, d));
    }
    if by_parent.len().saturating_mul(2) > edge_count {
        for (c, r, d) in edges.into_iter().rev() {
            st.worklist.push_front(Item::EdgeSerial(c, r, d));
        }
        return true;
    }
    prof.nf4_batch_calls += 1;
    prof.nf4_batch_edges += edges.len() as u64;
    prof.nf4_batch_groups += by_parent.len() as u64;
    let prop = &st.prop;
    let labels = &st.sub_super;
    let mut conclusions: Vec<(u32, Vec<u32>, u64)> = by_parent
        .into_par_iter()
        .map(|(c, parent_edges)| {
            let label = &labels[c as usize];
            let mut missing: HashSet<u32> = HashSet::default();
            let mut scanned = 0u64;
            for (r, d) in parent_edges {
                if let Some(sups) = prop.get(&(d, r)) {
                    scanned += sups.len() as u64;
                    for &sup in sups {
                        if !label.contains(&sup) {
                            missing.insert(sup);
                        }
                    }
                }
            }
            let mut missing: Vec<u32> = missing.into_iter().collect();
            missing.sort_unstable();
            (c, missing, scanned)
        })
        .collect();
    conclusions.sort_unstable_by_key(|(c, _, _)| *c);
    for (c, missing, scanned) in conclusions {
        prof.nf4_edge_scan += scanned;
        prof.nf4_batch_missing += missing.len() as u64;
        for sup in missing {
            st.add_sub(c, sup);
        }
    }

    // Preserve the original order for bottom propagation, role chains, and
    // hierarchy lifting. Only the already-completed NF4 join is skipped.
    for (c, r, d) in edges.into_iter().rev() {
        st.worklist.push_front(Item::EdgeAfterNf4(c, r, d));
    }
    true
}

/// Run the completion rules to fixpoint over whatever is on `st`'s worklist.
/// Re-entrant: the certificate repair re-enters with extra seeded facts and the
/// SAME `idx` (the rule set never changes), so a repaired structure is again
/// closed under every EL rule — i.e. it stays a model of the EL clause set.
fn run(idx: &Idx, st: &mut State, prof: &mut Prof) {
    // Empty fallback so an unindexed role still yields the empty super-set
    // without a per-lookup allocation (it never occurs for edge roles in
    // practice, but keeps the borrow simple).
    let empty: HashSet<u32> = HashSet::default();

    // ----- Main loop -----
    // `idx` is borrowed immutably throughout; `st` mutably. Because they are
    // distinct objects, a rule can scan an index slice while pushing into the
    // state. Snapshots (`.collect()`) are taken only when iterating one of the
    // state's *own* mutated collections (sub_super[d], edges[d], the backward
    // links of c).
    let parallel_nf4 = std::env::var_os("KM_ELC_PAR_NF4").is_some();
    while !st.worklist.is_empty() {
        if fire_edge_nf4_batch(idx, st, prof, parallel_nf4) {
            continue;
        }
        let item = st.worklist.pop_front().expect("checked non-empty");
        match item {
            Item::Sub(c, d) => {
                prof.sub_items += 1;
                // R⊑ : C ⊑ D, D ⊑ E ⟹ C ⊑ E  (NF1)
                if let Some(sups) = idx.nf1_by_sub.get(&d) {
                    prof.nf1_scan += sups.len() as u64;
                    for &sup in sups {
                        st.add_sub(c, sup);
                    }
                }
                // R⊓ : C ⊑ D, C ⊑ D', D ⊓ D' ⊑ E ⟹ C ⊑ E  (NF2)
                if let Some(cand) = idx.nf2_by_sub.get(&d) {
                    prof.nf2_scan += cand.len() as u64;
                    for &(other, sup) in cand {
                        if st.sub_super[c as usize].contains(&other) {
                            st.add_sub(c, sup);
                        }
                    }
                }
                // R⊥ : D ⊑ ⊥ axiomatically (NF5) ⟹ C ⊑ ⊥
                if idx.nf5_subs.contains(&d) {
                    st.add_sub(c, BOTTOM);
                }
                // R∃ : C ⊑ D, D ⊑ ∃R.E ⟹ edge (C,R,E)  (NF3)
                if let Some(edges) = idx.nf3_by_sub.get(&d) {
                    prof.nf3_scan += edges.len() as u64;
                    for &(role, filler) in edges {
                        st.add_edge(c, role, filler);
                    }
                }
                // R⊥-edge : C ⊑ ⊥ propagates backwards along edges into C. This
                // rule needs EVERY predecessor regardless of role, so it walks
                // the role-keyed index role by role via `in_roles[c]`.
                // `add_sub_parts` touches only `sub_super` and the worklist,
                // never the backward links, so both lists are iterated in place
                // with no clone.
                if d == BOTTOM {
                    let State {
                        sub_super,
                        in_by_role,
                        in_roles,
                        worklist,
                        sub_journal,
                        ..
                    } = &mut *st;
                    for &role in &in_roles[c as usize] {
                        if let Some(parents) = in_by_role.get(&(c, role)) {
                            prof.botback += parents.len() as u64;
                            for &parent in parents {
                                State::add_sub_parts(
                                    sub_super,
                                    worklist,
                                    sub_journal,
                                    parent,
                                    BOTTOM,
                                );
                            }
                        }
                    }
                }
                // R∃⁻ (NF4) + ELK propagation registration. `d` is a new subsumer
                // of `c`; if it is an NF4 filler, each axiom `∃R.d ⊑ E` is a new
                // propagation in context `c`: (a) record it in `prop[(c,R)]` so any
                // FUTURE edge into `c` with exact role R fires it (edge-side), and
                // (b) fire it now against the backward links already at `c` whose
                // EXACT role is R (super-role edges exist by the lift, so the
                // exact-role key suffices; no role-closure scan). The role-keyed
                // backward-link index turns (b) into one lookup per axiom role
                // group -- predecessors of `c` along roles no axiom mentions are
                // never touched, where the flat list visited every backward link
                // per Sub item. `add_sub_parts` never mutates `in_by_role`, so
                // the parent slices are iterated in place, self-edges included.
                if let Some(axs) = idx.nf4_by_filler.get(&d) {
                    for &(s, e) in axs {
                        // No dedup: each (c,s,e) propagation is pushed ~once in EL
                        // (measured bucket-duplication on the 8737 giant is <0.5%),
                        // so ELK's `propagatedSubsumers_` Set buys nothing here and
                        // a `contains` guard only adds cost. The residual `add_sub`
                        // re-fires are confluence (the same `c⊑E` reached via many
                        // edges), which ELK's join pays identically.
                        st.prop.entry((c, s)).or_default().push(e);
                    }
                    let State {
                        sub_super,
                        in_by_role,
                        worklist,
                        sub_journal,
                        ..
                    } = &mut *st;
                    // `axs` is role-sorted (build_idx), so each iteration handles
                    // one contiguous exact-role group [lo..hi).
                    let mut lo = 0;
                    while lo < axs.len() {
                        let role = axs[lo].0;
                        let hi = axs.partition_point(|&(s, _)| s <= role);
                        if let Some(parents) = in_by_role.get(&(c, role)) {
                            prof.nf4_sub_scan += (parents.len() * (hi - lo)) as u64;
                            for &parent in parents {
                                for &(_, e) in &axs[lo..hi] {
                                    State::add_sub_parts(
                                        sub_super,
                                        worklist,
                                        sub_journal,
                                        parent,
                                        e,
                                    );
                                }
                            }
                        }
                        lo = hi;
                    }
                }
            }
            Item::Edge(c, r, d)
            | Item::EdgeSerial(c, r, d)
            | Item::EdgeAfterNf4(c, r, d) => {
                let nf4_already_fired = matches!(item, Item::EdgeAfterNf4(..));
                prof.edge_items += 1;
                // R∃⁻ (NF4), ELK backward-link join: this new edge `(c,r,d)` is a
                // backward link arriving at context `d` with EXACT role `r`. Fire
                // it against the propagations already stored at `d` for that exact
                // role -- a single hashmap lookup yielding the conclusions `E`
                // (`∃r.X⊑E`, X∈label[d]), instead of rescanning the whole filler
                // label crossed with the role closure. Super-role matches are
                // covered because the lift below materialises a separate edge
                // (c,super_role,d), which fires `prop[(d,super_role)]` in turn.
                // The stored slice is iterated in place (no snapshot copy):
                // see `fire_edge_nf4` for why `prop[(d,r)]` is stable across
                // the loop, self-edge c==d included. Skipped entirely when
                // there are no NF4 axioms.
                if !nf4_already_fired && !idx.nf4_by_filler.is_empty() {
                    prof.nf4_edge_scan += st.fire_edge_nf4(c, r, d);
                }
                // R⊥-edge: edge to a known-unsat target propagates.
                if st.sub_super[d as usize].contains(&BOTTOM) {
                    st.add_sub(c, BOTTOM);
                }
                // R∘ (NF7): compose with edges leaving d. Skipped with no chains.
                if !idx.nf7_by_pair.is_empty() {
                    let out: Vec<(u32, u32)> = st.edges[d as usize].iter().copied().collect();
                    prof.nf7_scan += out.len() as u64;
                    for (r2, e) in out {
                        if let Some(sups) = idx.nf7_by_pair.get(&(r, r2)) {
                            for &nfsup in sups {
                                for &super_role in
                                    idx.role_sub.get(nfsup as usize).unwrap_or(&empty)
                                {
                                    st.add_edge(c, super_role, e);
                                }
                            }
                        }
                    }
                    // Symmetric: edge into c with role r0 plus this new edge.
                    // Only the roles that actually compose with `r` are read out
                    // of the backward-link index; predecessors along the other
                    // roles are never materialised (the loop body was a no-op
                    // for them anyway).
                    let mut preds: Vec<(u32, u32)> = Vec::new();
                    for &r0 in &st.in_roles[c as usize] {
                        if !idx.nf7_by_pair.contains_key(&(r0, r)) {
                            continue;
                        }
                        if let Some(ps) = st.in_by_role.get(&(c, r0)) {
                            preds.extend(ps.iter().map(|&p| (p, r0)));
                        }
                    }
                    for (parent, r0) in preds {
                        if let Some(sups) = idx.nf7_by_pair.get(&(r0, r)) {
                            for &nfsup in sups {
                                for &super_role in
                                    idx.role_sub.get(nfsup as usize).unwrap_or(&empty)
                                {
                                    st.add_edge(parent, super_role, d);
                                }
                            }
                        }
                    }
                }
                // Plain role-hierarchy lift: an R-edge is also an S-edge for R ⊑ S.
                for &super_role in idx.role_supers(r) {
                    if super_role != r {
                        st.add_edge(c, super_role, d);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Completeness certificate over the canonical model
// ---------------------------------------------------------------------------
//
// The saturated structure is the canonical model `I` of the EL subset:
// domain = the satisfiable concept nodes, `x_C ∈ D^I` iff `C ⊑ D` was derived,
// `(x_C, x_D) ∈ R^I` iff the edge `(C, R, D)` was derived. At fixpoint `I`
// satisfies every EL clause (each completion rule is exactly the closure
// condition of one normal form). If `I` ALSO satisfies every residual (non-EL)
// clause, then `I ⊨ O` for the full ontology `O`, and the EL answer is exact:
// for any entailment `O ⊨ A ⊑ B` we have `x_A ∈ A^I` (Init), hence
// `x_A ∈ B^I` (since `I ⊨ O`), hence `A ⊑ B` was already derived (membership
// IS derivedness). The same argument covers unsatisfiable classes (an alive
// node `x_A` witnesses `O ⊭ A ⊑ ⊥`) and consistency (a model exists). So a
// passing certificate yields a sound AND complete classification; a failing
// one returns `None` and the caller falls back to the disjunctive context
// engine. Never an approximation.
//
// (Calculus-logic change: needs Lean certification of the canonical-model
// lemma; deferred by explicit decision, see CHANGELOG.)

/// A residual atom, compiled to interned ids + per-clause variable indices.
#[derive(Clone, Copy)]
enum RAtom {
    C { cid: u32, v: usize },
    R { rid: u32, s: usize, t: usize },
    Eq { s: usize, t: usize },
}

#[derive(Clone)]
enum ROrigin {
    Source { source: String, name: usize },
    Function { function: u32, witness: u32 },
}

/// A residual clause: `body -> head`, universally quantified over `nvars`
/// variables.  Skolem terms `f(x)` are compiled to *pinned* variables, fixed
/// to a dedicated canonical witness for that skolem function. Each witness is
/// made an EL subclass of the NF3 filler, so it receives the filler's completed
/// label and existential structure while remaining distinct from witnesses for
/// other functions. This makes ≥n witness-distinctness clauses
/// (`Q(x) ∧ f₀(x) ≈ f₁(x) → ⊥`) and other fun-term residuals checkable:
/// distinct skolem functions denote distinct domain elements even when they
/// have the same filler concept.
struct RClause {
    nvars: usize,
    /// Exact source/function namespace origin for every compiled slot. This is
    /// emitted to Lean, which independently reconstructs compilation evidence.
    origins: Vec<ROrigin>,
    body: Vec<RAtom>,
    head: Vec<RAtom>,
    /// (variable index, canonical node) fixed before evaluation
    pins: Vec<(usize, u32)>,
}

/// Compile the residual clauses for certificate checking. Returns `None` if
/// any clause has a shape the checker cannot evaluate (function/`ind`/`aux`
/// terms, equality in the body) — the caller then bails to the context engine
/// BEFORE paying for saturation. Concept names mentioned only residually are
/// added to `nfs.concept_names` so they get canonical-model nodes (required
/// for the completeness argument when they appear as query subjects).
fn compile_residual(
    residual: &[JClause],
    it: &mut Interner,
    nfs: &mut Nfs,
    skolem_target: &HashMap<u32, (u32, u32, u32)>,
) -> Option<Vec<RClause>> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum ResidualVarKey<'a> {
        Source(&'a str),
        Function(&'a str),
    }
    let debug = std::env::var("KM_ELC_DEBUG").is_ok();
    macro_rules! bail {
        ($c:expr, $why:expr) => {{
            if debug {
                eprintln!(
                    "KM_ELC_CERT uncheckable residual ({}): {}",
                    $why,
                    serde_json::to_string($c).unwrap_or_default()
                );
            }
            return None;
        }};
    }
    // tiny per-clause var sets: linear scan beats hashing
    fn vid<'a>(vars: &mut Vec<ResidualVarKey<'a>>, key: ResidualVarKey<'a>) -> usize {
        if let Some(i) = vars.iter().position(|v| *v == key) {
            return i;
        }
        vars.push(key);
        vars.len() - 1
    }
    let mut out = Vec::with_capacity(residual.len());
    let mut skolem_witness: HashMap<u32, u32> = HashMap::default();
    for c in residual {
        let mut vars: Vec<ResidualVarKey<'_>> = Vec::new();
        let mut pins: Vec<(usize, u32)> = Vec::new();
        let mut body = Vec::with_capacity(c.body.len());
        let mut head = Vec::with_capacity(c.head.len());
        // a term: plain variable, or a skolem `f(x)` pinned to its filler node
        macro_rules! term_v {
            ($t:expr) => {
                match $t {
                    JTerm::Var { name } => vid(&mut vars, ResidualVarKey::Source(name)),
                    JTerm::Fun { function, arg } => {
                        if !matches!(arg.as_ref(), JTerm::Var { .. }) {
                            bail!(c, "nested fun term");
                        }
                        let fnid = it.intern(function);
                        let (sub, role, filler) = match skolem_target.get(&fnid) {
                            Some(&target) => target,
                            None => bail!(c, "fun term without NF3 filler"),
                        };
                        let witness = match skolem_witness.entry(fnid) {
                            std::collections::hash_map::Entry::Occupied(e) => *e.get(),
                            std::collections::hash_map::Entry::Vacant(e) => {
                                let witness = it.intern(&format!("__cert_witness__{function}"));
                                nfs.concept_names.insert(witness);
                                nfs.nf1.push(Nf1 {
                                    sub: witness,
                                    sup: filler,
                                });
                                let nf3 = match nfs.nf3.iter_mut().find(|nf| {
                                    nf.sub == sub && nf.role == role && nf.filler == filler
                                }) {
                                    Some(nf3) => nf3,
                                    None => bail!(c, "fun term without matching NF3"),
                                };
                                nf3.filler = witness;
                                e.insert(witness);
                                witness
                            }
                        };
                        let v = vid(&mut vars, ResidualVarKey::Function(function));
                        if !pins.iter().any(|&(pv, _)| pv == v) {
                            pins.push((v, witness));
                        }
                        v
                    }
                    _ => bail!(c, "ind/aux term"),
                }
            };
        }
        for (atoms, dst, is_head) in [(&c.body, &mut body, false), (&c.head, &mut head, true)] {
            for a in atoms {
                match a {
                    JAtom::Concept { concept, term } => {
                        let v = term_v!(term);
                        let cid = it.intern(concept);
                        nfs.concept_names.insert(cid);
                        dst.push(RAtom::C { cid, v });
                    }
                    JAtom::Role {
                        role,
                        source,
                        target,
                    } => {
                        let s = term_v!(source);
                        let t = term_v!(target);
                        let rid = it.intern(role);
                        nfs.role_names.insert(rid);
                        dst.push(RAtom::R { rid, s, t });
                    }
                    JAtom::Eq { left, right } => {
                        // An equality conclusion (number restriction) holds
                        // only under identical bindings.  An equality
                        // HYPOTHESIS is checkable when both sides are bound
                        // by the time it is evaluated (pinned skolems or
                        // variables generated by other body atoms) — the
                        // bound-coverage check below guarantees that.
                        let _ = is_head;
                        let s = term_v!(left);
                        let t = term_v!(right);
                        dst.push(RAtom::Eq { s, t });
                    }
                }
            }
        }
        // body equalities need both sides bound: by a pin or a body C/R atom
        let mut coverable = vec![false; vars.len()];
        for &(v, _) in &pins {
            coverable[v] = true;
        }
        for a in &body {
            match *a {
                RAtom::C { v, .. } => coverable[v] = true,
                RAtom::R { s, t, .. } => {
                    coverable[s] = true;
                    coverable[t] = true;
                }
                RAtom::Eq { .. } => {}
            }
        }
        let eq_ok = body.iter().all(|a| match *a {
            RAtom::Eq { s, t } => coverable[s] && coverable[t],
            _ => true,
        });
        if !eq_ok {
            bail!(c, "body equality over unbound variable");
        }
        out.push(RClause {
            nvars: vars.len(),
            origins: vars
                .iter()
                .enumerate()
                .map(|(slot, key)| match key {
                    ResidualVarKey::Source(source) => Some(ROrigin::Source {
                        source: (*source).to_string(),
                        name: slot,
                    }),
                    ResidualVarKey::Function(function) => {
                        let function = it.id(function)?;
                        let witness = *skolem_witness.get(&function)?;
                        Some(ROrigin::Function { function, witness })
                    }
                })
                .collect::<Option<Vec<_>>>()?,
            body,
            head,
            pins,
        });
    }
    Some(out)
}

fn build_lean_residual_compilations(
    residual: &[JClause],
    compiled: &[RClause],
    interner: &Interner,
) -> Result<Vec<LeanResidualCompilation>, String> {
    if residual.len() != compiled.len() {
        return Err("residual source/compiled clause count mismatch".into());
    }
    fn raw_term(
        term: &JTerm,
        clause: &RClause,
        interner: &Interner,
    ) -> Result<LeanRawTerm, String> {
        match term {
            JTerm::Var { name } => {
                let source_name = clause.origins.iter().find_map(|origin| match origin {
                    ROrigin::Source { source, name: source_name } if source == name => {
                        Some(*source_name)
                    }
                    _ => None,
                });
                // A variable occurring only as the ignored argument of a
                // constant Skolem interpretation need not own a compiled slot.
                let name = source_name.or_else(|| (clause.nvars > 0).then_some(0))
                    .ok_or_else(|| format!("residual variable {name} has no slot"))?;
                Ok(LeanRawTerm::Var { name: name as u32 })
            }
            JTerm::Fun { function, arg } => Ok(LeanRawTerm::Fun {
                function: interner
                    .id(function)
                    .ok_or_else(|| format!("uninterned residual function {function}"))?,
                argument: Box::new(raw_term(arg, clause, interner)?),
            }),
            JTerm::Ind { .. } | JTerm::Aux { .. } => {
                Err("unsupported residual term reached Lean payload".into())
            }
        }
    }
    fn raw_atom(
        atom: &JAtom,
        clause: &RClause,
        interner: &Interner,
    ) -> Result<LeanResidualAtom, String> {
        match atom {
            JAtom::Concept { concept, term } => Ok(LeanResidualAtom::Concept {
                concept: interner
                    .id(concept)
                    .ok_or_else(|| format!("uninterned residual concept {concept}"))?,
                term: raw_term(term, clause, interner)?,
            }),
            JAtom::Role { role, source, target } => Ok(LeanResidualAtom::Role {
                role: interner
                    .id(role)
                    .ok_or_else(|| format!("uninterned residual role {role}"))?,
                source: raw_term(source, clause, interner)?,
                target: raw_term(target, clause, interner)?,
            }),
            JAtom::Eq { left, right } => Ok(LeanResidualAtom::Eq {
                left: raw_term(left, clause, interner)?,
                right: raw_term(right, clause, interner)?,
            }),
        }
    }
    fn compiled_atom(atom: &RAtom) -> LeanCompiledResidualAtom {
        match *atom {
            RAtom::C { cid, v } => LeanCompiledResidualAtom::Concept {
                concept: cid,
                slot: v,
            },
            RAtom::R { rid, s, t } => LeanCompiledResidualAtom::Role {
                role: rid,
                source: s,
                target: t,
            },
            RAtom::Eq { s, t } => LeanCompiledResidualAtom::Eq { left: s, right: t },
        }
    }

    residual
        .iter()
        .zip(compiled)
        .map(|(raw, clause)| {
            let origins = clause
                .origins
                .iter()
                .map(|origin| match origin {
                    ROrigin::Source { name, .. } => LeanResidualOrigin::Source { name: *name },
                    ROrigin::Function { function, witness } => LeanResidualOrigin::Function {
                        function: *function,
                        witness: *witness,
                    },
                })
                .collect();
            Ok(LeanResidualCompilation {
                variable_count: clause.nvars,
                origins,
                raw: LeanResidualClause {
                    body: raw
                        .body
                        .iter()
                        .map(|atom| raw_atom(atom, clause, interner))
                        .collect::<Result<_, _>>()?,
                    head: raw
                        .head
                        .iter()
                        .map(|atom| raw_atom(atom, clause, interner))
                        .collect::<Result<_, _>>()?,
                },
                body: clause.body.iter().map(compiled_atom).collect(),
                head: clause.head.iter().map(compiled_atom).collect(),
                pins: clause.pins.clone(),
            })
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Cardinality-aware repair guidance
// ---------------------------------------------------------------------------
//
// The recognisers below read structure back out of the compiled residual: they
// match on variable wiring alone and never on concept or role spelling. The
// repair search consults them through [`CardGuide`] to ORDER its choices.
// Ordering choices cannot change an answer: a pass model is accepted only when
// [`cert_round`] finds EVERY residual clause satisfied, and that check does not
// consult a recogniser. A recogniser that misses a clause leaves the search
// exactly as it was; one that fires on an unintended shape can only send the
// search down a different branch of the same disjunction.

/// A qualified-cardinality UPPER bound recovered from a residual clause.
///
/// The frontend normalises `G ⊑ ≤n R.C` into
/// `G(x) ∧ ⋀_{i≤n}(C(y_i) ∧ R(x,y_i)) → ⋁_{i<j} y_i ≈ y_j`: once the guard
/// holds at `x` and `x` carries `n+1` successors in `C`, two of them are the
/// same element.
#[derive(Debug, PartialEq, Eq)]
struct AtMostBound {
    /// concepts that must ALL hold at the source node for the bound to bite
    guards: Vec<u32>,
    role: u32,
    /// concepts every counted successor carries (empty for unqualified `≤n R`)
    fillers: Vec<u32>,
    /// `n`: the clause enumerates `n+1` successor variables
    bound: usize,
}

/// Recognise `≤n R.C`. Returns `None` for every other shape.
fn recognize_at_most(rc: &RClause) -> Option<AtMostBound> {
    if rc.head.is_empty() || !rc.pins.is_empty() {
        return None;
    }
    // Head must be exactly the set of unordered pairs over one successor set.
    let mut succ: Vec<usize> = Vec::new();
    let mut pairs: HashSet<(usize, usize)> = HashSet::default();
    for a in &rc.head {
        let RAtom::Eq { s, t } = *a else { return None };
        if s == t {
            return None;
        }
        if !succ.contains(&s) {
            succ.push(s);
        }
        if !succ.contains(&t) {
            succ.push(t);
        }
        if !pairs.insert((s.min(t), s.max(t))) {
            return None;
        }
    }
    let k = succ.len();
    if k < 2 || pairs.len() != k * (k - 1) / 2 {
        return None;
    }
    // Body: one `R(source, y_i)` per successor, one shared role and source,
    // identical filler concepts on every successor, guards on the source.
    let mut role: Option<u32> = None;
    let mut source: Option<usize> = None;
    let mut edge_seen: HashSet<usize> = HashSet::default();
    let mut per_succ: HashMap<usize, Vec<u32>> = HashMap::default();
    let mut guard_atoms: Vec<(u32, usize)> = Vec::new();
    for a in &rc.body {
        match *a {
            RAtom::R { rid, s, t } => {
                if !succ.contains(&t) || succ.contains(&s) {
                    return None;
                }
                match role {
                    None => role = Some(rid),
                    Some(r) if r == rid => {}
                    _ => return None,
                }
                match source {
                    None => source = Some(s),
                    Some(x) if x == s => {}
                    _ => return None,
                }
                if !edge_seen.insert(t) {
                    return None;
                }
            }
            RAtom::C { cid, v } => {
                if succ.contains(&v) {
                    per_succ.entry(v).or_default().push(cid);
                } else {
                    guard_atoms.push((cid, v));
                }
            }
            RAtom::Eq { .. } => return None,
        }
    }
    let (role, source) = (role?, source?);
    if edge_seen.len() != k {
        return None;
    }
    let mut guards: Vec<u32> = Vec::new();
    for (cid, v) in guard_atoms {
        if v != source {
            return None;
        }
        guards.push(cid);
    }
    // Every successor carries the same filler set, so one count decides the
    // bound; differing fillers are a different (unrecognised) constraint.
    let mut fillers: Option<Vec<u32>> = None;
    for &y in &succ {
        let mut fs = per_succ.remove(&y).unwrap_or_default();
        fs.sort_unstable();
        fs.dedup();
        match &fillers {
            None => fillers = Some(fs),
            Some(prev) if *prev == fs => {}
            _ => return None,
        }
    }
    Some(AtMostBound {
        guards,
        role,
        fillers: fillers.unwrap_or_default(),
        bound: k - 1,
    })
}

/// Recognise a witness DISTINCTNESS constraint `G(x) ∧ f_i(x) ≈ f_j(x) → ⊥`,
/// the `≥n R.C` half of a number restriction, and return the two canonical
/// witness nodes it forces apart.
///
/// This is the shape that makes at-most repair delicate: the certificate model
/// keeps ONE canonical node per skolem function, shared across every source
/// element (see [`RClause`]), so identifying such a pair to satisfy an at-most
/// restriction at one node contradicts this clause at every node carrying the
/// guard.
fn recognize_distinct_pins(rc: &RClause) -> Option<(u32, u32)> {
    if !rc.head.is_empty() {
        return None;
    }
    let mut eq: Option<(usize, usize)> = None;
    for a in &rc.body {
        if let RAtom::Eq { s, t } = *a {
            if eq.is_some() {
                return None;
            }
            eq = Some((s, t));
        }
    }
    let (s, t) = eq?;
    let pin = |v: usize| {
        rc.pins
            .iter()
            .find(|&&(pv, _)| pv == v)
            .map(|&(_, node)| node)
    };
    let (a, b) = (pin(s)?, pin(t)?);
    if a == b {
        return None;
    }
    Some((a, b))
}

/// How many qualifying successors past a bound the incompatibility probe
/// collects before it stops looking. The probe only ever REMOVES a choice from
/// the search's preferred tier, so stopping early costs guidance, never
/// validity.
const SUCC_PROBE_MARGIN: usize = 8;

/// Static, ontology-independent guidance for the repair search, read off the
/// compiled residual once per certificate.
///
/// An exhaustive disjoint partition between a `≤n R.C` definer and a `≥m R.C`
/// definer with `m > n` is where the pinning bites. Every element must take a
/// side, and taking the at-most side at a node that already carries `m`
/// pairwise pinned successors is locally unsatisfiable. Left unrecognised, the
/// search merges the pinned witnesses, the resulting `⊥` fires several closure
/// rounds later, and the blame no longer reaches the side choice that caused
/// it, so the restart re-derives the same rounds and bans a triple that was
/// never at fault.
///
/// This is search guidance only. Nothing here discharges a residual clause and
/// nothing here is consulted by [`cert_round`], which still has to find every
/// residual clause satisfied before a pass model is accepted.
struct CardGuide {
    /// canonical node pairs a `≥n` clause pins apart, as stored (unordered)
    pinned_apart: Vec<(u32, u32)>,
    /// qualified at-most bounds recovered from the residual
    bounds: Vec<AtMostBound>,
    /// guard concept -> the bounds it helps activate. Only bounds with at
    /// least one guard appear: an unguarded bound is active everywhere, so no
    /// choice can activate it and it is not a partition side.
    by_guard: HashMap<u32, Vec<usize>>,
}

impl CardGuide {
    fn new(rcs: &[RClause]) -> CardGuide {
        let mut pinned_apart: Vec<(u32, u32)> = Vec::new();
        let mut bounds: Vec<AtMostBound> = Vec::new();
        let mut by_guard: HashMap<u32, Vec<usize>> = HashMap::default();
        for rc in rcs {
            if let Some(b) = recognize_at_most(rc) {
                let bi = bounds.len();
                for &g in &b.guards {
                    by_guard.entry(g).or_default().push(bi);
                }
                bounds.push(b);
            } else if let Some((a, b)) = recognize_distinct_pins(rc) {
                pinned_apart.push((a, b));
            }
        }
        CardGuide {
            pinned_apart,
            bounds,
            by_guard,
        }
    }

    /// Nothing recognised: every query below is inert, so the search runs
    /// exactly as it did before this guidance existed.
    fn is_inert(&self) -> bool {
        self.pinned_apart.is_empty() && self.by_guard.is_empty()
    }

    /// May the pass model identify `x` and `y`?
    ///
    /// Only a pinned pair is refused. Refusing is the whole point: the pin is
    /// a residual clause of the model under construction, so merging its two
    /// nodes makes that clause false everywhere its guard holds. Every other
    /// pair stays available, so this cannot narrow the search below what it
    /// could already reach.
    fn merge_legal(&self, round: &CardRound, repr: &mut [u32], x: u32, y: u32) -> bool {
        let (a, b) = (uf_find(repr, x), uf_find(repr, y));
        a == b || !round.apart.contains(&(a.min(b), a.max(b)))
    }

    /// Would identifying `x` and `y` immediately drive the merged node to `⊥`
    /// through a disjointness axiom? A soft preference only: a clashing pair
    /// is still merged when it is the only legal one, because a node reaching
    /// `⊥` removes it from the certificate domain rather than invalidating the
    /// model.
    fn merge_clashes(
        &self,
        st: &State,
        disj: &HashMap<u32, HashSet<u32>>,
        repr: &mut [u32],
        x: u32,
        y: u32,
    ) -> bool {
        let (a, b) = (uf_find(repr, x), uf_find(repr, y));
        if a == b {
            return false;
        }
        let (la, lb) = (&st.sub_super[a as usize], &st.sub_super[b as usize]);
        let (small, large) = if la.len() <= lb.len() {
            (la, lb)
        } else {
            (lb, la)
        };
        small.iter().any(|p| {
            disj.get(p)
                .is_some_and(|ds| ds.iter().any(|q| large.contains(q)))
        })
    }

    /// Does asserting concept `cid` at `nd` activate a qualified at-most bound
    /// this node cannot satisfy — more qualifying successors than the bound
    /// allows, with every candidate identification pinned apart?
    ///
    /// A `true` verdict demotes `cid` out of the search's preferred choice
    /// tier. It never bans the choice: if no other disjunct survives, `cid` is
    /// still taken and the resulting model is validated in full.
    fn locally_incompatible(
        &self,
        round: &mut CardRound,
        st: &State,
        repr: &mut [u32],
        nd: u32,
        cid: u32,
    ) -> bool {
        let Some(bis) = self.by_guard.get(&cid) else {
            return false;
        };
        for &bi in bis {
            let b = &self.bounds[bi];
            // the bound bites only once every guard holds at the source
            if !b
                .guards
                .iter()
                .all(|&g| g == cid || st.sub_super[nd as usize].contains(&g))
            {
                continue;
            }
            if let Some(&hit) = round.memo.get(&(nd, bi)) {
                if hit {
                    round.demoted += 1;
                    return true;
                }
                continue;
            }
            let bad = self.over_full_and_pinned(round, st, repr, nd, b);
            round.memo.insert((nd, bi), bad);
            if bad {
                round.demoted += 1;
                return true;
            }
        }
        false
    }

    /// The uncached half of [`Self::locally_incompatible`]: does `nd` carry
    /// more distinct qualifying successors than `b` allows, with every pair
    /// among them pinned apart?
    fn over_full_and_pinned(
        &self,
        round: &CardRound,
        st: &State,
        repr: &mut [u32],
        nd: u32,
        b: &AtMostBound,
    ) -> bool {
        let mut succ: Vec<u32> = Vec::new();
        for &(r, t) in &st.edges[nd as usize] {
            if r != b.role {
                continue;
            }
            let tr = uf_find(repr, t);
            if succ.contains(&tr) {
                continue;
            }
            if !b
                .fillers
                .iter()
                .all(|f| st.sub_super[tr as usize].contains(f))
            {
                continue;
            }
            succ.push(tr);
            if succ.len() > b.bound + SUCC_PROBE_MARGIN {
                break;
            }
        }
        if succ.len() <= b.bound {
            return false;
        }
        // over the bound: satisfiable here iff some pair may still be identified
        for i in 0..succ.len() {
            for j in (i + 1)..succ.len() {
                let (u, w) = (succ[i], succ[j]);
                if !round.apart.contains(&(u.min(w), u.max(w))) {
                    return false;
                }
            }
        }
        true
    }
}

/// The quotient-dependent half of [`CardGuide`], valid for one repair round.
///
/// `apart` lifts the pinned pairs to the current union-find representatives
/// and is rebuilt whenever the quotient changes. `memo` caches the
/// successor-count probe for the round; it is a steering hint, so a stale
/// entry can only send the search down a different branch of a disjunction it
/// was free to choose either way.
#[derive(Default)]
struct CardRound {
    apart: HashSet<(u32, u32)>,
    memo: HashMap<(u32, usize), bool>,
    /// choices demoted out of the preferred tier this round (debug reporting)
    demoted: usize,
}

impl CardRound {
    fn resync(&mut self, guide: &CardGuide, repr: &mut [u32]) {
        self.apart.clear();
        self.memo.clear();
        for &(x, y) in &guide.pinned_apart {
            let (a, b) = (uf_find(repr, x), uf_find(repr, y));
            if a != b {
                self.apart.insert((a.min(b), a.max(b)));
            }
        }
    }
}

/// Hard cap on violations recorded per repair round: bounds round memory; the
/// uncollected remainder is caught by the recheck after this round's repairs.
const REPAIR_VIOL_CAP: usize = 100_000;

/// How many conflict-driven restarts one repair pass may spend before it gives
/// up on its polarity. Each restart re-derives the pass from the base model, so
/// a search that charges one restart per subject cannot outrun a residual whose
/// bad choices outnumber this.
const REPAIR_RESTART_CAP: usize = 64;

/// The body-atom enumeration index [`cert_round`] joins over, kept across the
/// rounds of one repair pass.
///
/// Built from scratch a round costs one pass over every label of every live
/// node (`members`) plus one over every edge of every live node
/// (`edges_by_role`). On ore_ont_1194 that is 78M label entries and 44M edges,
/// 1.4 s of the 1.5 s a repair round takes — paid again for all 16 rounds of
/// every conflict-driven restart, even though a round changes ~0.1M facts.
/// Refreshing from the round's delta is EXACT, not an approximation, because
/// both indexes are defined by an outer loop over `nodes`:
///
/// * `members[s]` is the subsequence of `nodes` whose label contains `s`. Its
///   order is `nodes` order — the inner `sub_super[c]` iteration only decides
///   which bucket an entry lands in, never its position within one — so a new
///   member merged in at its `nodes` position gives a bucket bit-identical to
///   a rebuild.
/// * `edges_by_role[r]` also runs over `nodes` outermost, but within a node it
///   follows `edges[c]`'s own iteration order, which an insert may permute.
///   It is therefore reused only while `State::edge_epoch` is unchanged (no
///   edge added, removed, or re-cloned anywhere) and rebuilt in full otherwise.
///
/// A change to the live domain invalidates both — a node that dies has to
/// leave every bucket — so those rounds rebuild from scratch as well. Every
/// index this hands to the join is thus the one a full rebuild would produce,
/// which is what keeps the violation enumeration order, and with it the repair
/// choices and the accepted models, unchanged.
#[derive(Default)]
struct CertIdx {
    alive: Vec<bool>,
    nodes: Vec<u32>,
    /// position of each node in `nodes`; `u32::MAX` for everything else
    npos: Vec<u32>,
    needed_c: HashSet<u32>,
    needed_r: HashSet<u32>,
    members: HashMap<u32, Vec<u32>>,
    edges_by_role: HashMap<u32, Vec<(u32, u32)>>,
    /// `State::edge_epoch` when `edges_by_role` was last built
    edge_epoch: u64,
    built: bool,
}

/// A caller's offer to refresh [`CertIdx`] incrementally: the index itself, the
/// `sub_super` additions since it was last refreshed (`None` forces a full
/// rebuild) and the state's current edge epoch.
struct CertReuse<'a> {
    idx: &'a mut CertIdx,
    delta: Option<&'a [(u32, u32)]>,
    edge_epoch: u64,
}

impl CertIdx {
    /// Discard everything: the next refresh rebuilds from the structure. For
    /// the callers that mutate the structure in a way no delta can describe.
    fn invalidate(&mut self) {
        self.built = false;
    }

    fn build_members(&mut self, sub_super: &[HashSet<u32>]) {
        self.members = HashMap::default();
        for &c in &self.nodes {
            for &s in &sub_super[c as usize] {
                if self.needed_c.contains(&s) {
                    self.members.entry(s).or_default().push(c);
                }
            }
        }
    }

    fn build_edges(&mut self, edges: &[HashSet<(u32, u32)>]) {
        self.edges_by_role = HashMap::default();
        for &c in &self.nodes {
            for &(r, d) in &edges[c as usize] {
                if self.needed_r.contains(&r) && self.alive[d as usize] {
                    self.edges_by_role.entry(r).or_default().push((c, d));
                }
            }
        }
    }

    /// Merge the round's new memberships into the existing buckets at their
    /// `nodes` positions. Entries already present are dropped, so the result is
    /// the same list `build_members` would produce over the new labels.
    fn merge_members(&mut self, delta: &[(u32, u32)]) {
        let CertIdx {
            npos,
            needed_c,
            members,
            ..
        } = self;
        let mut fresh: HashMap<u32, Vec<u32>> = HashMap::default();
        for &(c, s) in delta {
            if needed_c.contains(&s) && npos[c as usize] != u32::MAX {
                fresh.entry(s).or_default().push(c);
            }
        }
        for (s, mut add) in fresh {
            add.sort_unstable_by_key(|&c| npos[c as usize]);
            add.dedup();
            let bucket = members.entry(s).or_default();
            let mut out: Vec<u32> = Vec::with_capacity(bucket.len() + add.len());
            let (mut i, mut j) = (0usize, 0usize);
            while i < bucket.len() && j < add.len() {
                let (pi, pj) = (npos[bucket[i] as usize], npos[add[j] as usize]);
                match pi.cmp(&pj) {
                    std::cmp::Ordering::Less => {
                        out.push(bucket[i]);
                        i += 1;
                    }
                    std::cmp::Ordering::Greater => {
                        out.push(add[j]);
                        j += 1;
                    }
                    std::cmp::Ordering::Equal => {
                        out.push(bucket[i]);
                        i += 1;
                        j += 1;
                    }
                }
            }
            out.extend_from_slice(&bucket[i..]);
            out.extend_from_slice(&add[j..]);
            *bucket = out;
        }
    }

    fn refresh(
        &mut self,
        rcs: &[RClause],
        concept_names: &HashSet<u32>,
        sub_super: &[HashSet<u32>],
        edges: &[HashSet<(u32, u32)>],
        delta: Option<&[(u32, u32)]>,
        edge_epoch: u64,
    ) {
        let n = sub_super.len();
        if !self.built {
            for rc in rcs {
                for a in &rc.body {
                    match a {
                        RAtom::C { cid, .. } => {
                            self.needed_c.insert(*cid);
                        }
                        RAtom::R { rid, .. } => {
                            self.needed_r.insert(*rid);
                        }
                        RAtom::Eq { .. } => {}
                    }
                }
            }
        }
        // domain: satisfiable concept nodes
        let mut alive = vec![false; n];
        let mut nodes: Vec<u32> = Vec::new();
        for &cn in concept_names {
            if cn != BOTTOM && !sub_super[cn as usize].contains(&BOTTOM) {
                alive[cn as usize] = true;
                nodes.push(cn);
            }
        }
        if !self.built || self.nodes != nodes {
            self.npos = vec![u32::MAX; n];
            for (i, &c) in nodes.iter().enumerate() {
                self.npos[c as usize] = i as u32;
            }
            self.alive = alive;
            self.nodes = nodes;
            self.build_members(sub_super);
            self.build_edges(edges);
            self.edge_epoch = edge_epoch;
            self.built = true;
            return;
        }
        match delta {
            Some(d) => self.merge_members(d),
            None => self.build_members(sub_super),
        }
        if self.edge_epoch != edge_epoch {
            self.build_edges(edges);
            self.edge_epoch = edge_epoch;
        }
        if cert_audit() {
            self.audit(sub_super, edges);
        }
    }

    /// `KM_ELC_CERT_AUDIT=1`: assert that the refreshed index is the one a full
    /// rebuild would have produced, bucket contents and order included. Costs a
    /// full rebuild per round, so it is opt-in — it exists to check the reuse
    /// against the real repair traces, not to run in production.
    fn audit(&mut self, sub_super: &[HashSet<u32>], edges: &[HashSet<(u32, u32)>]) {
        let members = std::mem::take(&mut self.members);
        let edges_by_role = std::mem::take(&mut self.edges_by_role);
        self.build_members(sub_super);
        self.build_edges(edges);
        assert_eq!(
            members, self.members,
            "KM_ELC_CERT_AUDIT: reused `members` differs from a rebuild"
        );
        assert_eq!(
            edges_by_role, self.edges_by_role,
            "KM_ELC_CERT_AUDIT: reused `edges_by_role` differs from a rebuild"
        );
    }
}

fn cert_audit() -> bool {
    static AUDIT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *AUDIT.get_or_init(|| std::env::var_os("KM_ELC_CERT_AUDIT").is_some())
}

/// One certificate round over the structure `(sub_super, edges)`.
///
/// With `collect == None` this is the plain check: `true` iff every residual
/// clause is satisfied, aborting on the first violation (or on budget
/// exhaustion, which conservatively returns `false`).
///
/// With `collect == Some(out)` it ENUMERATES violating instances instead of
/// aborting: each violation is recorded as `(clause index, full binding)`, up
/// to [`REPAIR_VIOL_CAP`] per round. Returns `true` iff no violation was found
/// and the budget survived. On `false`: an empty `out` means budget exhaustion
/// (the caller must fail conservatively); a non-empty `out` is repair work.
fn cert_round(
    rcs: &[RClause],
    concept_names: &HashSet<u32>,
    sub_super: &[HashSet<u32>],
    edges: &[HashSet<(u32, u32)>],
    // node identity modulo repair merges (fully compressed union-find): a
    // merged node and its witness mirror are the SAME quotient element, so
    // equalities must compare representatives, not raw ids
    repr: Option<&[u32]>,
    budget: &mut u64,
    mut collect: Option<&mut Vec<(usize, Vec<u32>)>>,
    debug: bool,
    // the caller's cross-round enumeration index; `None` builds a throwaway one
    reuse: Option<CertReuse<'_>>,
) -> bool {
    // enumeration indexes for the body atoms, over the domain of satisfiable
    // concept nodes
    let mut scratch = CertIdx::default();
    let (idx, delta, epoch) = match reuse {
        Some(r) => (r.idx, r.delta, r.edge_epoch),
        None => (&mut scratch, None, 0),
    };
    idx.refresh(rcs, concept_names, sub_super, edges, delta, epoch);
    let CertIdx {
        alive,
        nodes,
        members,
        edges_by_role,
        ..
    } = &*idx;
    let empty_m: Vec<u32> = Vec::new();
    let empty_e: Vec<(u32, u32)> = Vec::new();

    // recursive join over one clause; returns false on a violating assignment
    // (collect == None), on a full violation round (collect cap reached), or
    // on budget exhaustion (budget == 0).
    #[allow(clippy::too_many_arguments)]
    fn join(
        rc: &RClause,
        rci: usize,
        order: &[usize],
        depth: usize,
        asg: &mut Vec<Option<u32>>,
        nodes: &[u32],
        alive: &[bool],
        sub_super: &[HashSet<u32>],
        edges: &[HashSet<(u32, u32)>],
        repr: Option<&[u32]>,
        members: &HashMap<u32, Vec<u32>>,
        edges_by_role: &HashMap<u32, Vec<(u32, u32)>>,
        empty_m: &Vec<u32>,
        empty_e: &Vec<(u32, u32)>,
        budget: &mut u64,
        collect: &mut Option<&mut Vec<(usize, Vec<u32>)>>,
    ) -> bool {
        if *budget == 0 {
            return false;
        }
        if depth == order.len() {
            // body satisfied; bind any remaining (head-only) variables, then
            // require some head atom to hold.
            if let Some(free) = asg.iter().position(|b| b.is_none()) {
                for &nd in nodes {
                    *budget = budget.saturating_sub(1);
                    if *budget == 0 {
                        return false;
                    }
                    asg[free] = Some(nd);
                    if !join(
                        rc,
                        rci,
                        order,
                        depth,
                        asg,
                        nodes,
                        alive,
                        sub_super,
                        edges,
                        repr,
                        members,
                        edges_by_role,
                        empty_m,
                        empty_e,
                        budget,
                        collect,
                    ) {
                        asg[free] = None;
                        return false;
                    }
                }
                asg[free] = None;
                return true;
            }
            let ok = rc.head.iter().any(|a| match *a {
                RAtom::C { cid, v } => sub_super[asg[v].unwrap() as usize].contains(&cid),
                RAtom::R { rid, s, t } => {
                    edges[asg[s].unwrap() as usize].contains(&(rid, asg[t].unwrap()))
                }
                RAtom::Eq { s, t } => {
                    let (a, b) = (asg[s].unwrap(), asg[t].unwrap());
                    match repr {
                        Some(r) => r[a as usize] == r[b as usize],
                        None => a == b,
                    }
                }
            });
            if ok {
                return true;
            }
            if let Some(out) = collect.as_deref_mut() {
                out.push((rci, asg.iter().map(|b| b.unwrap()).collect()));
                // Under the cap, keep enumerating this round's violations.
                return out.len() < REPAIR_VIOL_CAP;
            }
            return false;
        }
        let atom = rc.body[order[depth]];
        match atom {
            RAtom::C { cid, v } => match asg[v] {
                Some(nd) => {
                    *budget = budget.saturating_sub(1);
                    if !sub_super[nd as usize].contains(&cid) {
                        return true; // body unsatisfied: clause holds here
                    }
                    join(
                        rc,
                        rci,
                        order,
                        depth + 1,
                        asg,
                        nodes,
                        alive,
                        sub_super,
                        edges,
                        repr,
                        members,
                        edges_by_role,
                        empty_m,
                        empty_e,
                        budget,
                        collect,
                    )
                }
                None => {
                    for &nd in members.get(&cid).unwrap_or(empty_m) {
                        *budget = budget.saturating_sub(1);
                        if *budget == 0 {
                            return false;
                        }
                        asg[v] = Some(nd);
                        if !join(
                            rc,
                            rci,
                            order,
                            depth + 1,
                            asg,
                            nodes,
                            alive,
                            sub_super,
                            edges,
                            repr,
                            members,
                            edges_by_role,
                            empty_m,
                            empty_e,
                            budget,
                            collect,
                        ) {
                            asg[v] = None;
                            return false;
                        }
                    }
                    asg[v] = None;
                    true
                }
            },
            RAtom::R { rid, s, t } => match (asg[s], asg[t]) {
                (Some(sn), Some(tn)) => {
                    *budget = budget.saturating_sub(1);
                    if !edges[sn as usize].contains(&(rid, tn)) {
                        return true;
                    }
                    join(
                        rc,
                        rci,
                        order,
                        depth + 1,
                        asg,
                        nodes,
                        alive,
                        sub_super,
                        edges,
                        repr,
                        members,
                        edges_by_role,
                        empty_m,
                        empty_e,
                        budget,
                        collect,
                    )
                }
                (Some(sn), None) => {
                    for &(r, d) in &edges[sn as usize] {
                        if r != rid || !alive[d as usize] {
                            continue;
                        }
                        *budget = budget.saturating_sub(1);
                        if *budget == 0 {
                            return false;
                        }
                        asg[t] = Some(d);
                        if !join(
                            rc,
                            rci,
                            order,
                            depth + 1,
                            asg,
                            nodes,
                            alive,
                            sub_super,
                            edges,
                            repr,
                            members,
                            edges_by_role,
                            empty_m,
                            empty_e,
                            budget,
                            collect,
                        ) {
                            asg[t] = None;
                            return false;
                        }
                    }
                    asg[t] = None;
                    true
                }
                (sn_opt, tn_opt) => {
                    for &(c, d) in edges_by_role.get(&rid).unwrap_or(empty_e) {
                        if let Some(sn) = sn_opt {
                            if c != sn {
                                continue;
                            }
                        }
                        if let Some(tn) = tn_opt {
                            if d != tn {
                                continue;
                            }
                        }
                        if s == t && c != d {
                            continue; // reflexive atom R(x,x): one binding
                        }
                        *budget = budget.saturating_sub(1);
                        if *budget == 0 {
                            return false;
                        }
                        let (os, ot) = (asg[s], asg[t]);
                        asg[s] = Some(c);
                        asg[t] = Some(d);
                        if !join(
                            rc,
                            rci,
                            order,
                            depth + 1,
                            asg,
                            nodes,
                            alive,
                            sub_super,
                            edges,
                            repr,
                            members,
                            edges_by_role,
                            empty_m,
                            empty_e,
                            budget,
                            collect,
                        ) {
                            asg[s] = os;
                            asg[t] = ot;
                            return false;
                        }
                        asg[s] = os;
                        asg[t] = ot;
                    }
                    true
                }
            },
            RAtom::Eq { s, t } => match (asg[s], asg[t]) {
                // body equality hypothesis: both sides are bound here (the
                // compile-time coverage check guarantees it) — unequal
                // bindings falsify the body, so the clause holds
                (Some(a), Some(b)) => {
                    *budget = budget.saturating_sub(1);
                    let eq = match repr {
                        Some(r) => r[a as usize] == r[b as usize],
                        None => a == b,
                    };
                    if !eq {
                        return true;
                    }
                    join(
                        rc,
                        rci,
                        order,
                        depth + 1,
                        asg,
                        nodes,
                        alive,
                        sub_super,
                        edges,
                        repr,
                        members,
                        edges_by_role,
                        empty_m,
                        empty_e,
                        budget,
                        collect,
                    )
                }
                // unbound side: cannot evaluate — fail conservatively
                _ => false,
            },
        }
    }

    for (i, rc) in rcs.iter().enumerate() {
        // static atom order: bound-first greedy (atoms whose vars are already
        // bound act as filters; among generators prefer the smaller list).
        // Pinned (skolem) variables start bound to their filler node.
        let mut remaining: Vec<usize> = (0..rc.body.len()).collect();
        let mut order: Vec<usize> = Vec::with_capacity(rc.body.len());
        let mut bound = vec![false; rc.nvars];
        for &(v, _) in &rc.pins {
            bound[v] = true;
        }
        while !remaining.is_empty() {
            let pick = remaining
                .iter()
                .enumerate()
                .min_by_key(|(_, &ai)| match rc.body[ai] {
                    RAtom::C { cid, v } => {
                        if bound[v] {
                            (0usize, 0usize)
                        } else {
                            (1, members.get(&cid).map_or(0, |m| m.len()))
                        }
                    }
                    RAtom::R { rid, s, t } => {
                        let nb = !bound[s] as usize + !bound[t] as usize;
                        if nb == 0 {
                            (0, 0)
                        } else {
                            (1, edges_by_role.get(&rid).map_or(0, |e| e.len()))
                        }
                    }
                    RAtom::Eq { .. } => (2, 0),
                })
                .map(|(j, _)| j)
                .unwrap();
            let ai = remaining.swap_remove(pick);
            match rc.body[ai] {
                RAtom::C { v, .. } => bound[v] = true,
                RAtom::R { s, t, .. } => {
                    bound[s] = true;
                    bound[t] = true;
                }
                RAtom::Eq { .. } => {}
            }
            order.push(ai);
        }
        let mut asg: Vec<Option<u32>> = vec![None; rc.nvars];
        for &(v, node) in &rc.pins {
            asg[v] = Some(node);
        }
        let ok = join(
            rc,
            i,
            &order,
            0,
            &mut asg,
            nodes,
            alive,
            sub_super,
            edges,
            repr,
            members,
            edges_by_role,
            &empty_m,
            &empty_e,
            budget,
            &mut collect,
        );
        if !ok {
            if debug {
                eprintln!(
                    "KM_ELC_CERT fail at residual clause {} of {} (budget_left={})",
                    i,
                    rcs.len(),
                    budget
                );
            }
            return false;
        }
    }
    // In collect mode the join keeps going past violations (under the cap), so
    // reaching this point only means enumeration completed — clean iff nothing
    // was recorded.
    if let Some(out) = collect.as_deref() {
        if !out.is_empty() {
            return false;
        }
    }
    if debug {
        eprintln!(
            "KM_ELC_CERT pass: {} residual clauses over {} nodes (budget_left={})",
            rcs.len(),
            nodes.len(),
            budget
        );
    }
    true
}

/// Check every residual clause against the (already saturated) canonical
/// model. `true` iff all are satisfied. Work is bounded by a fixed budget of
/// candidate extensions; exhausting it fails conservatively.
fn check_certificate(rcs: &[RClause], nfs: &Nfs, st: &State, debug: bool) -> bool {
    let mut budget: u64 = 200_000_000;
    cert_round(
        rcs,
        &nfs.concept_names,
        &st.sub_super,
        &st.edges,
        None,
        &mut budget,
        None,
        debug,
        None,
    )
}

/// Completeness certificate by MODEL REPAIR (pay-as-you-go upper bound).
///
/// The plain certificate needs the canonical model of the EL subset to already
/// satisfy every residual clause; a live covering disjunction `⊤ ⊑ A ⊔ B`
/// always defeats it. Repair closes that gap soundly:
///
/// For each choice policy (first / last addable head atom), fork the saturated
/// structure and loop: enumerate the violated residual instances; for each,
/// make the chosen head atom true (a concept membership or a role edge);
/// re-run the EL completion to fixpoint; recheck. If the loop empties, the
/// result is a genuine model `I_p ⊨ O` of the FULL ontology in which every
/// base-derived fact still holds (repair only adds). Such a model is an UPPER
/// bound: `D ∉ label_p(x_C)` refutes `C ⊑ D`. The base saturation is the
/// LOWER bound (sound derivations). The certificate passes iff on every
/// named, base-satisfiable node the intersection of the pass labels — over
/// the passes where the node stays satisfiable; at least one is required as
/// that node's satisfiability witness — adds NO named concept over the base.
/// Then lower bound = truth = upper bound and the EL answer is exact, for
/// subsumptions, unsatisfiable classes, and consistency alike. Any other
/// outcome fails conservatively (context-engine fallback). Never an
/// approximation.
/// Union-find representative with path halving.
fn uf_find(repr: &mut [u32], mut x: u32) -> u32 {
    while repr[x as usize] != x {
        let p = repr[x as usize];
        repr[x as usize] = repr[p as usize];
        x = repr[x as usize];
    }
    x
}

/// Merge node `y` into node `x` in a repair-pass model: a violated all-eq
/// head (an at-most restriction) forces the two bound elements to coincide.
/// Memberships and outgoing edges of `y` move to the representative through
/// the State API (so the EL closure re-runs over them), incoming edges are
/// redirected via the reverse index, and `y` becomes a mirror of the
/// representative (re-synced after each closure round) so every concept's
/// canonical witness stays present in the domain.
fn merge_nodes(st: &mut State, repr: &mut [u32], merged: &mut Vec<u32>, x: u32, y: u32) {
    let a = uf_find(repr, x);
    let b = uf_find(repr, y);
    if a == b {
        return;
    }
    repr[b as usize] = a;
    merged.push(b);
    let subs: Vec<u32> = st.sub_super[b as usize].iter().copied().collect();
    for s in subs {
        st.add_sub(a, s);
    }
    let outs: Vec<(u32, u32)> = st.edges[b as usize].iter().copied().collect();
    for (r, d) in outs {
        st.add_edge(a, r, d);
    }
    let roles: Vec<u32> = std::mem::take(&mut st.in_roles[b as usize]);
    for r in roles {
        let Some(srcs) = st.in_by_role.remove(&(b, r)) else {
            continue;
        };
        for src in srcs {
            if st.edges[src as usize].remove(&(r, b)) {
                st.edge_epoch += 1;
            }
            st.add_edge(src, r, a);
        }
    }
}

/// Attribute a local contradiction to the repair choice that caused it: the
/// direct choice that put a body concept at the conflicting node, else the
/// most recent unbanned choice at a node this clause instance mentions, else
/// the most recent unbanned choice anywhere (chronological backtracking).
///
/// `None` means no choice was made at all, so the contradiction is entailed by
/// the base model and the certificate must fail rather than restart.
fn blame_choice(
    rc: &RClause,
    asg: &[u32],
    repr: &mut [u32],
    prov: &HashMap<(u32, u32), usize>,
    chrono: &[(u32, usize, u32)],
    banned: &HashSet<(u32, usize, u32)>,
) -> Option<(u32, usize, u32)> {
    for a in &rc.body {
        if let RAtom::C { cid, v } = *a {
            let nd = uf_find(repr, asg[v]);
            if let Some(&src) = prov.get(&(nd, cid)) {
                if !banned.contains(&(nd, src, cid)) {
                    return Some((nd, src, cid));
                }
            }
        }
    }
    let mut conf_nodes: Vec<u32> = Vec::new();
    for a in &rc.body {
        if let RAtom::C { v, .. } | RAtom::R { s: v, .. } = *a {
            conf_nodes.push(uf_find(repr, asg[v]));
        }
    }
    chrono
        .iter()
        .rev()
        .find(|t| conf_nodes.contains(&uf_find(repr, t.0)) && !banned.contains(*t))
        .copied()
        .or_else(|| chrono.iter().rev().find(|t| !banned.contains(*t)).copied())
}

/// Certificate verdict: `Pass` answers everything; `Partial(subjects)`
/// answers every named subject EXCEPT the listed ones (their truth could not
/// be pinned between the EL lower bound and the model upper bounds — the
/// caller resolves exactly those with the context engine); `Fail` answers
/// nothing.
pub enum CertOutcome {
    Pass,
    Partial(Vec<u32>),
    Fail,
}

fn repair_certify(
    rcs: &[RClause],
    nfs: &Nfs,
    idx: &Idx,
    base: &State,
    it: &Interner,
    debug: bool,
) -> CertOutcome {
    const MAX_ROUNDS: usize = 64;
    let n = base.sub_super.len();
    let mut is_named = vec![false; n];
    for &c in &nfs.concept_names {
        if c != TOP && c != BOTTOM && !crate::calc::is_internal_concept(it.name(c)) {
            is_named[c as usize] = true;
        }
    }
    // disjointness pairs (NF2 with a ⊥ head), for greedy choice avoidance:
    // when repairing a covering disjunction at a node, prefer a disjunct that
    // is not already disjoint with the node's labels
    let mut disj: HashMap<u32, HashSet<u32>> = HashMap::default();
    for f in &nfs.nf2 {
        if f.sup == BOTTOM {
            disj.entry(f.sub1).or_default().insert(f.sub2);
            disj.entry(f.sub2).or_default().insert(f.sub1);
        }
    }

    // qualified-cardinality guidance: which node pairs a `≥n` clause pins
    // apart, and which concepts activate a `≤n` bound when chosen
    let guide = CardGuide::new(rcs);
    if debug {
        eprintln!(
            "KM_ELC_CERT repair guidance: {} pinned witness pair(s), {} at-most bound(s), \
             {} partition-side concept(s){}",
            guide.pinned_apart.len(),
            guide.bounds.len(),
            guide.by_guard.len(),
            if guide.is_inert() {
                " (inert: choice order unchanged)"
            } else {
                ""
            },
        );
    }

    // base-satisfiable named nodes: a repair that drives one of these to ⊥
    // is a wrong choice (the criterion would fail), treated as a conflict
    let base_alive_named: Vec<u32> = (0..n as u32)
        .filter(|&c| is_named[c as usize] && !base.sub_super[c as usize].contains(&BOTTOM))
        .collect();

    enum PassOut {
        /// the base model already satisfies everything (plain certificate)
        Pristine,
        /// a complete pass model plus the provenance of its direct repair
        /// additions ((node, concept) -> choosing clause)
        Model(State, HashMap<(u32, u32), usize>),
        /// a ⊥-clause fired on a repair choice: ban that (node, clause,
        /// disjunct) triple and retry
        Conflict((u32, usize, u32)),
        Fail,
    }

    // One repair pass under a per-clause choice-polarity vector.  Choices are
    // greedy (skip disjuncts disjoint with the node's current labels) with
    // the polarity as the tie-break, and every direct concept addition is
    // recorded so a later ⊥-violation can be traced back to the choice that
    // caused it (conflict-driven restart).
    let run_pass = |polv: &[bool],
                    pass_label: usize,
                    banned: &HashSet<(u32, usize, u32)>,
                    tolerate_deaths: bool|
     -> PassOut {
        let mut st = base.fork();
        // Journal label additions and reuse one enumeration index for the whole
        // pass: every round would otherwise rescan the entire structure to
        // rebuild an index a round changes only marginally (see [`CertIdx`]).
        st.start_journal();
        let mut cidx = CertIdx::default();
        let mut budget: u64 = 400_000_000;
        let mut adds: u64 = 0;
        let mut repr: Vec<u32> = (0..n as u32).collect();
        let mut merged: Vec<u32> = Vec::new();
        let mut prov: HashMap<(u32, u32), usize> = HashMap::default();
        // chronological choice log (node, clause, disjunct) for blame when
        // the direct lookup misses (conflicting facts often arrive via the
        // closure, not directly)
        let mut chrono: Vec<(u32, usize, u32)> = Vec::new();
        // quotient-dependent half of the cardinality guidance, re-lifted to the
        // current union-find representatives at the head of every round and
        // after every merge inside one
        let mut cround = CardRound::default();
        for round in 1..=MAX_ROUNDS {
            let mut viols: Vec<(usize, Vec<u32>)> = Vec::new();
            let crep: Vec<u32> = (0..n as u32).map(|i| uf_find(&mut repr, i)).collect();
            cround.resync(&guide, &mut repr);
            let delta = st.drain_journal();
            let epoch = st.edge_epoch;
            let clean = cert_round(
                rcs,
                &nfs.concept_names,
                &st.sub_super,
                &st.edges,
                Some(&crep),
                &mut budget,
                Some(&mut viols),
                false,
                Some(CertReuse {
                    idx: &mut cidx,
                    delta: delta.as_deref(),
                    edge_epoch: epoch,
                }),
            );
            if clean {
                if adds == 0 {
                    return PassOut::Pristine;
                }
                if debug {
                    eprintln!(
                        "KM_ELC_CERT repair pass {pass_label}: model complete after {} rounds, \
                         {adds} additions (budget_left={budget})",
                        round - 1
                    );
                }
                return PassOut::Model(st, prov);
            }
            if viols.is_empty() {
                if debug {
                    eprintln!(
                        "KM_ELC_CERT repair pass {pass_label}: budget exhausted (round {round})"
                    );
                }
                return PassOut::Fail;
            }
            // `cert_round` reports violations against the state at the start
            // of this repair round. Process forced (single addable-head)
            // consequences before genuine choices, and recheck each reported
            // head against the incrementally repaired state. Otherwise a
            // singleton consequence can make a previously reported covering
            // disjunction true, yet the stale report still adds its opposite
            // disjunct and manufactures an avoidable clash. This changes only
            // model-search order: every accepted model is still closed under
            // EL and checked against every residual clause below.
            viols.sort_by_key(|(rci, _)| {
                rcs[*rci]
                    .head
                    .iter()
                    .filter(|atom| !matches!(atom, RAtom::Eq { .. }))
                    .count()
            });
            for (rci, asg) in &viols {
                let head = &rcs[*rci].head;
                let already_satisfied = head.iter().any(|atom| match *atom {
                    RAtom::C { cid, v } => {
                        let nd = uf_find(&mut repr, asg[v]);
                        st.sub_super[nd as usize].contains(&cid)
                    }
                    RAtom::R { rid, s, t } => {
                        let sn = uf_find(&mut repr, asg[s]);
                        let tn = uf_find(&mut repr, asg[t]);
                        st.edges[sn as usize].contains(&(rid, tn))
                    }
                    RAtom::Eq { s, t } => uf_find(&mut repr, asg[s]) == uf_find(&mut repr, asg[t]),
                });
                if already_satisfied {
                    continue;
                }
                // addable candidates in this clause's preference order
                let cands: Vec<&RAtom> = if polv[*rci] {
                    head.iter()
                        .rev()
                        .filter(|a| !matches!(a, RAtom::Eq { .. }))
                        .collect()
                } else {
                    head.iter()
                        .filter(|a| !matches!(a, RAtom::Eq { .. }))
                        .collect()
                };
                // Choice tiers, most constrained first, scanned in the
                // polarity order so the two seed passes still diverge:
                //   0  unbanned, not disjoint with the node's labels, and not
                //      made locally unsatisfiable by a qualified at-most bound;
                //   1  unbanned and not disjoint with the node's labels;
                //   2  unbanned;
                //   3  anything.
                // Tiers 1-3 are the previous behaviour. Tier 0 coincides with
                // tier 1 whenever the residual holds no cardinality partition,
                // so ontologies without one search exactly as before.
                let mut pick: Option<&RAtom> = None;
                for tier in 0..4u8 {
                    for a in &cands {
                        let ok = match **a {
                            RAtom::C { cid, v } => {
                                let nd = uf_find(&mut repr, asg[v]);
                                let unbanned = !banned.contains(&(nd, *rci, cid));
                                let free = || {
                                    !disj.get(&cid).is_some_and(|ds| {
                                        ds.iter().any(|d| st.sub_super[nd as usize].contains(d))
                                    })
                                };
                                match tier {
                                    0 => {
                                        unbanned
                                            && free()
                                            && !guide.locally_incompatible(
                                                &mut cround,
                                                &st,
                                                &mut repr,
                                                nd,
                                                cid,
                                            )
                                    }
                                    1 => unbanned && free(),
                                    2 => unbanned,
                                    _ => true,
                                }
                            }
                            _ => true,
                        };
                        if ok {
                            pick = Some(*a);
                            break;
                        }
                    }
                    if pick.is_some() {
                        break;
                    }
                }
                match pick {
                    Some(&RAtom::C { cid, v }) => {
                        let nd = uf_find(&mut repr, asg[v]);
                        st.add_sub(nd, cid);
                        prov.entry((nd, cid)).or_insert(*rci);
                        chrono.push((nd, *rci, cid));
                    }
                    Some(&RAtom::R { rid, s, t }) => {
                        let sn = uf_find(&mut repr, asg[s]);
                        let tn = uf_find(&mut repr, asg[t]);
                        st.add_edge(sn, rid, tn);
                    }
                    Some(&RAtom::Eq { .. }) => unreachable!("eq filtered from cands"),
                    None => {
                        // Every head atom is an equality: a qualified at-most
                        // bound bit at this node and one of the enumerated
                        // pairs has to be identified. Choose a pair the model
                        // may actually identify, preferring one that does not
                        // immediately clash. Merging a pinned pair instead
                        // makes the pinning clause false wherever its guard
                        // holds, and the resulting ⊥ surfaces rounds later
                        // with the blame out of reach of the choice at fault.
                        let mut merged_now = false;
                        let mut already = false;
                        for prefer_clean in [true, false] {
                            for a in head {
                                let RAtom::Eq { s, t } = *a else { continue };
                                let (u, w) = (asg[s], asg[t]);
                                // an earlier merge in THIS round may already
                                // have unified the pair (violations were
                                // enumerated against the round-start state)
                                if uf_find(&mut repr, u) == uf_find(&mut repr, w) {
                                    already = true;
                                    break;
                                }
                                if !guide.merge_legal(&cround, &mut repr, u, w) {
                                    continue;
                                }
                                if prefer_clean && guide.merge_clashes(&st, &disj, &mut repr, u, w)
                                {
                                    continue;
                                }
                                merge_nodes(&mut st, &mut repr, &mut merged, u, w);
                                cround.resync(&guide, &mut repr);
                                merged_now = true;
                                break;
                            }
                            if already || merged_now {
                                break;
                            }
                        }
                        if already {
                            continue;
                        }
                        if !merged_now {
                            // Either the clause has no head at all, or every
                            // identification it offers is pinned apart. Both
                            // are local contradictions: charge the choice that
                            // produced them and restart.
                            let empty_head = head.is_empty();
                            match blame_choice(&rcs[*rci], asg, &mut repr, &prov, &chrono, banned) {
                                Some(triple) => {
                                    if debug {
                                        let why = if empty_head {
                                            "violated ⊥-clause"
                                        } else {
                                            "at-most bound with every pair pinned apart"
                                        };
                                        eprintln!(
                                            "KM_ELC_CERT repair pass {pass_label}: clause \
                                             {rci} conflict ({why}), banning choice {:?} \
                                             (node={}, concept={})",
                                            triple,
                                            it.name(triple.0),
                                            it.name(triple.2),
                                        );
                                    }
                                    return PassOut::Conflict(triple);
                                }
                                None => {
                                    if debug {
                                        let why = if empty_head {
                                            "empty head"
                                        } else {
                                            "at-most bound with every pair pinned apart"
                                        };
                                        eprintln!(
                                            "KM_ELC_CERT repair pass {pass_label}: clause \
                                             {rci} violated ({why}, no choices made \
                                             — genuine inconsistency)"
                                        );
                                    }
                                    return PassOut::Fail;
                                }
                            }
                        }
                    }
                }
                adds += 1;
            }
            if debug {
                eprintln!(
                    "KM_ELC_CERT repair pass {pass_label} round {round}: \
                     violations={} adds={adds} merges={} card_demoted={}",
                    viols.len(),
                    merged.len(),
                    cround.demoted,
                );
            }
            // Re-close under the EL rules: the repaired structure must again
            // be a model of the EL clause set before the next recheck.
            run(idx, &mut st, &mut Prof::default());
            // Re-sync merged ids as mirrors of their (closed) representative,
            // so every concept's canonical witness remains in the domain with
            // exactly the representative's labels and edges.
            for &b in &merged {
                let a = uf_find(&mut repr, b);
                if a != b {
                    // The re-sync itself is unchanged; what is added is the
                    // record of whether it actually moved the mirror. An
                    // assignment that reproduces the sequence the mirror already
                    // iterates leaves both certificate indexes exactly as they
                    // were, and so is not reported.
                    let subs_moved = !st.sub_super[b as usize]
                        .iter()
                        .eq(st.sub_super[a as usize].iter());
                    if subs_moved
                        && st.sub_super[b as usize]
                            .iter()
                            .any(|s| !st.sub_super[a as usize].contains(s))
                    {
                        // The mirror only ever GAINS labels: `merge_nodes` folds
                        // b's label into a's, b keeps no backward links, and
                        // every rule that fires on b fires on a over the mirrored
                        // edges, so at fixpoint label(b) ⊆ label(a). Were that
                        // ever to fail, this assignment would also delete from
                        // the mirror — which an addition journal cannot express —
                        // so drop the index and rebuild instead of patching it.
                        cidx.invalidate();
                    }
                    st.sub_super[b as usize] = st.sub_super[a as usize].clone();
                    if subs_moved {
                        let State {
                            sub_super,
                            sub_journal,
                            ..
                        } = &mut st;
                        if let Some(j) = sub_journal.as_mut() {
                            for &s in &sub_super[b as usize] {
                                j.push((b, s));
                            }
                        }
                    }
                    let edges_moved = !st.edges[b as usize].iter().eq(st.edges[a as usize].iter());
                    st.edges[b as usize] = st.edges[a as usize].clone();
                    if edges_moved {
                        st.edge_epoch += 1;
                    }
                }
            }
            // a repair choice cascaded a base-satisfiable named witness to ⊥:
            // the killing choice was made at SOME newly-⊥ node (the cascade
            // travels the closure, e.g. a poisoned existential filler kills
            // its sources) — blame the most recent unbanned choice at any
            // newly-dead node, else at the witness itself, else anywhere
            for &c in &base_alive_named {
                if tolerate_deaths {
                    break;
                }
                let cr = uf_find(&mut repr, c);
                if st.sub_super[cr as usize].contains(&BOTTOM) {
                    let blame = chrono
                        .iter()
                        .rev()
                        .find(|t| {
                            !banned.contains(*t) && {
                                let nd = uf_find(&mut repr, t.0);
                                st.sub_super[nd as usize].contains(&BOTTOM)
                                    && !base.sub_super[nd as usize].contains(&BOTTOM)
                            }
                        })
                        .copied()
                        .or_else(|| {
                            chrono
                                .iter()
                                .rev()
                                .find(|t| uf_find(&mut repr, t.0) == cr && !banned.contains(*t))
                                .copied()
                        })
                        .or_else(|| chrono.iter().rev().find(|t| !banned.contains(*t)).copied());
                    match blame {
                        Some(triple) => {
                            if debug {
                                eprintln!(
                                    "KM_ELC_CERT repair pass {pass_label}: witness {} died, \
                                     banning choice {:?} (node={}, concept={})",
                                    c,
                                    triple,
                                    it.name(triple.0),
                                    it.name(triple.2),
                                );
                            }
                            return PassOut::Conflict(triple);
                        }
                        None => {
                            if debug {
                                eprintln!(
                                    "KM_ELC_CERT repair pass {pass_label}: witness {} died \
                                     with no choices made (genuinely unsatisfiable?)",
                                    c
                                );
                            }
                            return PassOut::Fail;
                        }
                    }
                }
            }
        }
        if debug {
            eprintln!(
                "KM_ELC_CERT repair pass {pass_label}: no convergence in {MAX_ROUNDS} rounds"
            );
        }
        PassOut::Fail
    };

    const RESTART_CAP: usize = REPAIR_RESTART_CAP;
    let mut pass_states: Vec<(State, HashMap<(u32, u32), usize>)> = Vec::new();
    let polv0 = vec![false; rcs.len()];
    let mut banned0: HashSet<(u32, usize, u32)> = HashSet::default();
    for seed in 0..2usize {
        let polv = vec![seed == 1; rcs.len()];
        let mut banned: HashSet<(u32, usize, u32)> = HashSet::default();
        let mut restarts = 0usize;
        let mut got_model = false;
        loop {
            match run_pass(&polv, seed, &banned, false) {
                PassOut::Pristine => {
                    if debug {
                        eprintln!("KM_ELC_CERT repair: base model already complete");
                    }
                    return CertOutcome::Pass;
                }
                PassOut::Model(st, prov) => {
                    if seed == 0 {
                        banned0 = banned.clone();
                    }
                    pass_states.push((st, prov));
                    got_model = true;
                    break;
                }
                PassOut::Conflict(triple) => {
                    if restarts >= RESTART_CAP || !banned.insert(triple) {
                        if debug {
                            eprintln!(
                                "KM_ELC_CERT repair pass {seed}: conflicts persist after \
                                 {restarts} restarts"
                            );
                        }
                        break;
                    }
                    restarts += 1;
                }
                PassOut::Fail => break,
            }
        }
        if !got_model {
            // strict passes kept dying: accept a model that lets witnesses
            // die — their subjects become unresolved residue for the engine
            if let PassOut::Model(st, prov) = run_pass(&polv, seed + 10, &banned, true) {
                if debug {
                    eprintln!("KM_ELC_CERT repair pass {seed}: death-tolerant model accepted");
                }
                if seed == 0 {
                    banned0 = banned.clone();
                }
                pass_states.push((st, prov));
            }
        }
    }
    if pass_states.is_empty() {
        return CertOutcome::Fail;
    }
    // Per-subject intersection criterion with refinement.  Subjects whose
    // truth cannot be pinned (unsat in every surviving model, or with
    // undetermined extra supers after the refinement passes) become the
    // unresolved residue; everything else is answered exactly.
    const REFINE_CAP: usize = 8;
    let mut refine = 0usize;
    loop {
        let mut unsat_subjects: Vec<u32> = Vec::new();
        let mut undet: Vec<(u32, u32)> = Vec::new();
        for c in 0..n {
            if !is_named[c] || base.sub_super[c].contains(&BOTTOM) {
                continue;
            }
            let mut inter: Option<HashSet<u32>> = None;
            for (st, _) in &pass_states {
                if st.sub_super[c].contains(&BOTTOM) {
                    continue;
                }
                let extras: HashSet<u32> = st.sub_super[c]
                    .iter()
                    .copied()
                    .filter(|&d| is_named[d as usize] && !base.sub_super[c].contains(&d))
                    .collect();
                inter = Some(match inter {
                    None => extras,
                    Some(prev) => prev.intersection(&extras).copied().collect(),
                });
                if inter.as_ref().is_some_and(|s| s.is_empty()) {
                    break;
                }
            }
            match inter {
                None => unsat_subjects.push(c as u32),
                Some(set) => {
                    for d in set {
                        undet.push((c as u32, d));
                    }
                }
            }
        }
        if undet.is_empty() || refine >= REFINE_CAP {
            let mut unresolved: Vec<u32> = unsat_subjects;
            unresolved.extend(undet.iter().map(|p| p.0));
            unresolved.sort_unstable();
            unresolved.dedup();
            if unresolved.is_empty() {
                if debug {
                    eprintln!(
                        "KM_ELC_CERT repair pass: {} model(s) agree with the EL lower bound",
                        pass_states.len()
                    );
                }
                return CertOutcome::Pass;
            }
            let cap: usize = std::env::var("KM_ELC_RESIDUE_CAP")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(64);
            if unresolved.len() <= cap {
                if debug {
                    eprintln!(
                        "KM_ELC_CERT partial: {} unresolved subject(s) left for the \
                         context engine",
                        unresolved.len()
                    );
                }
                return CertOutcome::Partial(unresolved);
            }
            if debug {
                eprintln!(
                    "KM_ELC_CERT repair fail: {} unresolved subjects exceed the residue cap",
                    unresolved.len()
                );
            }
            return CertOutcome::Fail;
        }
        // refinement: ban the choices behind the undetermined pairs and run
        // one more targeted pass; dead ends just finalize with the residue
        refine += 1;
        let mut new_bans = 0usize;
        for &(nd, a) in &undet {
            for (_, prov) in &pass_states {
                if let Some(&rci) = prov.get(&(nd, a)) {
                    if banned0.insert((nd, rci, a)) {
                        new_bans += 1;
                    }
                }
            }
        }
        if new_bans == 0 {
            refine = REFINE_CAP;
            continue;
        }
        let mut restarts = 0usize;
        loop {
            match run_pass(&polv0, 20 + refine, &banned0, true) {
                PassOut::Pristine => return CertOutcome::Pass,
                PassOut::Model(st, prov) => {
                    pass_states.push((st, prov));
                    break;
                }
                PassOut::Conflict(triple) => {
                    if restarts >= RESTART_CAP || !banned0.insert(triple) {
                        refine = REFINE_CAP;
                        break;
                    }
                    restarts += 1;
                }
                PassOut::Fail => {
                    refine = REFINE_CAP;
                    break;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// The engine-shaped classification result (mirrors `el_route.classify`'s dict).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ElResult {
    /// named subjects the certificate could NOT determine (nonempty only in
    /// repair mode): the caller must classify exactly these with the context
    /// engine and merge; every other subject's answer is exact.
    pub unresolved: Vec<String>,
    /// `concept -> [super-concepts]` (full internal names; `owl:Nothing` for ⊥).
    pub subsumptions: std::collections::BTreeMap<String, Vec<String>>,
    pub inconsistent: bool,
}

/// Decide consistency of a positive ground ABox against a pure EL++ TBox.
///
/// Each equality class of named individuals becomes one fresh EL concept
/// node. Class assertions seed that node, and a ground role assertion becomes
/// an edge between the two corresponding nodes. EL completion is the canonical
/// ABox materialisation procedure for this fragment, so the ABox is
/// inconsistent exactly when the TBox is inconsistent, an equality contradicts
/// a `DifferentIndividuals` pair, or one fresh node derives `owl:Nothing`.
///
/// Returns `None` unless the frontend retained the whole ABox and the combined
/// clause set is pure EL++. Negative role assertions need closed-world edge
/// comparison and therefore decline here.
pub struct PositiveAboxResult {
    pub consistent: bool,
    /// Present when completion ran. An explicit identity contradiction proves
    /// inconsistency before saturation and therefore has no taxonomy to reuse.
    pub classification: Option<ElResult>,
}

/// Materialise a positive ground ABox and retain the exact EL taxonomy produced
/// by that same completion. Every injected rule is rooted at a fresh ABox-node
/// concept, and generated role edges connect only those fresh roots and their
/// fresh witnesses. No injected rule can therefore add a subsumption whose
/// subject is an original named class. Consequently the returned named-class
/// taxonomy is the ordinary TBox taxonomy as well as the consistency
/// certificate.
pub fn positive_abox_classify(
    mut clauses: Vec<JClause>,
    meta: &crate::json_io::NominalAboxMeta,
) -> Option<PositiveAboxResult> {
    let debug = std::env::var_os("KM_ELC_DEBUG").is_some();
    if !meta.complete || !meta.unsupported.is_empty() || !meta.negative_role_assertions.is_empty() {
        if debug {
            eprintln!(
                "KM_EL_ABOX defer: complete={} unsupported={} negative_roles={}",
                meta.complete,
                meta.unsupported.len(),
                meta.negative_role_assertions.len()
            );
        }
        return None;
    }

    let ids: std::collections::HashMap<&str, usize> = meta
        .individuals
        .iter()
        .enumerate()
        .map(|(i, entry)| (entry.individual.as_str(), i))
        .collect();
    // Every retained identity/role endpoint must have a corresponding typed
    // individual record. `complete` promises this; recheck at the consumer
    // boundary so malformed JSON fails closed.
    for (left, right) in meta.same.iter().chain(meta.different.iter()) {
        if !ids.contains_key(left.as_str()) || !ids.contains_key(right.as_str()) {
            if debug {
                eprintln!("KM_EL_ABOX defer: identity endpoint absent from typed individuals");
            }
            return None;
        }
    }
    for edge in &meta.role_assertions {
        if !ids.contains_key(edge.source.as_str()) || !ids.contains_key(edge.target.as_str()) {
            if debug {
                eprintln!("KM_EL_ABOX defer: role endpoint absent from typed individuals");
            }
            return None;
        }
    }

    let mut parent: Vec<usize> = (0..ids.len()).collect();
    fn find(parent: &mut [usize], mut node: usize) -> usize {
        let mut root = node;
        while parent[root] != root {
            root = parent[root];
        }
        while parent[node] != node {
            let next = parent[node];
            parent[node] = root;
            node = next;
        }
        root
    }
    for (left, right) in &meta.same {
        let l = find(&mut parent, ids[left.as_str()]);
        let r = find(&mut parent, ids[right.as_str()]);
        if l != r {
            parent[r] = l;
        }
    }
    for (left, right) in &meta.different {
        let l = find(&mut parent, ids[left.as_str()]);
        let r = find(&mut parent, ids[right.as_str()]);
        if l == r {
            return Some(PositiveAboxResult {
                consistent: false,
                classification: None,
            });
        }
    }

    let node = |root: usize| format!("__km_abox_node_{root}");
    let var = || JTerm::Var {
        name: "x".to_string(),
    };
    let concept = |name: String, term: JTerm| JAtom::Concept {
        concept: name,
        term,
    };

    for (index, entry) in meta.individuals.iter().enumerate() {
        if entry.assertions.len() != entry.assertion_markers.len() {
            if debug {
                eprintln!(
                    "KM_EL_ABOX defer: assertion marker mismatch individual={}",
                    entry.individual
                );
            }
            return None;
        }
        let root = find(&mut parent, index);
        for marker in &entry.assertion_markers {
            clauses.push(JClause {
                body: vec![concept(node(root), var())],
                head: vec![concept(marker.clone(), var())],
            });
        }
    }
    for (edge_index, edge) in meta.role_assertions.iter().enumerate() {
        let source = find(&mut parent, ids[edge.source.as_str()]);
        let target = find(&mut parent, ids[edge.target.as_str()]);
        let fun = JTerm::Fun {
            function: format!("__km_abox_edge_{edge_index}"),
            arg: Box::new(var()),
        };
        clauses.push(JClause {
            body: vec![concept(node(source), var())],
            head: vec![JAtom::Role {
                role: edge.role.clone(),
                source: var(),
                target: fun.clone(),
            }],
        });
        clauses.push(JClause {
            body: vec![concept(node(source), var())],
            head: vec![concept(node(target), fun)],
        });
    }
    // Keep identity-only representatives in the completion signature.
    for index in 0..parent.len() {
        let root = find(&mut parent, index);
        clauses.push(JClause {
            body: vec![concept(node(root), var())],
            head: vec![concept(node(root), var())],
        });
    }

    let roots: std::collections::HashSet<String> = (0..parent.len())
        .map(|i| node(find(&mut parent, i)))
        .collect();
    let result = match classify(clauses) {
        Some(result) => result,
        None => {
            if debug {
                eprintln!("KM_EL_ABOX defer: augmented clause set is not pure EL++");
            }
            return None;
        }
    };
    let node_unsat = roots.iter().any(|root| {
        result
            .subsumptions
            .get(root)
            .is_some_and(|supers| supers.iter().any(|sup| sup == "owl:Nothing"))
    });
    Some(PositiveAboxResult {
        consistent: !result.inconsistent && !node_unsat,
        classification: Some(result),
    })
}

pub fn positive_abox_consistent(
    clauses: Vec<JClause>,
    meta: &crate::json_io::NominalAboxMeta,
) -> Option<bool> {
    // Preserve the historical consistency-only API for callers and tests that
    // do not need to retain the already-computed taxonomy.
    positive_abox_classify(clauses, meta).map(|result| result.consistent)
}

/// Classify `clauses` with EL++ completion. Returns `Some(result)` when the
/// clause set lies in EL++, or when the non-EL residual passes the
/// canonical-model completeness certificate (the result is then exact for the
/// FULL clause set). Returns `None` otherwise (caller must use the disjunctive
/// context engine). `KM_ELC_CERT=0` disables the certificate (old behaviour:
/// any non-EL clause routes to the context engine); `KM_ELC_DEBUG=1` reports
/// residual counts and the certificate verdict on stderr.
/// Certificate mode, from `KM_ELC_CERT`: unset/`0` = off, `1`/`on` = plain
/// canonical-model check, `2`/`repair` = model repair with intersection.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CertMode {
    Off,
    Check,
    Repair,
}

/// Why an ontology or update cannot be handled by the incremental EL++
/// classifier.
///
/// Incremental reasoning deliberately has a narrower contract than
/// [`classify`]: every accepted clause must map directly to an EL++ normal
/// form. Certificate-assisted residual clauses are not accepted because a
/// later addition can invalidate a previously passing model certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IncrementalError {
    /// At least one clause was recognised but lies outside EL++.
    NonElResidual { clauses: usize },
    /// The clause set contains a shape that cannot be assembled into an EL++
    /// normal form, such as an existential filler half with no role half.
    UnsupportedNormalForm,
}

impl std::fmt::Display for IncrementalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IncrementalError::NonElResidual { clauses } => write!(
                f,
                "incremental EL++ mode rejected {clauses} non-EL clause(s)"
            ),
            IncrementalError::UnsupportedNormalForm => write!(
                f,
                "incremental EL++ mode could not assemble every clause into a supported normal form"
            ),
        }
    }
}

impl std::error::Error for IncrementalError {}

/// Statistics for one accepted addition transaction.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct IncrementalUpdate {
    /// Monotonically increasing transaction revision. The initial snapshot is
    /// revision 0; each nonempty accepted addition advances it once.
    pub revision: u64,
    pub added_clauses: usize,
    pub total_clauses: usize,
    /// False only when adding a Skolem filler half rewrites a previously
    /// assembled existential normal form, forcing a safe fresh completion.
    pub reused_fixpoint: bool,
    /// Facts retained from the preceding fixpoint and replayed against the
    /// enlarged rule indexes.
    pub reused_subsumptions: usize,
    pub reused_edges: usize,
    /// Closure facts derived beyond the retained state. When
    /// `reused_fixpoint` is false these counts describe the whole fresh state.
    pub new_subsumptions: usize,
    pub new_edges: usize,
}

/// Addition-only incremental EL++ classification.
///
/// The classifier keeps the completed relation and role graph across updates.
/// An update is a transaction containing normalised [`JClause`] values. KM
/// reparses the union only to rebuild compact rule indexes, then replays the
/// old fixpoint and saturates newly enabled consequences. Since OWL entailment
/// and every EL++ completion rule are monotone under axiom addition, all reused
/// facts remain entailed and the resulting fixpoint equals a fresh completion
/// of the union. If a new Skolem filler half rewrites a previously assembled
/// existential normal form, KM detects the non-monotone compact translation and
/// completes that transaction afresh.
///
/// Updates are atomic: an unsupported transaction returns an error without
/// changing the clauses, revision, or completed state. Retraction is not
/// exposed. Callers that need removal must build a new classifier from the new
/// ontology snapshot.
pub struct IncrementalElClassifier {
    clauses: Vec<JClause>,
    interner: Interner,
    concept_ids: HashSet<u32>,
    normal_forms: HashSet<NormalFormKey>,
    state: State,
    revision: u64,
}

impl IncrementalElClassifier {
    /// Complete an initial, pure-EL++ clause snapshot.
    pub fn new(clauses: Vec<JClause>) -> Result<Self, IncrementalError> {
        let mut interner = Interner::new();
        let (nfs, residual, _) =
            to_nf(&clauses, &mut interner).ok_or(IncrementalError::UnsupportedNormalForm)?;
        if !residual.is_empty() {
            return Err(IncrementalError::NonElResidual {
                clauses: residual.len(),
            });
        }

        let idx = build_idx(&nfs, interner.len());
        let mut state = init_state(&nfs, interner.len());
        seed_reflexive_edges(&nfs, &idx, &mut state);
        run(&idx, &mut state, &mut Prof::default());
        let normal_forms = normal_form_keys(&nfs);
        let concept_ids = nfs.concept_names;

        Ok(IncrementalElClassifier {
            clauses,
            interner,
            concept_ids,
            normal_forms,
            state,
            revision: 0,
        })
    }

    /// Add a transaction of normalised clauses and complete only the enlarged
    /// closure. An empty transaction is a no-op and does not advance revision.
    pub fn add_clauses(
        &mut self,
        additions: Vec<JClause>,
    ) -> Result<IncrementalUpdate, IncrementalError> {
        let added_clauses = additions.len();
        let reused_subsumptions = fact_count(&self.state.sub_super);
        let reused_edges = fact_count(&self.state.edges);
        if additions.is_empty() {
            return Ok(IncrementalUpdate {
                revision: self.revision,
                added_clauses: 0,
                total_clauses: self.clauses.len(),
                reused_fixpoint: true,
                reused_subsumptions,
                reused_edges,
                new_subsumptions: 0,
                new_edges: 0,
            });
        }

        // Parse into a cloned interner so a rejected transaction cannot leak
        // new symbol ids into the live session. Existing ids remain stable;
        // `to_nf` only appends ids for symbols introduced by the addition.
        let old_clause_count = self.clauses.len();
        self.clauses.extend(additions);
        let mut next_interner = self.interner.clone();
        let parsed = to_nf(&self.clauses, &mut next_interner);
        let (next_nfs, residual, _) = match parsed {
            Some(parts) => parts,
            None => {
                self.clauses.truncate(old_clause_count);
                return Err(IncrementalError::UnsupportedNormalForm);
            }
        };
        if !residual.is_empty() {
            let clauses = residual.len();
            self.clauses.truncate(old_clause_count);
            return Err(IncrementalError::NonElResidual { clauses });
        }

        let next_normal_forms = normal_form_keys(&next_nfs);
        let can_reuse_fixpoint = self.normal_forms.is_subset(&next_normal_forms);
        if !can_reuse_fixpoint {
            // Completing a previously one-sided existential can replace
            // A⊑∃R.⊤ with A⊑∃R.B in the NF view. The source clause union is
            // monotone, but that compact rule translation is not. Retaining
            // the old canonical TOP edge could enable spurious role-chain
            // joins, so restart this rare transaction from Init.
            let next_idx = build_idx(&next_nfs, next_interner.len());
            let mut next_state = init_state(&next_nfs, next_interner.len());
            seed_reflexive_edges(&next_nfs, &next_idx, &mut next_state);
            run(&next_idx, &mut next_state, &mut Prof::default());
            let new_subsumptions = fact_count(&next_state.sub_super);
            let new_edges = fact_count(&next_state.edges);
            self.interner = next_interner;
            self.concept_ids = next_nfs.concept_names;
            self.normal_forms = next_normal_forms;
            self.state = next_state;
            self.revision += 1;
            return Ok(IncrementalUpdate {
                revision: self.revision,
                added_clauses,
                total_clauses: self.clauses.len(),
                reused_fixpoint: false,
                reused_subsumptions: 0,
                reused_edges: 0,
                new_subsumptions,
                new_edges,
            });
        }

        // Preserve every fact from the old fixpoint. Arrays grow only because
        // additions may introduce symbols; existing dense ids never move.
        let next_len = next_interner.len();
        self.state.sub_super.resize_with(next_len, HashSet::default);
        self.state.edges.resize_with(next_len, HashSet::default);
        // `in_by_role` is a sparse global map keyed by (target, role): retained
        // entries stay valid under new symbols and need no resizing.
        self.state.in_roles.resize_with(next_len, Vec::new);

        // PROP is a derived join index, not an entailment. Rebuild it by
        // replaying every retained subsumption under the new NF4 index. Replay
        // all retained edges as well, which activates new role inclusions and
        // chains. This is seminaive at transaction granularity: old closure
        // facts are retained, while only newly enabled add_sub/add_edge calls
        // enter the normal worklist recursively.
        self.state.prop.clear();
        let mut replay = VecDeque::new();
        for (c, supers) in self.state.sub_super.iter().enumerate() {
            for &d in supers {
                replay.push_back(Item::Sub(c as u32, d));
            }
        }
        for (c, edges) in self.state.edges.iter().enumerate() {
            for &(r, d) in edges {
                replay.push_back(Item::Edge(c as u32, r, d));
            }
        }
        self.state.worklist = replay;

        let next_idx = build_idx(&next_nfs, next_len);
        // Init and newly reflexive roles can add facts that did not exist in
        // the retained closure. Duplicate facts are filtered by State.
        for &c in &next_nfs.concept_names {
            if c != BOTTOM {
                self.state.add_sub(c, c);
                self.state.add_sub(c, TOP);
            }
        }
        seed_reflexive_edges(&next_nfs, &next_idx, &mut self.state);
        run(&next_idx, &mut self.state, &mut Prof::default());

        self.interner = next_interner;
        self.concept_ids = next_nfs.concept_names;
        self.normal_forms = next_normal_forms;
        self.revision += 1;

        let final_subsumptions = fact_count(&self.state.sub_super);
        let final_edges = fact_count(&self.state.edges);
        Ok(IncrementalUpdate {
            revision: self.revision,
            added_clauses,
            total_clauses: self.clauses.len(),
            reused_fixpoint: true,
            reused_subsumptions,
            reused_edges,
            new_subsumptions: final_subsumptions.saturating_sub(reused_subsumptions),
            new_edges: final_edges.saturating_sub(reused_edges),
        })
    }

    /// Materialise the current classification without consuming the session.
    pub fn result(&self) -> ElResult {
        let mut subsumptions = std::collections::BTreeMap::new();
        for c in 0..self.state.sub_super.len() {
            let cid = c as u32;
            if cid == TOP || cid == BOTTOM || !self.concept_ids.contains(&cid) {
                continue;
            }
            let mut out: Vec<String> = self.state.sub_super[c]
                .iter()
                .filter_map(|&d| {
                    if d == cid || d == TOP {
                        None
                    } else if d == BOTTOM {
                        Some("owl:Nothing".to_string())
                    } else {
                        Some(self.interner.name(d).to_string())
                    }
                })
                .collect();
            out.sort_unstable();
            if !out.is_empty() {
                subsumptions.insert(self.interner.name(cid).to_string(), out);
            }
        }
        ElResult {
            unresolved: Vec::new(),
            subsumptions,
            inconsistent: self.is_inconsistent(),
        }
    }

    /// Query a named-class subsumption. `None` means the subject is not in the
    /// current concept signature; it does not mean false.
    pub fn is_subsumed_by(&self, sub: &str, sup: &str) -> Option<bool> {
        let sub_id = self.interner.id(sub)?;
        if !self.concept_ids.contains(&sub_id) {
            return None;
        }
        if self.is_inconsistent() {
            return Some(true);
        }
        if sub == sup || sup == "owl:Thing" || sup == "\u{22a4}" {
            return Some(true);
        }
        let sup_id = if sup == "owl:Nothing" || sup == "\u{22a5}" {
            BOTTOM
        } else {
            match self.interner.id(sup) {
                Some(id) if self.concept_ids.contains(&id) => id,
                _ => return Some(false),
            }
        };
        Some(self.state.sub_super[sub_id as usize].contains(&sup_id))
    }

    pub fn is_inconsistent(&self) -> bool {
        self.state.sub_super[TOP as usize].contains(&BOTTOM)
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }
}

fn fact_count<T>(sets: &[HashSet<T>]) -> usize {
    sets.iter().map(HashSet::len).sum()
}

fn seed_reflexive_edges(nfs: &Nfs, idx: &Idx, state: &mut State) {
    if idx.reflexive_closed.is_empty() {
        return;
    }
    for &c in &nfs.concept_names {
        if c == BOTTOM {
            continue;
        }
        for &r in &idx.reflexive_closed {
            state.add_edge(c, r, c);
        }
    }
}

pub fn classify(clauses: Vec<JClause>) -> Option<ElResult> {
    // Default OFF: on the ORE 2015 corpus every non-EL residual is a live
    // covering disjunction / non-inert inverse bridge / multi-successor
    // functionality, none of which the canonical EL model satisfies, so the
    // PLAIN certificate never passes there -- and attempting it would saturate
    // the (large) EL subset before failing, stealing time from the CB
    // fallback. `KM_ELC_CERT=1` enables the plain check (near-EL ontologies
    // whose non-EL part IS model-satisfiable); `KM_ELC_CERT=2` additionally
    // repairs violated residuals by disjunct choice and certifies via the
    // intersection of the choice-pass models.
    let cert = match std::env::var("KM_ELC_CERT").as_deref() {
        Ok("1") | Ok("on") => CertMode::Check,
        Ok("2") | Ok("repair") => CertMode::Repair,
        _ => CertMode::Off,
    };
    let debug = std::env::var("KM_ELC_DEBUG").is_ok();
    classify_inner(clauses, cert, debug)
}

/// KM_ELC_HOIST (P1) — *semantic* common-disjunct extraction, the EL-side
/// counterpart of the frontend's syntactic `hoist_common_disjuncts`. After the
/// EL subset is saturated, a parked residual disjunction `D ⊑ A₁ ∨ … ∨ Aₙ` lets
/// us derive `D ⊑ X` for every `X` that subsumes all disjuncts in the *completed*
/// relation (`Aᵢ ⊑ X` ∈ `sub_super`, or `Aᵢ = X`) — the ⊔-distribution lemma
/// `A⊑X ∧ B⊑X ⟹ A⊔B⊑X`. This recovers subsumptions the EL completion dropped by
/// parking the disjunction, *without* expanding it. The completion saw only the
/// EL part, so this finds supers the frontend pass cannot (they require
/// EL-derived subsumptions). Sound by the lemma; it only adds entailed pairs, so
/// it can shrink the certificate's INSUFFICIENT residue but never make it unsound.
///
/// Handles disjunctions with an empty body (`⊤⊑…`, subject = ⊤) or a single
/// concept body (`D⊑…`); multi-concept (conjunctive) bodies are left to the CB
/// engine. Disjuncts naming concepts the EL pass never interned are skipped
/// (they carry no completed supers). Returns the number of pairs added.
fn hoist_residual_disjuncts(
    residual: &[JClause],
    it: &Interner,
    sub_super: &mut [HashSet<u32>],
) -> usize {
    let n = sub_super.len() as u32;
    // (name, term) of a concept atom over a *variable*; None for anything else.
    fn var_concept(a: &JAtom) -> Option<(&str, &JTerm)> {
        match concept_of(a) {
            Some((name, t)) if matches!(tk(t), Tk::Var(_)) => Some((name, t)),
            _ => None,
        }
    }
    let mut added = 0usize;
    for c in residual {
        if c.head.len() < 2 {
            continue;
        }
        // head: ≥2 concept atoms, all over ONE shared variable, nothing else.
        let mut hvar: Option<&JTerm> = None;
        let mut disjuncts: Vec<u32> = Vec::with_capacity(c.head.len());
        let mut ok = true;
        for a in &c.head {
            match var_concept(a) {
                Some((name, t)) if *hvar.get_or_insert(t) == t => match it.id(name) {
                    Some(id) if id < n => disjuncts.push(id),
                    _ => {
                        ok = false;
                        break;
                    }
                },
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok || disjuncts.len() < 2 {
            continue;
        }
        let hvar = hvar.unwrap();
        // subject: ⊤ (empty body) or a single concept over the SAME variable.
        let subject = match c.body.len() {
            0 => TOP,
            1 => match var_concept(&c.body[0]) {
                Some((name, t)) if t == hvar => match it.id(name) {
                    Some(id) if id < n => id,
                    _ => continue,
                },
                _ => continue,
            },
            _ => continue,
        };
        // common supers = ∩ over disjuncts of (sub_super[d] ∪ {d}).
        let supers_of = |d: u32| -> HashSet<u32> {
            let mut s = sub_super[d as usize].clone();
            s.insert(d);
            s
        };
        let mut common = supers_of(disjuncts[0]);
        for &d in &disjuncts[1..] {
            let s = supers_of(d);
            common.retain(|x| s.contains(x));
            if common.is_empty() {
                break;
            }
        }
        for x in common {
            if x != subject && x != TOP && sub_super[subject as usize].insert(x) {
                added += 1;
            }
        }
    }
    added
}

/// KM_ELC_RESIDUE_STATS — measure the INSUFFICIENT residue (Konclude's notion):
/// after EL saturation, how many concepts are touched by a parked disjunction
/// with no disjunct in their completed label. Reports before/after the
/// common-disjunct hoist so we can see how much the deterministic distribution
/// lemma resolves. Decides whether a shared-node residue-gate would pay off:
/// a small INSUFFICIENT set ⇒ route few concepts to a complete tester (fast +
/// complete); a near-total set ⇒ the gate buys nothing for this ontology.
fn residue_stats(residual: &[JClause], it: &Interner, sub_super: &mut [HashSet<u32>]) {
    let n = sub_super.len() as u32;
    fn var_concept(a: &JAtom) -> Option<(&str, &JTerm)> {
        match concept_of(a) {
            Some((name, t)) if matches!(tk(t), Tk::Var(_)) => Some((name, t)),
            _ => None,
        }
    }
    // Parse parked disjunctions into (subject, disjuncts); subject = TOP for an
    // empty body, a single concept for a one-atom body; multi-body skipped.
    let mut parked: Vec<(u32, Vec<u32>)> = Vec::new();
    for c in residual {
        if c.head.len() < 2 {
            continue;
        }
        let mut hvar: Option<&JTerm> = None;
        let mut disjuncts: Vec<u32> = Vec::with_capacity(c.head.len());
        let mut ok = true;
        for a in &c.head {
            match var_concept(a) {
                Some((name, t)) if *hvar.get_or_insert(t) == t => match it.id(name) {
                    Some(id) if id < n => disjuncts.push(id),
                    _ => {
                        ok = false;
                        break;
                    }
                },
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok || disjuncts.len() < 2 {
            continue;
        }
        let hvar = hvar.unwrap();
        let subject = match c.body.len() {
            0 => TOP,
            1 => match var_concept(&c.body[0]) {
                Some((name, t)) if t == hvar => match it.id(name) {
                    Some(id) if id < n => id,
                    _ => continue,
                },
                _ => continue,
            },
            _ => continue,
        };
        parked.push((subject, disjuncts));
    }
    // A concept C is INSUFFICIENT if some parked disjunction holds at C (subject is
    // ⊤, is C, or subsumes C) yet no disjunct is in C's completed label.
    let count_insuff = |ss: &[HashSet<u32>]| -> usize {
        let mut insuff = 0usize;
        for c in 0..n {
            if c == TOP || c == BOTTOM {
                continue;
            }
            let lab = &ss[c as usize];
            let live = parked.iter().any(|(subj, disj)| {
                let holds = *subj == TOP || *subj == c || lab.contains(subj);
                holds && disj.iter().all(|&d| d != c && !lab.contains(&d))
            });
            if live {
                insuff += 1;
            }
        }
        insuff
    };
    let named = (n as usize).saturating_sub(2); // minus TOP/BOTTOM
    let top_level = parked.iter().filter(|(s, _)| *s == TOP).count();
    let pre = count_insuff(sub_super);
    let added = hoist_residual_disjuncts(residual, it, sub_super);
    let post = count_insuff(sub_super);
    eprintln!(
        "KM_ELC_RESIDUE_STATS concepts={named} parked_disjunctions={} (top_level={top_level}) \
         insufficient_pre_hoist={pre} ({:.0}%) hoist_added={added} insufficient_post_hoist={post} ({:.0}%)",
        parked.len(),
        100.0 * pre as f64 / named.max(1) as f64,
        100.0 * post as f64 / named.max(1) as f64,
    );
}

/// Core of [`classify`] with the certificate mode explicit (the env read is in
/// `classify`; tests drive this directly to avoid racy `set_var` across
/// parallel test threads).
fn classify_inner(clauses: Vec<JClause>, cert: CertMode, debug: bool) -> Option<ElResult> {
    let lean_cert_path = std::env::var_os("KM_ELC_LEAN_CERT_OUT").map(std::path::PathBuf::from);
    let lean_cert_checker =
        std::env::var_os("KM_ELC_LEAN_CERT_CHECKER").map(std::path::PathBuf::from);
    let lean_cert_requested = lean_cert_path.is_some() || lean_cert_checker.is_some();
    let mut unresolved: Vec<String> = Vec::new();
    // Exact residual-shrinking rewrites, certificate routes only. Cert-off
    // classify declines on the first residual clause anyway, and leaving that
    // path byte-identical keeps `is_pure_el_shape` (the router's screen) in
    // step with what cert-off `classify` accepts.
    let mut clauses = clauses;
    if cert != CertMode::Off && std::env::var_os("KM_ELC_NO_BRIDGE_PREP").is_none() {
        prepare_inverse_bridges(&mut clauses, debug);
    }
    let clauses = clauses;
    let mut it = Interner::new();
    let (mut nfs, residual, skolem_target) = to_nf(&clauses, &mut it)?;
    // TOP is always a semantic concept context, even when no normalized axiom
    // mentions it explicitly. The inconsistency readout queries TOP ⊑ BOTTOM,
    // so omitting this initialization could miss an ontology-level clash.
    nfs.concept_names.insert(TOP);
    // ELK discards the OWL parse tree once axioms are indexed. `to_nf` has
    // interned the EL part into `nfs` (u32-keyed) and cloned the non-EL part into
    // `residual`; the original `clauses` (millions of `JClause`, each owning
    // `String` IRIs -- a multi-GB block on the giants) is dead from here on.
    // Drop it BEFORE saturation so the parse tree never coexists with the peak
    // saturation state. On a pure-EL ont (`residual` empty) this is the whole
    // input freed; the saturation then peaks on the interned state alone.
    let certificate_clauses = lean_cert_requested.then_some(clauses);
    let rcs = if residual.is_empty() {
        Vec::new()
    } else {
        if cert == CertMode::Off {
            if debug {
                eprintln!(
                    "KM_ELC defer: {} non-EL residual clause(s); first={}",
                    residual.len(),
                    residual
                        .first()
                        .and_then(|clause| serde_json::to_string(clause).ok())
                        .unwrap_or_else(|| "<unavailable>".to_string())
                );
            }
            return None;
        }
        match compile_residual(&residual, &mut it, &mut nfs, &skolem_target) {
            Some(r) => r,
            None => {
                if debug {
                    eprintln!(
                        "KM_ELC_CERT skip: {} residual clauses, uncheckable shape",
                        residual.len()
                    );
                }
                return None;
            }
        }
    };
    let n = it.len();
    let idx = build_idx(&nfs, n);
    let mut st = init_state(&nfs, n);
    // EL++ reflexive roles: seed a self-edge (C,R,C) at every satisfiable concept
    // node for each reflexive role (closed up the role hierarchy). The existing
    // NF4 (∃R.D⊑E), NF7 (R∘S⊑T, both chain positions), ⊥-edge, and role-lift
    // rules then fire over these edges through the normal fixpoint -- no new rule
    // logic. This mirrors ELK's `⊤⊑∃R.Self` + ObjectHasSelf decomposition, and
    // because a self-edge feeds NF7 in both directions it also closes the
    // reflexive-role-plus-chain corner ELK marks only partially supported.
    if !idx.reflexive_closed.is_empty() {
        for &c in &nfs.concept_names {
            if c == BOTTOM {
                continue;
            }
            for &r in &idx.reflexive_closed {
                st.add_edge(c, r, c);
            }
        }
    }
    // build_idx owns copies of every normal form used by the fixpoint. On the
    // pure-EL path there is no residual certificate, so only concept_names is
    // read after this point. Release the duplicate normal forms before the
    // saturation peak.
    if rcs.is_empty() && !lean_cert_requested {
        nfs.nf1 = Vec::new();
        nfs.nf2 = Vec::new();
        nfs.nf3 = Vec::new();
        nfs.nf4 = Vec::new();
        nfs.nf5 = Vec::new();
        nfs.nf6 = Vec::new();
        nfs.nf7 = Vec::new();
        nfs.role_names = HashSet::default();
        nfs.reflexive_roles = HashSet::default();
    }
    let mut prof = Prof::default();
    run(&idx, &mut st, &mut prof);
    if lean_cert_requested {
        if !residual.is_empty() {
            if debug {
                eprintln!("KM_ELC_LEAN_CERT defer: residual clauses are outside pure ELC");
            }
            return None;
        }
        let certificate = match build_lean_el_certificate(
            &nfs,
            &st,
            &it,
            certificate_clauses.as_deref().expect("requested certificate retains source clauses"),
            Vec::new(),
        ) {
            Ok(certificate) => certificate,
            Err(error) => {
                eprintln!("KM_ELC_LEAN_CERT fail closed: {error}");
                return None;
            }
        };
        let temporary_path;
        let path = if let Some(path) = lean_cert_path.as_deref() {
            path
        } else {
            temporary_path = std::env::temp_dir().join(format!(
                "km-elc-cert-{}.json",
                std::process::id()
            ));
            temporary_path.as_path()
        };
        let file = match std::fs::File::create(path) {
            Ok(file) => file,
            Err(error) => {
                eprintln!("KM_ELC_LEAN_CERT cannot create {}: {error}", path.display());
                return None;
            }
        };
        if let Err(error) = serde_json::to_writer(file, &certificate) {
            eprintln!("KM_ELC_LEAN_CERT cannot write {}: {error}", path.display());
            return None;
        }
        if let Some(checker) = lean_cert_checker.as_deref() {
            let status = match std::process::Command::new(checker)
                .arg(path)
                // The worker stdout is a JSON protocol. Checker diagnostics
                // must never be allowed to corrupt that stream.
                .stdout(std::process::Stdio::null())
                .status()
            {
                Ok(status) => status,
                Err(error) => {
                    eprintln!(
                        "KM_ELC_LEAN_CERT cannot execute {}: {error}",
                        checker.display()
                    );
                    return None;
                }
            };
            if lean_cert_path.is_none() {
                let _ = std::fs::remove_file(path);
            }
            if !status.success() {
                eprintln!(
                    "KM_ELC_LEAN_CERT checker {} rejected the certificate ({status})",
                    checker.display()
                );
                return None;
            }
            return Some(certificate.verified_result());
        }
    }
    if std::env::var_os("KM_ELC_PROFILE").is_some() {
        eprintln!(
            "KM_ELC_PROFILE sub_items={} edge_items={} | nf1_scan={} nf2_scan={} nf3_scan={} \
             nf4_sub_scan={} nf4_edge_scan={} nf7_scan={} botback={} | \
             nf4_batch_calls={} nf4_batch_edges={} nf4_batch_groups={} nf4_batch_missing={}",
            prof.sub_items,
            prof.edge_items,
            prof.nf1_scan,
            prof.nf2_scan,
            prof.nf3_scan,
            prof.nf4_sub_scan,
            prof.nf4_edge_scan,
            prof.nf7_scan,
            prof.botback,
            prof.nf4_batch_calls,
            prof.nf4_batch_edges,
            prof.nf4_batch_groups,
            prof.nf4_batch_missing
        );
    }
    let mut res = st;
    // KM_ELC_RESIDUE_STATS: measurement-only. After EL saturation (+ a local
    // common-disjunct hoist), report how many concepts the deterministic
    // saturation leaves INSUFFICIENT — i.e. touched by a parked disjunction with
    // no disjunct in their completed label (Konclude's INSUFFICIENT). This is the
    // size of the residue a shared-node residue-gate would have to SAT-test; it
    // decides whether that architecture pays off. Prints and exits (no classify).
    if std::env::var_os("KM_ELC_RESIDUE_STATS").is_some() {
        residue_stats(&residual, &it, &mut res.sub_super);
        return None;
    }
    // An inconsistent EL subset makes the full ontology inconsistent
    // (monotonicity), so that answer is exact without a certificate.
    let el_inconsistent = res.sub_super[TOP as usize].contains(&BOTTOM);
    if !rcs.is_empty() && !el_inconsistent {
        if debug {
            eprintln!("KM_ELC_CERT checking {} residual clauses", rcs.len());
        }
        let outcome = match cert {
            CertMode::Check => {
                if check_certificate(&rcs, &nfs, &res, debug) {
                    CertOutcome::Pass
                } else {
                    CertOutcome::Fail
                }
            }
            CertMode::Repair => repair_certify(&rcs, &nfs, &idx, &res, &it, debug),
            CertMode::Off => unreachable!("residual with cert off returns early"),
        };
        match outcome {
            CertOutcome::Pass => {}
            CertOutcome::Partial(subjects) => {
                unresolved = subjects.iter().map(|&c| it.name(c).to_string()).collect();
            }
            CertOutcome::Fail => return None,
        }
    }

    // KM_ELC_HOIST (P1): recover subsumptions hidden in parked disjunctions via
    // the ⊔-distribution lemma over the completed relation. Sound (adds only
    // entailed pairs), so it runs after the certificate without affecting its
    // verdict; inert when there are no residual disjunctions.
    if !residual.is_empty() && std::env::var_os("KM_ELC_HOIST").is_some() {
        let added = hoist_residual_disjuncts(&residual, &it, &mut res.sub_super);
        if debug {
            eprintln!("KM_ELC_HOIST added {added} common-disjunct subsumptions");
        }
    }

    let unresolved_set: std::collections::BTreeSet<&str> =
        unresolved.iter().map(|s| s.as_str()).collect();
    // Everything below reads only the completed relation (`sub_super`) and the
    // interner names. The rule indexes, the normal forms, the residual, the
    // compiled residual clauses, and the role graph (`edges` / `in_by_role` /
    // `in_roles` / `prop`) are dead here — free them BEFORE materialising the output
    // strings, so the string map reuses their memory instead of stacking on
    // top of the full saturation state (process peak RSS on the ORE giants
    // sits exactly at this point, the fixpoint). Destructuring `res` drops the
    // unbound `State` fields in place.
    let State { mut sub_super, .. } = res;
    drop(idx);
    drop(nfs);
    drop(rcs);
    drop(residual);
    drop(skolem_target);
    let mut subsumptions = std::collections::BTreeMap::new();
    for c in 0..sub_super.len() {
        let cid = c as u32;
        // ⊤/⊥ as a *subject* give trivially-true ⊤⊑X / ⊥⊑X, which no reasoner
        // reports as a class subsumption — skip them.
        if cid == TOP || cid == BOTTOM {
            continue;
        }
        // unresolved subjects are answered by the context engine instead
        if unresolved_set.contains(it.name(cid)) {
            continue;
        }
        // Take the subject's super-set so it is freed as soon as it has been
        // converted (the set and its string form never coexist in full); the
        // element sequence is the set's own iteration, exactly as before.
        let sups = std::mem::take(&mut sub_super[c]);
        let mut out = Vec::new();
        for &d in sups.iter() {
            if d == cid || d == TOP {
                continue;
            }
            out.push(if d == BOTTOM {
                "owl:Nothing".to_string()
            } else {
                it.name(d).to_string()
            });
        }
        if !out.is_empty() {
            subsumptions.insert(it.name(cid).to_string(), out);
        }
    }

    Some(ElResult {
        subsumptions,
        inconsistent: el_inconsistent,
        unresolved,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lean_certificate_reconstructs_and_audits_the_production_fixpoint() {
        let mut concepts = HashSet::default();
        concepts.extend([TOP, BOTTOM, 2, 3]);
        let mut roles = HashSet::default();
        roles.extend([4, 5, 6]);
        let mut reflexive = HashSet::default();
        reflexive.insert(4);
        let nfs = Nfs {
            nf1: vec![Nf1 { sub: 2, sup: 3 }],
            nf2: vec![Nf2 { sub1: 2, sub2: 3, sup: TOP }],
            nf3: vec![Nf3 { sub: 3, role: 4, filler: 2 }],
            nf4: vec![Nf4 { role: 4, filler: 3, sup: 2 }],
            nf5: vec![],
            nf6: vec![Nf6 { sub: 4, sup: 5 }],
            nf7: vec![Nf7 { r1: 5, r2: 4, sup: 6 }],
            reflexive_roles: reflexive,
            concept_names: concepts,
            role_names: roles,
            conjunction_origins: HashMap::default(),
        };
        let idx = build_idx(&nfs, 7);
        let mut state = init_state(&nfs, 7);
        for &a in &nfs.concept_names {
            if a != BOTTOM {
                for &role in &idx.reflexive_closed {
                    state.add_edge(a, role, a);
                }
            }
        }
        run(&idx, &mut state, &mut Prof::default());

        let mut interner = Interner::new();
        for name in ["A", "B", "r", "s", "t"] {
            interner.intern(name);
        }
        let cert = build_lean_el_certificate(&nfs, &state, &interner, &[], Vec::new())
            .expect("exact certificate");
        assert_eq!(cert.version, 4);
        assert!(!cert.trace.is_empty());
        let json = serde_json::to_string(&cert).expect("certificate JSON");
        assert!(json.contains("\"nf7\""));
        assert!(json.contains("\"reflexive\""));
        assert!(json.contains("\"public_subsumptions\""));
        assert!(json.contains("\"public_named_subsumptions\""));
        assert!(cert.active_concepts.contains(&TOP));
        assert_eq!(cert.symbols.len(), 7);
        assert_eq!(
            cert.public_subsumptions.len(),
            cert.public_named_subsumptions.len()
        );
        let verified = cert.verified_result();
        assert_eq!(verified.inconsistent, cert.public_inconsistent);
        assert!(verified.unresolved.is_empty());
        assert!(cert.public_subsumptions.iter().all(|fact| {
            fact.sub != TOP
                && fact.sub != BOTTOM
                && fact.sup != fact.sub
                && fact.sup != TOP
        }));

        state.sub_super[2].insert(6);
        assert!(build_lean_el_certificate(&nfs, &state, &interner, &[], Vec::new())
            .unwrap_err()
            .contains("Rust-only subsumption"));
    }

    fn clauses(json: &str) -> Vec<JClause> {
        serde_json::from_str::<Vec<JClause>>(json).expect("test clause JSON")
    }
    fn v(n: &str) -> String {
        format!("{{\"kind\":\"var\",\"name\":\"{}\"}}", n)
    }
    fn c(name: &str, t: &str) -> String {
        format!(
            "{{\"kind\":\"concept\",\"concept\":\"{}\",\"term\":{}}}",
            name,
            v(t)
        )
    }

    fn positive_abox_consistency(ofn: &str) -> Option<bool> {
        crate::frontend::with_ofn_to_clauses_requested_route(
            ofn,
            crate::routing::Route::ProductionAll,
            |result| positive_abox_consistent(result.clauses, &result.nominal_abox),
        )
        .expect("test ontology parses")
    }

    #[test]
    fn positive_abox_completion_respects_identity_and_conjunction_clashes() {
        let consistent = r#"Ontology(
            SubClassOf(ObjectIntersectionOf(<A> <B>) owl:Nothing)
            ClassAssertion(<A> <a>)
            ClassAssertion(<B> <b>)
            DifferentIndividuals(<a> <b>)
        )"#;
        assert_eq!(positive_abox_consistency(consistent), Some(true));

        let inconsistent = r#"Ontology(
            SubClassOf(ObjectIntersectionOf(<A> <B>) owl:Nothing)
            ClassAssertion(<A> <a>)
            ClassAssertion(<B> <b>)
            SameIndividual(<a> <b>)
        )"#;
        assert_eq!(positive_abox_consistency(inconsistent), Some(false));
    }

    #[test]
    fn positive_abox_completion_materializes_ground_role_edges() {
        let inconsistent = r#"Ontology(
            SubClassOf(ObjectSomeValuesFrom(<r> <B>) owl:Nothing)
            ObjectPropertyAssertion(<r> <a> <b>)
            ClassAssertion(<B> <b>)
        )"#;
        assert_eq!(positive_abox_consistency(inconsistent), Some(false));
    }

    #[test]
    fn positive_abox_completion_retains_the_exact_named_taxonomy() {
        let ofn = r#"Ontology(
            Declaration(Class(<A>))
            Declaration(Class(<B>))
            Declaration(Class(<C>))
            SubClassOf(<A> <B>)
            SubClassOf(<B> <C>)
            ClassAssertion(<A> <a>)
        )"#;
        crate::frontend::with_ofn_to_clauses_requested_route(
            ofn,
            crate::routing::Route::ProductionAll,
            |frontend| {
                let named: std::collections::HashSet<&str> =
                    frontend.named.iter().map(String::as_str).collect();
                let tbox = classify(frontend.clauses.clone()).expect("pure EL TBox");
                let abox = positive_abox_classify(
                    frontend.clauses,
                    &frontend.nominal_abox,
                )
                .expect("positive EL ABox");
                assert!(abox.consistent);
                let abox = abox.classification.expect("completion ran");
                for subject in named {
                    assert_eq!(
                        abox.subsumptions.get(subject),
                        tbox.subsumptions.get(subject),
                        "named taxonomy changed for {subject}"
                    );
                }
            },
        )
        .expect("ontology parses");
    }
    fn cf(name: &str, f: &str, t: &str) -> String {
        format!(
            "{{\"kind\":\"concept\",\"concept\":\"{}\",\"term\":{{\"kind\":\"fun\",\"function\":\"{}\",\"arg\":{}}}}}",
            name, f, v(t)
        )
    }
    fn r(role: &str, s: &str, t: &str) -> String {
        format!(
            "{{\"kind\":\"role\",\"role\":\"{}\",\"source\":{},\"target\":{}}}",
            role,
            v(s),
            v(t)
        )
    }
    fn rf(role: &str, s: &str, f: &str) -> String {
        format!(
            "{{\"kind\":\"role\",\"role\":\"{}\",\"source\":{},\"target\":{{\"kind\":\"fun\",\"function\":\"{}\",\"arg\":{}}}}}",
            role, v(s), f, v(s)
        )
    }
    fn cl(body: &[String], head: &[String]) -> String {
        format!(
            "{{\"body\":[{}],\"head\":[{}]}}",
            body.join(","),
            head.join(",")
        )
    }

    /// `a ≈ b` over two plain variables (an at-most head).
    fn eqv(a: &str, b: &str) -> String {
        format!("{{\"kind\":\"eq\",\"left\":{},\"right\":{}}}", v(a), v(b))
    }
    /// `f(t) ≈ g(t)` over two skolem terms (the `≥n` witness-distinctness body).
    fn eqf(f: &str, g: &str, t: &str) -> String {
        let fun = |name: &str| {
            format!(
                "{{\"kind\":\"fun\",\"function\":\"{}\",\"arg\":{}}}",
                name,
                v(t)
            )
        };
        format!(
            "{{\"kind\":\"eq\",\"left\":{},\"right\":{}}}",
            fun(f),
            fun(g)
        )
    }

    fn subs_of(res: &ElResult, sub: &str) -> Vec<String> {
        res.subsumptions.get(sub).cloned().unwrap_or_default()
    }

    #[test]
    fn pure_el_screen_matches_all_cert_off_normal_forms() {
        let cs = clauses(&format!(
            "[{},{},{},{},{},{},{},{}]",
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[c("A", "x"), c("B", "x")], &[c("C", "x")]),
            cl(&[c("Z", "x")], &[]),
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[r("R", "x", "y"), c("B", "y")], &[c("D", "x")]),
            cl(&[r("R", "x", "y")], &[r("S", "x", "y")]),
            cl(&[r("R", "x", "y"), r("S", "y", "z")], &[r("T", "x", "z")]),
        ));
        assert!(is_pure_el_shape(&cs));
        assert!(classify_inner(cs, CertMode::Off, false).is_some());

        let reflexive = clauses(&format!("[{}]", cl(&[], &[r("R", "x", "x")])));
        assert!(is_pure_el_shape(&reflexive));
        assert!(classify_inner(reflexive, CertMode::Off, false).is_some());
    }

    #[test]
    fn pure_el_screen_rejects_every_cert_off_residual_and_orphan() {
        let disjunction = clauses(&format!(
            "[{}]",
            cl(&[c("A", "x")], &[c("B", "x"), c("C", "x")])
        ));
        assert!(!is_pure_el_shape(&disjunction));
        assert!(classify_inner(disjunction, CertMode::Off, false).is_none());

        let inverse = clauses(&format!(
            "[{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")])
        ));
        assert!(!is_pure_el_shape(&inverse));
        assert!(classify_inner(inverse, CertMode::Off, false).is_none());

        let orphan_filler = clauses(&format!("[{}]", cl(&[c("A", "x")], &[cf("B", "f", "x")])));
        assert!(!is_pure_el_shape(&orphan_filler));
        assert!(classify_inner(orphan_filler, CertMode::Off, false).is_none());

        let equality = clauses(&format!(
            "[{{\"body\":[],\"head\":[{{\"kind\":\"eq\",\"left\":{},\"right\":{}}}]}}]",
            v("x"),
            v("y")
        ));
        assert!(!is_pure_el_shape(&equality));
        assert!(classify_inner(equality, CertMode::Off, false).is_none());
    }

    fn rr(role: &str, s: &str, t: &str) -> String {
        format!(
            "{{\"kind\":\"role\",\"role\":\"{}\",\"source\":{{\"kind\":\"fun\",\"function\":\"{}\",\"arg\":{}}},\"target\":{}}}",
            role, s, v(t), v(t)
        )
    }

    /// POSITIVE: a mutual pair whose eliminated side carries no EL rule is
    /// substituted away, the bridges go with it, and the residual constraint
    /// over the eliminated role is still enforced — against the real edges of
    /// the canonical role, with no mirror edge materialised.
    #[test]
    fn exact_inverse_substitution_removes_bridges_and_keeps_the_constraint() {
        // A ⊑ ∃R.F, ∃R.F ⊑ D, S = R⁻, and the residual ⊥-clause
        // `S(x,y) ∧ G(y) → ⊥` (an empty head keeps it out of the normal forms).
        // `S` occurs only there and in the bridges.
        let mut cs = clauses(&format!(
            "[{},{},{},{},{},{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("F", "f", "x")]),
            cl(&[r("R", "x", "y"), c("F", "y")], &[c("D", "x")]),
            cl(&[r("S", "x", "y"), c("G", "y")], &[]),
        ));
        assert_eq!(mutual_inverse_pairs(&cs), vec![("R".into(), "S".into())]);
        assert!(inverse_substitution_is_exact(&cs, "S"));
        let (removed, oriented) = prepare_inverse_bridges(&mut cs, false);
        assert_eq!(oriented, 1);
        assert_eq!(removed, 2, "both bridges become tautologies");
        assert!(cs.iter().all(|c| !mentions_role(c, "S")));
        // The surviving constraint reads `R(y,x) ∧ G(y) → ⊥`.
        let kept = cs.iter().find(|c| c.head.is_empty()).expect("⊥ clause");
        assert!(mentions_role(kept, "R"));
        // A ⊑ D still classifies, and A is not driven to ⊥ (no G anywhere).
        let res = classify_inner(cs, CertMode::Repair, false).expect("certifies");
        assert!(subs_of(&res, "A").contains(&"D".to_string()));
        assert!(!subs_of(&res, "A").contains(&"owl:Nothing".to_string()));
    }

    /// NEGATIVE / ADVERSARIAL ORIENTATION: when BOTH sides of the pair carry an
    /// EL rule, no orientation is exact, so nothing is rewritten and both
    /// bridges stay in the residual for the certificate to discharge. This is
    /// the ORE-1194 shape (`BFO_0000050`/`BFO_0000051`, each with its own NF3
    /// and NF4 axioms).
    #[test]
    fn inverse_pair_with_el_rules_on_both_sides_is_left_alone() {
        let mut cs = clauses(&format!(
            "[{},{},{},{},{},{},{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("F", "f", "x")]),
            cl(&[r("R", "x", "y"), c("F", "y")], &[c("D", "x")]),
            cl(&[c("B", "x")], &[rf("S", "x", "g")]),
            cl(&[r("S", "x", "y"), c("F", "y")], &[c("E", "x")]),
        ));
        assert_eq!(mutual_inverse_pairs(&cs), vec![("R".into(), "S".into())]);
        assert!(!inverse_substitution_is_exact(&cs, "R"));
        assert!(!inverse_substitution_is_exact(&cs, "S"));
        let before = cs.len();
        let (_, oriented) = prepare_inverse_bridges(&mut cs, false);
        assert_eq!(oriented, 0);
        assert_eq!(cs.len(), before, "no clause deleted");
        assert!(cs.iter().filter(|c| as_inverse_bridge(c).is_some()).count() == 2);
    }

    /// A one-way inclusion `R ⊑ S⁻` is not an equivalence and must never be
    /// substituted. It IS deletable when `R` occurs in no head, by the
    /// vacuous-role argument.
    #[test]
    fn one_way_bridge_is_never_substituted_but_may_be_vacuous() {
        let one_way = clauses(&format!(
            "[{},{},{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[c("A", "x")], &[rf("S", "x", "f")]),
            cl(&[c("A", "x")], &[cf("F", "f", "x")]),
        ));
        assert!(mutual_inverse_pairs(&one_way).is_empty());
        let mut cs = one_way.clone();
        // `R` is head-free, so the bridge goes.
        let (removed, oriented) = prepare_inverse_bridges(&mut cs, false);
        assert_eq!((removed, oriented), (1, 0));
        assert!(cs.iter().all(|c| !mentions_role(c, "R")));

        // With `R` occurring in a head that survives, the bridge is NOT vacuous
        // and must stay: `R ⊑ S⁻` is a real constraint the certificate owes.
        let mut constrained = one_way;
        constrained.extend(clauses(&format!(
            "[{},{}]",
            cl(&[c("B", "x")], &[rf("R", "x", "g")]),
            cl(&[c("B", "x")], &[cf("G", "g", "x")]),
        )));
        let (removed, oriented) = prepare_inverse_bridges(&mut constrained, false);
        assert_eq!((removed, oriented), (0, 0));
        assert!(constrained.iter().any(|c| as_inverse_bridge(c).is_some()));
    }

    /// ADVERSARIAL: an ambiguous inverse graph (`R` reciprocated by two distinct
    /// roles) is skipped rather than quotiented.
    #[test]
    fn ambiguous_inverse_graph_is_refused() {
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
            cl(&[r("R", "x", "y")], &[r("T", "y", "x")]),
            cl(&[r("T", "x", "y")], &[r("R", "y", "x")]),
        ));
        assert!(mutual_inverse_pairs(&cs).is_empty());

        // Same-variable and same-role shapes are not bridges either: `R(x,x)` is
        // reflexivity and `R(x,y) → R(y,x)` is symmetry.
        let reflexive = clauses(&format!(
            "[{}]",
            cl(&[r("R", "x", "x")], &[r("S", "x", "x")])
        ));
        assert!(as_inverse_bridge(&reflexive[0]).is_none());
        let symmetric = clauses(&format!(
            "[{}]",
            cl(&[r("R", "x", "y")], &[r("R", "y", "x")])
        ));
        assert!(as_inverse_bridge(&symmetric[0]).is_none());
    }

    /// ROLE INCLUSION and CHAIN clauses are orientation-sensitive, so a pair
    /// whose eliminated side appears in one is refused. Substituting into
    /// `S ⊑ T` would produce the reverse inclusion `R⁻ ⊑ T`, which this
    /// completion has no normal form for.
    #[test]
    fn orientation_sensitive_role_inclusions_and_chains_block_substitution() {
        let inclusion = clauses(&format!(
            "[{},{},{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("T", "x", "y")]),
        ));
        assert!(!inverse_substitution_is_exact(&inclusion, "S"));

        let chain = clauses(&format!(
            "[{},{},{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
            cl(&[r("S", "x", "y"), r("T", "y", "z")], &[r("U", "x", "z")]),
        ));
        assert!(!inverse_substitution_is_exact(&chain, "S"));
    }

    /// FUN TERM: a skolem-bearing residual is rewritten in place (the swap moves
    /// `f(x)` from target to source) and stays checkable, and the NF3 that
    /// introduces the witness is untouched because it belongs to the canonical
    /// role.
    #[test]
    fn substitution_rewrites_fun_term_residuals() {
        let mut cs = clauses(&format!(
            "[{},{},{},{},{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("F", "f", "x")]),
            // residual (disjunctive head, so not a normal form):
            // `S(f(x),x) → D(x) ⊔ E(x)`
            format!(
                "{{\"body\":[{}],\"head\":[{},{}]}}",
                rr("S", "f", "x"),
                c("D", "x"),
                c("E", "x")
            ),
        ));
        assert!(inverse_substitution_is_exact(&cs, "S"));
        prepare_inverse_bridges(&mut cs, false);
        let rewritten = cs
            .iter()
            .find(|c| c.head.len() == 2)
            .expect("residual survives");
        // The `S(f(x),x)` atom is now `R(x,f(x))`: source is the variable.
        let JAtom::Role {
            role,
            source,
            target,
        } = &rewritten.body[0]
        else {
            panic!("role atom")
        };
        assert_eq!(role, "R");
        assert!(matches!(source, JTerm::Var { .. }));
        assert!(matches!(target, JTerm::Fun { .. }));
    }

    /// The vacuous-role rule is a fixpoint: deleting a clause can leave a
    /// further role head-free.
    #[test]
    fn vacuous_role_pruning_reaches_a_fixpoint() {
        let mut cs = clauses(&format!(
            "[{},{},{}]",
            // U is head-free; deleting `U ⊑ T` makes T head-free; then `T ⊑ S`.
            cl(&[r("U", "x", "y")], &[r("T", "x", "y")]),
            cl(&[r("T", "x", "y")], &[r("S", "x", "y")]),
            cl(&[c("A", "x")], &[c("B", "x")]),
        ));
        let (removed, roles) = prune_vacuous_role_clauses(&mut cs);
        assert_eq!((removed, roles), (2, 2));
        assert_eq!(cs.len(), 1);
    }

    /// CERTIFICATE: pruning must not change any answer. A head-free role
    /// carrying a range clause is deleted, and the classification is identical
    /// to the one the certificate produces with the clause retained but with the
    /// role explicitly emptied.
    #[test]
    fn vacuous_prune_preserves_the_certified_classification() {
        let base = format!(
            "{},{},{}",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("F", "f", "x")]),
            cl(&[r("R", "x", "y"), c("F", "y")], &[c("D", "x")]),
        );
        // `V` occurs only in bodies: a range clause and a ⊥ clause.
        let with_vacuous = clauses(&format!(
            "[{},{},{}]",
            base,
            cl(&[r("V", "x", "y")], &[c("G", "y")]),
            cl(&[r("V", "x", "y"), c("G", "y")], &[]),
        ));
        let without = clauses(&format!("[{}]", base));
        let a = classify_inner(with_vacuous, CertMode::Repair, false).expect("certifies");
        let b = classify_inner(without, CertMode::Repair, false).expect("certifies");
        assert_eq!(a.subsumptions, b.subsumptions);
        assert_eq!(a.inconsistent, b.inconsistent);
        assert!(subs_of(&a, "A").contains(&"D".to_string()));
    }

    /// Orienting a proven inverse pair onto one canonical role and running the
    /// rewritten axioms as EL normal forms is UNSOUND in this completion, and
    /// this is the witness.
    ///
    /// `C ⊑ ∃R.D`, `C ⊑ A`, `S = R⁻`, `∃S.A ⊑ E`. Substituting `S := R⁻` turns
    /// `∃S.A ⊑ E` into `R(y,x) ∧ A(y) → E(x)`: a *reverse*-oriented NF4 that
    /// fires along the edge `C —R→ D` and writes `E` at node `D`, i.e. derives
    /// `D ⊑ E`. That subsumption does not hold: the one-element interpretation
    /// `Δ = {d}`, `D = {d}`, every other name empty, satisfies all four axioms
    /// (`C`, `R`, `S` are empty) and `d ∉ E`.
    ///
    /// The cause is structural, not a bug in any particular rewrite. A node
    /// here denotes *the* generic instance of a concept name, and every
    /// `X ⊑ ∃R.D` shares the single successor node `D`. A reverse-oriented rule
    /// concludes at that shared successor from ONE of its predecessors, so it
    /// asserts of every `D` instance what holds only of the `D` instances that
    /// have an `A` predecessor. Soundness needs the successor to carry
    /// `∃R⁻.A` as part of its identity, which is a context (concept-set)
    /// calculus — the CB engine — not single-name EL completion.
    #[test]
    fn reverse_oriented_inverse_nf4_would_be_unsound() {
        let cs = clauses(&format!(
            "[{},{},{},{},{}]",
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
            cl(&[c("C", "x")], &[rf("R", "x", "f")]),
            cl(&[c("C", "x")], &[cf("D", "f", "x")]),
            cl(&[c("C", "x")], &[c("A", "x")]),
        ));
        let mut cs = cs;
        cs.extend(clauses(&format!(
            "[{}]",
            cl(&[r("S", "x", "y"), c("A", "y")], &[c("E", "x")])
        )));
        // Whatever the route does with the bridges, `D ⊑ E` must never appear.
        if let Some(res) = classify_inner(cs, CertMode::Repair, false) {
            assert!(
                !subs_of(&res, "D").contains(&"E".to_string()),
                "unsound: derived D ⊑ E, which has a countermodel"
            );
        }
    }

    /// Regression: the NF recognizers accepted clauses whose VARIABLE WIRING
    /// does not match the normal form they were filed under — `to_nf` compared
    /// the body concept to the role target but never the head to the role
    /// source, and NF1/NF2/⊥ never required a shared variable at all. Reading
    /// such a clause as its nearest normal form is unsound (NF4 head on the
    /// target / self-loop) or incomplete (split-variable conjunctions), so
    /// every one of these shapes must land in the residual: cert-off classify
    /// declines (exit-3 defer to the CB engine) and the pure-EL screen rejects.
    #[test]
    fn adversarial_variable_wiring_is_rejected_to_residual() {
        // R(x,y) ∧ A(y) → B(y) is A ⊓ ∃R⁻.⊤ ⊑ B, not ∃R.A ⊑ B.
        let head_on_target = clauses(&format!(
            "[{}]",
            cl(&[r("R", "x", "y"), c("A", "y")], &[c("B", "y")])
        ));
        assert!(!is_pure_el_shape(&head_on_target));
        assert!(classify_inner(head_on_target, CertMode::Off, false).is_none());

        // R(x,x) ∧ A(x) → B(x) is a self-restriction, not ∃R.A ⊑ B.
        let self_loop = clauses(&format!(
            "[{}]",
            cl(&[r("R", "x", "x"), c("A", "x")], &[c("B", "x")])
        ));
        assert!(!is_pure_el_shape(&self_loop));
        assert!(classify_inner(self_loop, CertMode::Off, false).is_none());

        // A(x) ∧ B(y) → C(x) is not A ⊓ B ⊑ C.
        let split_conj = clauses(&format!(
            "[{}]",
            cl(&[c("A", "x"), c("B", "y")], &[c("C", "x")])
        ));
        assert!(!is_pure_el_shape(&split_conj));
        assert!(classify_inner(split_conj, CertMode::Off, false).is_none());

        // A(x) ∧ B(y) → ⊥ is a global constraint, not A ⊓ B ⊑ ⊥.
        let split_bottom = clauses(&format!("[{}]", cl(&[c("A", "x"), c("B", "y")], &[])));
        assert!(!is_pure_el_shape(&split_bottom));
        assert!(classify_inner(split_bottom, CertMode::Off, false).is_none());

        // R(x,x) → S(x,x) is a self-restriction implication, not R ⊑ S.
        let collapsed_role_sub = clauses(&format!(
            "[{}]",
            cl(&[r("R", "x", "x")], &[r("S", "x", "x")])
        ));
        assert!(!is_pure_el_shape(&collapsed_role_sub));
        assert!(classify_inner(collapsed_role_sub, CertMode::Off, false).is_none());

        // R(x,x) ∧ S(x,z) → T(x,z) is not the unrestricted chain R∘S ⊑ T.
        let collapsed_role_chain = clauses(&format!(
            "[{}]",
            cl(&[r("R", "x", "x"), r("S", "x", "z")], &[r("T", "x", "z")],)
        ));
        assert!(!is_pure_el_shape(&collapsed_role_chain));
        assert!(classify_inner(collapsed_role_chain, CertMode::Off, false).is_none());

        // The Skolem argument is the universally quantified source variable.
        // Changing it produces a different first-order clause, not A ⊑ ∃R.B.
        let mismatched_skolem_argument = clauses(&format!(
            "[{},{}]",
            cl(
                &[c("A", "x")],
                &[format!(
                    "{{\"kind\":\"role\",\"role\":\"R\",\"source\":{},\"target\":{{\"kind\":\"fun\",\"function\":\"f\",\"arg\":{}}}}}",
                    v("x"),
                    v("y")
                )],
            ),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
        ));
        assert!(!is_pure_el_shape(&mismatched_skolem_argument));
        assert!(classify_inner(mismatched_skolem_argument, CertMode::Off, false).is_none());

        // Both halves must quantify the same source variable as their Skolem
        // argument; merely sharing a function name is insufficient.
        let mismatched_filler_argument = clauses(&format!(
            "[{},{}]",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "y")]),
        ));
        assert!(!is_pure_el_shape(&mismatched_filler_argument));
        assert!(classify_inner(mismatched_filler_argument, CertMode::Off, false).is_none());
    }

    #[test]
    fn output_tail_semantics_preserved() {
        // Pins the exact semantics of classify_inner's output loop, which now
        // frees the saturation state before (and while) materialising the
        // string map: an unsatisfiable subject reports owl:Nothing; ⊤/⊥ never
        // appear as subjects; ⊤ and the subject itself are never reported as
        // supers; a ⊤ ⊑ G axiom surfaces on the named subjects instead.
        let cs = clauses(&format!(
            "[{},{},{}]",
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[c("Z", "x")], &[]),
            cl(&[], &[c("G", "x")]),
        ));
        let res = classify_inner(cs, CertMode::Off, false).expect("pure EL");
        assert!(subs_of(&res, "Z").contains(&"owl:Nothing".to_string()));
        let a = subs_of(&res, "A");
        assert!(a.contains(&"B".to_string()));
        assert!(a.contains(&"G".to_string()));
        assert!(!a.contains(&"A".to_string()));
        for (subject, supers) in &res.subsumptions {
            assert!(subject != "\u{22a4}" && subject != "\u{22a5}");
            assert!(supers.iter().all(|s| s != "\u{22a4}" && s != subject));
        }
        assert!(!res.inconsistent);
    }

    #[test]
    fn reflexive_role_fires_nf4_elimination() {
        // A ⊑ B, ∃R.B ⊑ C, Reflexive(R) ⟹ A ⊑ C (the reflexive self-edge at A,
        // whose target A is ⊑ B, satisfies ∃R.B at A). Without reflexivity there
        // is no edge and A ⋢ C.
        let ab = cl(&[c("A", "x")], &[c("B", "x")]);
        let nf4 = cl(&[r("R", "x", "y"), c("B", "y")], &[c("C", "x")]);
        let refl = cl(&[], &[r("R", "x", "x")]);
        let cs = clauses(&format!("[{},{},{}]", ab, nf4, refl));
        let res = classify_inner(cs, CertMode::Off, false).expect("pure EL + reflexive role");
        assert!(
            subs_of(&res, "A").contains(&"C".to_string()),
            "A⊑C via reflexive R: got {:?}",
            subs_of(&res, "A")
        );
        // Sanity: drop the reflexive fact and A⊑C must disappear.
        let cs_no = clauses(&format!("[{},{}]", ab, nf4));
        let res_no = classify_inner(cs_no, CertMode::Off, false).expect("pure EL");
        assert!(!subs_of(&res_no, "A").contains(&"C".to_string()));
    }

    #[test]
    fn nf4_backward_join_selects_only_the_exact_role_bucket() {
        // Both NF4 axioms share filler B. An R backward link must select every
        // R conclusion and no S conclusion; an S link must do the converse.
        // This pins the role-range index used by the Sub side of the join.
        let a_r = cl(&[c("A", "x")], &[rf("R", "x", "fr")]);
        let fr_b = cl(&[c("A", "x")], &[cf("B", "fr", "x")]);
        let x_s = cl(&[c("X", "x")], &[rf("S", "x", "fs")]);
        let fs_b = cl(&[c("X", "x")], &[cf("B", "fs", "x")]);
        let r_c = cl(&[r("R", "x", "y"), c("B", "y")], &[c("C", "x")]);
        let r_e = cl(&[r("R", "x", "y"), c("B", "y")], &[c("E", "x")]);
        let s_d = cl(&[r("S", "x", "y"), c("B", "y")], &[c("D", "x")]);
        let cs = clauses(&format!(
            "[{},{},{},{},{},{},{}]",
            a_r, fr_b, x_s, fs_b, r_c, r_e, s_d
        ));
        let res = classify_inner(cs, CertMode::Off, false).expect("pure EL");
        let a = subs_of(&res, "A");
        assert!(a.contains(&"C".to_string()) && a.contains(&"E".to_string()));
        assert!(!a.contains(&"D".to_string()));
        let x = subs_of(&res, "X");
        assert!(x.contains(&"D".to_string()));
        assert!(!x.contains(&"C".to_string()) && !x.contains(&"E".to_string()));
    }

    #[test]
    fn reflexive_role_composes_with_chain() {
        // Reflexive(R), R∘S ⊑ T, A ⊑ ∃S.B, ∃T.B ⊑ D ⟹ A ⊑ D.
        // The self-edge (A,R,A) composes with the S-edge (A,S,B) via R∘S⊑T to a
        // T-edge (A,T,B), which fires the NF4 ∃T.B⊑D. This is the reflexive-role-
        // plus-chain case ELK marks only partially supported.
        let refl = cl(&[], &[r("R", "x", "x")]);
        let chain = cl(&[r("R", "x", "y"), r("S", "y", "z")], &[r("T", "x", "z")]);
        let ex_role = cl(&[c("A", "x")], &[rf("S", "x", "f")]);
        let ex_fill = cl(&[c("A", "x")], &[cf("B", "f", "x")]);
        let nf4_t = cl(&[r("T", "x", "y"), c("B", "y")], &[c("D", "x")]);
        let cs = clauses(&format!(
            "[{},{},{},{},{}]",
            refl, chain, ex_role, ex_fill, nf4_t
        ));
        let res = classify_inner(cs, CertMode::Off, false).expect("pure EL + reflexive + chain");
        assert!(
            subs_of(&res, "A").contains(&"D".to_string()),
            "A⊑D via reflexive R composing R∘S⊑T: got {:?}",
            subs_of(&res, "A")
        );
    }

    #[test]
    fn cert_passes_when_disjunction_already_decided() {
        // EL: A ⊑ B. Residual: A → B ∨ D (every A-node has B). Must classify
        // and keep the EL answer.
        let cs = clauses(&format!(
            "[{},{}]",
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[c("A", "x")], &[c("B", "x"), c("D", "x")]),
        ));
        let res = classify_inner(cs, CertMode::Check, false).expect("certificate should pass");
        assert!(subs_of(&res, "A").contains(&"B".to_string()));
        assert!(!res.inconsistent);
    }

    #[test]
    fn cert_fails_on_live_disjunction() {
        // Residual: A → D ∨ E with neither derivable: the canonical model
        // violates it, so elc must hand off to the context engine.
        let cs = clauses(&format!(
            "[{},{}]",
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[c("A", "x")], &[c("D", "x"), c("E", "x")]),
        ));
        assert!(classify_inner(cs, CertMode::Check, false).is_none());
    }

    #[test]
    fn elc_hoist_recovers_common_disjunct_super() {
        // Completed EL relation: A⊑X, B⊑X. Parked residual: D ⊑ A ∨ B.
        // ⊔-distribution ⟹ D ⊑ X (a subsumption hidden in the parked disjunction).
        let mut it = Interner::new();
        let (a, b, x, d) = (
            it.intern("A"),
            it.intern("B"),
            it.intern("X"),
            it.intern("D"),
        );
        let mut sub_super: Vec<HashSet<u32>> = vec![HashSet::default(); it.len()];
        sub_super[a as usize].insert(x);
        sub_super[b as usize].insert(x);
        let residual = clauses(&format!(
            "[{}]",
            cl(&[c("D", "x")], &[c("A", "x"), c("B", "x")])
        ));
        let added = hoist_residual_disjuncts(&residual, &it, &mut sub_super);
        assert_eq!(added, 1, "exactly D⊑X recovered");
        assert!(sub_super[d as usize].contains(&x), "D⊑X must be derived");
    }

    #[test]
    fn elc_hoist_skips_when_no_common_super() {
        // A⊑X, B⊑Y. D ⊑ A ∨ B has no common super ⟹ nothing recovered.
        let mut it = Interner::new();
        let (a, b, x, y, _d) = (
            it.intern("A"),
            it.intern("B"),
            it.intern("X"),
            it.intern("Y"),
            it.intern("D"),
        );
        let mut sub_super: Vec<HashSet<u32>> = vec![HashSet::default(); it.len()];
        sub_super[a as usize].insert(x);
        sub_super[b as usize].insert(y);
        let residual = clauses(&format!(
            "[{}]",
            cl(&[c("D", "x")], &[c("A", "x"), c("B", "x")])
        ));
        assert_eq!(hoist_residual_disjuncts(&residual, &it, &mut sub_super), 0);
    }

    #[test]
    fn cert_checks_range_clause_over_edges() {
        // EL: A ⊑ ∃R.B (pair of half-clauses). Residual range: R(x,y) → C(y).
        // Fails without B ⊑ C, passes with it.
        let base = format!(
            "{},{}",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
        );
        let range = cl(&[r("R", "x", "y")], &[c("C", "y")]);
        let cs_fail = clauses(&format!("[{},{}]", base, range));
        assert!(classify_inner(cs_fail, CertMode::Check, false).is_none());
        let cs_pass = clauses(&format!(
            "[{},{},{}]",
            base,
            range,
            cl(&[c("B", "x")], &[c("C", "x")]),
        ));
        let res =
            classify_inner(cs_pass, CertMode::Check, false).expect("range satisfied by B ⊑ C");
        assert!(subs_of(&res, "B").contains(&"C".to_string()));
    }

    #[test]
    fn cert_checks_cardinality_eq_head() {
        // EL: A ⊑ ∃R.B and A ⊑ ∃R.C. Residual (≤1 R): R(x,y) ∧ R(x,z) → y = z.
        // Two distinct successors violate it.
        let cs = clauses(&format!(
            "[{},{},{},{},{}]",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "g")]),
            cl(&[c("A", "x")], &[cf("C", "g", "x")]),
            format!(
                "{{\"body\":[{},{}],\"head\":[{{\"kind\":\"eq\",\"left\":{},\"right\":{}}}]}}",
                r("R", "x", "y"),
                r("R", "x", "z"),
                v("y"),
                v("z")
            ),
        ));
        assert!(classify_inner(cs, CertMode::Check, false).is_none());
        // With a single successor the functionality constraint holds.
        let cs1 = clauses(&format!(
            "[{},{},{}]",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            format!(
                "{{\"body\":[{},{}],\"head\":[{{\"kind\":\"eq\",\"left\":{},\"right\":{}}}]}}",
                r("R", "x", "y"),
                r("R", "x", "z"),
                v("y"),
                v("z")
            ),
        ));
        let res =
            classify_inner(cs1, CertMode::Check, false).expect("functional with one successor");
        assert!(subs_of(&res, "A").is_empty() || !res.inconsistent);
    }

    #[test]
    fn cert_keeps_distinct_skolem_witnesses_with_the_same_filler() {
        // A ≥2 R.B normalises to two R/B witness pairs plus a constraint that
        // rejects interpretations where the two skolem functions coincide.
        // Their common filler concept B must not collapse the two witnesses.
        let distinct = format!(
            "{{\"body\":[{},{{\"kind\":\"eq\",\"left\":{{\"kind\":\"fun\",\"function\":\"f\",\"arg\":{}}},\"right\":{{\"kind\":\"fun\",\"function\":\"g\",\"arg\":{}}}}}],\"head\":[]}}",
            c("A", "x"),
            v("x"),
            v("x")
        );
        let cs = clauses(&format!(
            "[{},{},{},{},{}]",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "g")]),
            cl(&[c("A", "x")], &[cf("B", "g", "x")]),
            distinct,
        ));
        let res = classify_inner(cs.clone(), CertMode::Check, false)
            .expect("same-filler skolem witnesses remain distinct");
        assert!(!res.inconsistent);
        assert!(!subs_of(&res, "A").contains(&"owl:Nothing".to_string()));
        assert!(
            classify_inner(cs, CertMode::Repair, false).is_some(),
            "repair mode must preserve the same witness interpretation"
        );
    }

    #[test]
    fn residual_source_variables_cannot_alias_function_pin_slots() {
        // The source variable is deliberately named exactly like the Skolem
        // function. They inhabit different namespaces: pinning x(·) must not
        // pin the universally quantified source variable `x`.
        let cs = clauses(&format!(
            "[{},{},{}]",
            cl(&[c("A", "u")], &[rf("R", "u", "x")]),
            cl(&[c("A", "u")], &[cf("B", "x", "u")]),
            cl(&[c("A", "x")], &[cf("C", "x", "u")]),
        ));
        let mut interner = Interner::new();
        let (mut nfs, residual, skolem_target) =
            to_nf(&cs, &mut interner).expect("normalizable EL prefix");
        assert_eq!(residual.len(), 1);
        let compiled = compile_residual(&residual, &mut interner, &mut nfs, &skolem_target)
            .expect("supported residual");
        assert_eq!(compiled[0].nvars, 2);
        assert_eq!(compiled[0].pins.len(), 1);
        assert_ne!(compiled[0].pins[0].0, 0, "source slot must remain unpinned");
        assert!(matches!(compiled[0].body[0], RAtom::C { v: 0, .. }));
    }

    #[test]
    fn lean_residual_compilation_payload_accepts_and_tampering_fails() {
        let cs = clauses(&format!(
            "[{},{},{}]",
            cl(&[c("A", "u")], &[rf("R", "u", "x")]),
            cl(&[c("A", "u")], &[cf("B", "x", "u")]),
            cl(&[c("A", "x")], &[cf("C", "x", "u")]),
        ));
        let mut interner = Interner::new();
        let (mut nfs, residual, skolem_target) =
            to_nf(&cs, &mut interner).expect("normalizable EL prefix");
        let compiled = compile_residual(&residual, &mut interner, &mut nfs, &skolem_target)
            .expect("supported residual");
        let payloads = build_lean_residual_compilations(&residual, &compiled, &interner)
            .expect("exact residual payload");
        assert_eq!(payloads.len(), 1);
        assert_eq!(payloads[0].origins.len(), payloads[0].variable_count);
        let json = serde_json::to_string(&payloads[0]).expect("payload JSON");
        assert!(json.contains("\"source\""));
        assert!(json.contains("\"function\""));

        let Some(checker) = std::env::var_os("KM_ELC_TEST_LEAN_CHECKER") else {
            return;
        };
        let path = std::env::temp_dir().join(format!(
            "km-elc-residual-cert-{}-{}.json",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let run = |payload: &LeanResidualCompilation| {
            std::fs::write(&path, serde_json::to_vec(payload).unwrap()).unwrap();
            std::process::Command::new(&checker)
                .args(["--residual", &interner.len().to_string()])
                .arg(&path)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .expect("run Lean residual checker")
                .success()
        };
        assert!(run(&payloads[0]), "exact Rust compilation must be accepted");

        let mut pin_tamper = payloads[0].clone();
        pin_tamper.pins[0].0 = 0;
        assert!(!run(&pin_tamper), "pin mutation must fail closed");

        let mut origin_tamper = payloads[0].clone();
        origin_tamper.origins[0] = LeanResidualOrigin::Function {
            function: 0,
            witness: 0,
        };
        assert!(!run(&origin_tamper), "origin mutation must fail closed");
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn cert_bails_on_nominal_terms_before_saturation() {
        // ind terms are not modelled: classify must return None (context engine).
        let cs = clauses(
            "[{\"body\":[],\"head\":[{\"kind\":\"concept\",\"concept\":\"A\",\
              \"term\":{\"kind\":\"ind\",\"name\":\"a\"}}]}]",
        );
        assert!(classify_inner(cs, CertMode::Check, false).is_none());
    }

    #[test]
    fn pure_el_unchanged() {
        // No residual: behaves exactly as before.
        let cs = clauses(&format!(
            "[{},{}]",
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[c("B", "x")], &[c("C", "x")]),
        ));
        let res = classify_inner(cs, CertMode::Check, false).expect("plain EL");
        let a = subs_of(&res, "A");
        assert!(a.contains(&"B".to_string()) && a.contains(&"C".to_string()));
    }

    #[test]
    fn cert_handles_empty_head_constraint_over_edges() {
        // Residual constraint: A(x) ∧ R(x,y) ∧ D(y) → ⊥ (no head). Satisfied
        // when no A-node has an R-successor in D; violated when one exists.
        let base = format!(
            "{},{}",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
        );
        let constraint = format!(
            "{{\"body\":[{},{},{}],\"head\":[]}}",
            c("A", "x"),
            r("R", "x", "y"),
            c("D", "y")
        );
        let res = classify_inner(
            clauses(&format!("[{},{}]", base, constraint)),
            CertMode::Check,
            false,
        )
        .expect("constraint body unsatisfied: certificate passes");
        assert!(!res.inconsistent);
        // Now make the successor a D: the constraint is violated in the model.
        let cs_fail = clauses(&format!(
            "[{},{},{}]",
            base,
            constraint,
            cl(&[c("B", "x")], &[c("D", "x")]),
        ));
        assert!(classify_inner(cs_fail, CertMode::Check, false).is_none());
    }

    // ----- repair-mode certificate -----

    #[test]
    fn repair_passes_on_inert_covering_disjunction() {
        // ⊤ → A ∨ B (covering), A and B otherwise unconstrained, EL: C ⊑ D.
        // The plain check fails (live disjunction); repair builds the
        // choose-A and choose-B models, whose intersection adds nothing, so
        // the EL answer is certified exact.
        let cs = clauses(&format!(
            "[{},{}]",
            cl(&[], &[c("A", "x"), c("B", "x")]),
            cl(&[c("C", "x")], &[c("D", "x")]),
        ));
        assert!(classify_inner(cs.clone(), CertMode::Check, false).is_none());
        let res = classify_inner(cs, CertMode::Repair, false).expect("repair certifies");
        assert!(subs_of(&res, "C").contains(&"D".to_string()));
        // The choices must not leak into the answer.
        assert!(!subs_of(&res, "C").contains(&"A".to_string()));
        assert!(!subs_of(&res, "C").contains(&"B".to_string()));
        assert!(!res.inconsistent);
    }

    #[test]
    fn repair_fails_when_disjunction_forces_subsumption() {
        // ⊤ → A ∨ B with A ⊑ D and B ⊑ D entails C ⊑ D for every class C,
        // which EL completion cannot derive: D survives in the intersection at
        // the C node, so C must NOT be answered by the certificate — it is
        // either handed to the context engine as unresolved residue (partial
        // verdict) or the whole certificate fails.
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[], &[c("A", "x"), c("B", "x")]),
            cl(&[c("A", "x")], &[c("D", "x")]),
            cl(&[c("B", "x")], &[c("D", "x")]),
            cl(&[c("C", "x")], &[c("C", "x")]),
        ));
        match classify_inner(cs, CertMode::Repair, false) {
            None => {}
            Some(res) => {
                assert!(
                    res.unresolved.iter().any(|n| n == "C"),
                    "C must be unresolved, got {:?}",
                    res.unresolved
                );
                assert!(
                    !res.subsumptions.contains_key("C"),
                    "C must not be answered by the certificate"
                );
            }
        }
    }

    #[test]
    fn repair_fails_when_both_choices_force_bottom() {
        // ⊤ → A ∨ B with both disjuncts unsatisfiable: the ontology is
        // inconsistent but EL completion does not see it. Every repair choice
        // kills every node, so no pass model can witness C's satisfiability:
        // C must be unresolved residue (the engine then detects the
        // inconsistency) or the certificate must fail outright.
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[], &[c("A", "x"), c("B", "x")]),
            cl(&[c("A", "x")], &[]),
            cl(&[c("B", "x")], &[]),
            cl(&[c("C", "x")], &[c("C", "x")]),
        ));
        match classify_inner(cs, CertMode::Repair, false) {
            None => {}
            Some(res) => {
                assert!(
                    res.unresolved.iter().any(|n| n == "C"),
                    "C must be unresolved, got {:?}",
                    res.unresolved
                );
                assert!(
                    !res.subsumptions.contains_key("C"),
                    "C must not be answered by the certificate"
                );
            }
        }
    }

    #[test]
    fn repair_handles_inert_inverse_bridge_via_edge_addition() {
        // EL: A ⊑ ∃R.B. Residual inverse bridge R(x,y) → S(y,x) with S unused:
        // repair adds the S-edge, nothing else fires, both pass models agree
        // with the base, certificate passes with the EL answer.
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[c("C", "x")], &[c("D", "x")]),
        ));
        assert!(classify_inner(cs.clone(), CertMode::Check, false).is_none());
        let res = classify_inner(cs, CertMode::Repair, false).expect("edge repair certifies");
        assert!(subs_of(&res, "C").contains(&"D".to_string()));
        assert!(!res.inconsistent);
    }

    #[test]
    fn repair_shortcuts_when_base_model_already_complete() {
        // Residual already satisfied by the canonical model: repair mode must
        // pass without needing a second pass (adds == 0 shortcut).
        let cs = clauses(&format!(
            "[{},{}]",
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[c("A", "x")], &[c("B", "x"), c("D", "x")]),
        ));
        let res = classify_inner(cs, CertMode::Repair, false).expect("base model complete");
        assert!(subs_of(&res, "A").contains(&"B".to_string()));
    }

    // ----- cardinality-aware partition assignment -----

    /// Emit an exhaustive disjoint qualified-cardinality partition in the shape
    /// the normaliser produces: a covering disjunction between a `≤1 R.C`
    /// definer `lo` and its complement `hi`, the two definers disjoint, and `n`
    /// subjects each carrying two `R`-successors in `C` that a `≥2` clause pins
    /// apart. Taking the `lo` side at such a subject is locally unsatisfiable.
    ///
    /// `lo_first` places the at-most definer first in the cover, which is the
    /// order the forward-polarity pass tries first; `false` places it last,
    /// which is the order the reverse-polarity pass tries first.
    fn card_partition(
        out: &mut Vec<String>,
        tag: &str,
        lo: &str,
        hi: &str,
        lo_first: bool,
        n: usize,
    ) {
        let role = format!("R{tag}");
        let (filler, fa, fb) = (format!("C{tag}"), format!("C{tag}a"), format!("C{tag}b"));
        out.push(if lo_first {
            cl(&[], &[c(lo, "x"), c(hi, "x")])
        } else {
            cl(&[], &[c(hi, "x"), c(lo, "x")])
        });
        out.push(cl(&[c(lo, "x"), c(hi, "x")], &[]));
        // `lo ⊑ ≤1 R.C`
        out.push(cl(
            &[
                c(lo, "x"),
                r(&role, "x", "y1"),
                c(&filler, "y1"),
                r(&role, "x", "y2"),
                c(&filler, "y2"),
            ],
            &[eqv("y1", "y2")],
        ));
        // two distinct fillers, so the two existentials stay distinct NF3 rows
        out.push(cl(&[c(&fa, "x")], &[c(&filler, "x")]));
        out.push(cl(&[c(&fb, "x")], &[c(&filler, "x")]));
        for i in 0..n {
            let (subj, sa, sb) = (
                format!("A{tag}{i}"),
                format!("f{tag}{i}a"),
                format!("f{tag}{i}b"),
            );
            out.push(cl(&[c(&subj, "x")], &[rf(&role, "x", &sa)]));
            out.push(cl(&[c(&subj, "x")], &[cf(&fa, &sa, "x")]));
            out.push(cl(&[c(&subj, "x")], &[rf(&role, "x", &sb)]));
            out.push(cl(&[c(&subj, "x")], &[cf(&fb, &sb, "x")]));
            // `subj ⊑ ≥2 R.C`: the two canonical witnesses are pinned apart
            out.push(cl(&[c(&subj, "x"), eqf(&sa, &sb, "x")], &[]));
        }
    }

    #[test]
    fn repair_assigns_cardinality_partitions_without_merging_pinned_witnesses() {
        // Two independent partitions with opposite cover orientations, so
        // neither polarity seed can reach a model by trying the other side
        // first. Each partition has more subjects than the restart budget, so a
        // search that charges one conflict-driven restart per subject runs out
        // before it can ban them all. The assignment must instead see, at each
        // subject, that the at-most side is locally unsatisfiable — two
        // qualifying successors that a `≥2` clause pins apart, against a bound
        // of one — and take the other side directly.
        let n = REPAIR_RESTART_CAP + 6;
        let mut parts: Vec<String> = Vec::new();
        card_partition(&mut parts, "p", "Q_1", "Q_2", true, n);
        card_partition(&mut parts, "q", "Q_3", "Q_4", false, n);
        // a named EL consequence the certificate has to keep answering
        parts.push(cl(&[c("E", "x")], &[c("F", "x")]));
        let cs = clauses(&format!("[{}]", parts.join(",")));

        // the covering disjunctions are live, so the plain check cannot pass
        assert!(classify_inner(cs.clone(), CertMode::Check, false).is_none());
        let res = classify_inner(cs, CertMode::Repair, false).expect("repair certifies");
        assert!(subs_of(&res, "E").contains(&"F".to_string()));
        assert!(!res.inconsistent);
        assert!(
            res.unresolved.is_empty(),
            "partition assignment left residue: {:?}",
            res.unresolved
        );
        // the side choices are definers and must not leak into the answer
        for subj in [format!("Ap{}", n - 1), format!("Aq{}", n - 1)] {
            let supers = subs_of(&res, &subj);
            assert!(
                !supers.iter().any(|s| s.starts_with("Q_")),
                "definer leaked into {subj}: {supers:?}"
            );
        }
    }

    #[test]
    fn repair_still_merges_at_most_successors_that_are_not_pinned_apart() {
        // The same `≤1 R.C` bound, but with no `≥2` clause pinning the two
        // witnesses apart. Identifying them is legal and is the only way to
        // satisfy the bound, so the search must still do it. This is the
        // over-refusal guard: refusing every merge would also "avoid" conflicts
        // and would silently cost the certificate.
        let cs = clauses(&format!(
            "[{},{},{},{},{},{},{},{}]",
            cl(&[c("Ca", "x")], &[c("C", "x")]),
            cl(&[c("Cb", "x")], &[c("C", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "fa")]),
            cl(&[c("A", "x")], &[cf("Ca", "fa", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "fb")]),
            cl(&[c("A", "x")], &[cf("Cb", "fb", "x")]),
            cl(
                &[
                    c("A", "x"),
                    r("R", "x", "y1"),
                    c("C", "y1"),
                    r("R", "x", "y2"),
                    c("C", "y2"),
                ],
                &[eqv("y1", "y2")],
            ),
            cl(&[c("E", "x")], &[c("F", "x")]),
        ));
        assert!(classify_inner(cs.clone(), CertMode::Check, false).is_none());
        let res = classify_inner(cs, CertMode::Repair, false).expect("merge repair certifies");
        assert!(subs_of(&res, "E").contains(&"F".to_string()));
        assert!(!res.inconsistent);
    }

    #[test]
    fn repair_fails_closed_when_both_partition_sides_are_impossible() {
        // The at-most side is locally unsatisfiable at `A` (two pinned-apart
        // successors against a bound of one) and the other side is
        // unsatisfiable outright. No pass model can witness `A`, so the
        // certificate must decline: `A` is either unresolved residue for the
        // context engine or the whole certificate fails. It must never be
        // answered, and the guidance must not turn "no legal choice" into a
        // silently accepted model.
        // `A ⊑ ≥2 R.C` with the witnesses pinned apart, plus the partition
        let core = format!(
            "{},{},{},{},{},{},{}",
            cl(&[c("Ca", "x")], &[c("C", "x")]),
            cl(&[c("Cb", "x")], &[c("C", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "fa")]),
            cl(&[c("A", "x")], &[cf("Ca", "fa", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "fb")]),
            cl(&[c("A", "x")], &[cf("Cb", "fb", "x")]),
            cl(&[c("A", "x"), eqf("fa", "fb", "x")], &[]),
        );
        let at_most = |guard: &str| {
            cl(
                &[
                    c(guard, "x"),
                    r("R", "x", "y1"),
                    c("C", "y1"),
                    r("R", "x", "y2"),
                    c("C", "y2"),
                ],
                &[eqv("y1", "y2")],
            )
        };
        // (a) the at-most side is locally unsatisfiable, the other side is dead
        let dead_partner = clauses(&format!(
            "[{},{},{},{},{}]",
            core,
            cl(&[], &[c("Q_1", "x"), c("Q_2", "x")]),
            cl(&[c("Q_1", "x"), c("Q_2", "x")], &[]),
            cl(&[c("Q_2", "x")], &[]),
            at_most("Q_1"),
        ));
        // (b) no partition at all: `≥2 R.C` against `≤1 R.C` on the same
        // subject is inconsistent, and no repair choice exists to blame, so
        // the certificate has to fail outright rather than report `A` satisfiable
        let no_choice = clauses(&format!("[{},{}]", core, at_most("A")));
        for cs in [dead_partner, no_choice] {
            match classify_inner(cs, CertMode::Repair, false) {
                None => {}
                Some(res) => {
                    assert!(
                        res.unresolved.iter().any(|nm| nm == "A"),
                        "A must be unresolved, got {:?}",
                        res.unresolved
                    );
                    assert!(
                        !res.subsumptions.contains_key("A"),
                        "A must not be answered by the certificate"
                    );
                }
            }
        }
    }

    // ----- cardinality guidance, in isolation -----

    fn rc(nvars: usize, body: Vec<RAtom>, head: Vec<RAtom>, pins: Vec<(usize, u32)>) -> RClause {
        RClause {
            nvars,
            origins: (0..nvars)
                .map(|name| ROrigin::Source {
                    source: format!("v{name}"),
                    name,
                })
                .collect(),
            body,
            head,
            pins,
        }
    }

    /// `≤1 R.C` guarded by concept `g`, over variables `x, y1, y2`.
    fn at_most_one(g: u32, role: u32, filler: u32) -> RClause {
        rc(
            3,
            vec![
                RAtom::C { cid: g, v: 0 },
                RAtom::R {
                    rid: role,
                    s: 0,
                    t: 1,
                },
                RAtom::C { cid: filler, v: 1 },
                RAtom::R {
                    rid: role,
                    s: 0,
                    t: 2,
                },
                RAtom::C { cid: filler, v: 2 },
            ],
            vec![RAtom::Eq { s: 1, t: 2 }],
            vec![],
        )
    }

    /// `g(x) ∧ f_a(x) ≈ f_b(x) → ⊥`, pinning witness nodes `a` and `b` apart.
    fn pin_apart(g: u32, a: u32, b: u32) -> RClause {
        rc(
            3,
            vec![RAtom::C { cid: g, v: 0 }, RAtom::Eq { s: 1, t: 2 }],
            vec![],
            vec![(1, a), (2, b)],
        )
    }

    /// A structure with `n` nodes, the given labels, and the given edges.
    fn state_of(n: usize, labels: &[(u32, &[u32])], edges: &[(u32, u32, u32)]) -> State {
        let mut st = State {
            sub_super: vec![HashSet::default(); n],
            edges: vec![HashSet::default(); n],
            in_by_role: HashMap::default(),
            in_roles: vec![Vec::new(); n],
            prop: HashMap::default(),
            worklist: VecDeque::new(),
            sub_journal: None,
            edge_epoch: 0,
        };
        for (node, ls) in labels {
            for l in *ls {
                st.sub_super[*node as usize].insert(*l);
            }
        }
        for (s, r, t) in edges {
            if st.edges[*s as usize].insert((*r, *t)) {
                let parents = st.in_by_role.entry((*t, *r)).or_default();
                if parents.is_empty() {
                    st.in_roles[*t as usize].push(*r);
                }
                parents.push(*s);
            }
        }
        st
    }

    #[test]
    fn card_guide_reads_bounds_and_pins_off_clause_wiring() {
        let guide = CardGuide::new(&[at_most_one(7, 3, 9), pin_apart(7, 11, 12)]);
        assert_eq!(guide.bounds.len(), 1);
        assert_eq!(guide.bounds[0].bound, 1);
        assert_eq!(guide.bounds[0].role, 3);
        assert_eq!(guide.bounds[0].fillers, vec![9]);
        assert_eq!(guide.bounds[0].guards, vec![7]);
        assert_eq!(
            guide.by_guard.get(&7).map(Vec::as_slice),
            Some(&[0usize][..])
        );
        assert_eq!(guide.pinned_apart, vec![(11, 12)]);
        assert!(!guide.is_inert());

        // an unguarded bound is active everywhere, so no choice activates it
        let unguarded = CardGuide::new(&[rc(
            3,
            vec![
                RAtom::R { rid: 3, s: 0, t: 1 },
                RAtom::R { rid: 3, s: 0, t: 2 },
            ],
            vec![RAtom::Eq { s: 1, t: 2 }],
            vec![],
        )]);
        assert_eq!(unguarded.bounds.len(), 1);
        assert!(unguarded.bounds[0].fillers.is_empty());
        assert!(unguarded.by_guard.is_empty());
        assert!(unguarded.is_inert());

        // nothing recognised at all leaves the search untouched
        let plain = CardGuide::new(&[rc(
            2,
            vec![RAtom::C { cid: 1, v: 0 }],
            vec![RAtom::C { cid: 2, v: 0 }],
            vec![],
        )]);
        assert!(plain.is_inert());
    }

    #[test]
    fn recognize_at_most_rejects_near_miss_shapes() {
        // `≤2 R.C`: three successors, all three unordered pairs in the head
        let three = |pairs: Vec<RAtom>| {
            rc(
                4,
                vec![
                    RAtom::C { cid: 7, v: 0 },
                    RAtom::R { rid: 3, s: 0, t: 1 },
                    RAtom::C { cid: 9, v: 1 },
                    RAtom::R { rid: 3, s: 0, t: 2 },
                    RAtom::C { cid: 9, v: 2 },
                    RAtom::R { rid: 3, s: 0, t: 3 },
                    RAtom::C { cid: 9, v: 3 },
                ],
                pairs,
                vec![],
            )
        };
        let full = vec![
            RAtom::Eq { s: 1, t: 2 },
            RAtom::Eq { s: 1, t: 3 },
            RAtom::Eq { s: 2, t: 3 },
        ];
        let b = recognize_at_most(&three(full.clone())).expect("≤2 R.C");
        assert_eq!(
            (b.bound, b.role, b.fillers, b.guards),
            (2, 3, vec![9], vec![7])
        );

        // a head missing one pair is not an at-most bound: it constrains only
        // the pairs it names, so a node over the bound need not be repairable
        // by identifying any pair the clause happens to list
        assert!(recognize_at_most(&three(full[..2].to_vec())).is_none());
        // a duplicated pair, and a reflexive equality, are both malformed
        let mut dup = full.clone();
        dup.push(RAtom::Eq { s: 2, t: 1 });
        assert!(recognize_at_most(&three(dup)).is_none());
        let mut refl = full.clone();
        refl.push(RAtom::Eq { s: 1, t: 1 });
        assert!(recognize_at_most(&three(refl)).is_none());

        let mutate = |f: &dyn Fn(&mut RClause)| {
            let mut c = at_most_one(7, 3, 9);
            f(&mut c);
            recognize_at_most(&c)
        };
        // a pinned clause is a witness constraint, not a bound over free vars
        assert!(mutate(&|c| c.pins.push((1, 11))).is_none());
        // two different roles on the two successor edges
        assert!(mutate(&|c| c.body[3] = RAtom::R { rid: 4, s: 0, t: 2 }).is_none());
        // two different sources
        assert!(mutate(&|c| c.body[3] = RAtom::R { rid: 3, s: 2, t: 1 }).is_none());
        // successors with different fillers: a different constraint
        assert!(mutate(&|c| c.body[4] = RAtom::C { cid: 10, v: 2 }).is_none());
        // a guard on something other than the source
        assert!(mutate(&|c| c.body[0] = RAtom::C { cid: 7, v: 3 }).is_none());
        // an equality in the body
        assert!(mutate(&|c| c.body.push(RAtom::Eq { s: 0, t: 1 })).is_none());
        // a successor with no edge to the source
        assert!(mutate(&|c| {
            c.body.remove(3);
        })
        .is_none());
        // an empty head is a ⊥-clause, not a bound
        assert!(mutate(&|c| c.head.clear()).is_none());
        // a concept head is a cover, not a bound
        assert!(mutate(&|c| c.head = vec![RAtom::C { cid: 9, v: 0 }]).is_none());
    }

    #[test]
    fn recognize_distinct_pins_rejects_near_miss_shapes() {
        assert_eq!(
            recognize_distinct_pins(&pin_apart(7, 11, 12)),
            Some((11, 12))
        );
        let mutate = |f: &dyn Fn(&mut RClause)| {
            let mut c = pin_apart(7, 11, 12);
            f(&mut c);
            recognize_distinct_pins(&c)
        };
        // a non-empty head does not force the equality to be false
        assert!(mutate(&|c| c.head.push(RAtom::C { cid: 9, v: 0 })).is_none());
        // two equalities: falsity needs only ONE of them, so neither is pinned
        assert!(mutate(&|c| c.body.push(RAtom::Eq { s: 0, t: 1 })).is_none());
        // an unpinned side denotes no fixed node
        assert!(mutate(&|c| c.pins.retain(|&(v, _)| v != 2)).is_none());
        // both sides pinned to the SAME node: already violated, pins nothing
        assert!(mutate(&|c| c.pins = vec![(1, 11), (2, 11)]).is_none());
        // no equality at all
        assert!(mutate(&|c| c.body.retain(|a| !matches!(a, RAtom::Eq { .. }))).is_none());
    }

    #[test]
    fn card_guide_refuses_pinned_merges_modulo_the_quotient() {
        let guide = CardGuide::new(&[pin_apart(7, 11, 12)]);
        let mut repr: Vec<u32> = (0..16).collect();
        let mut round = CardRound::default();
        round.resync(&guide, &mut repr);

        assert!(!guide.merge_legal(&round, &mut repr, 11, 12));
        assert!(!guide.merge_legal(&round, &mut repr, 12, 11));
        assert!(guide.merge_legal(&round, &mut repr, 11, 13));
        // a node already identified with itself is always mergeable
        assert!(guide.merge_legal(&round, &mut repr, 11, 11));

        // fold 13 into 11: the pin now separates 13's class from 12 as well
        repr[13] = 11;
        round.resync(&guide, &mut repr);
        assert!(!guide.merge_legal(&round, &mut repr, 13, 12));
        assert!(guide.merge_legal(&round, &mut repr, 13, 14));
    }

    #[test]
    fn card_guide_demotes_only_over_full_all_pinned_choices() {
        // node 0 --R--> {1, 2}, both in filler 9; bound is ≤1 R.9 guarded by 7
        let guide = CardGuide::new(&[at_most_one(7, 3, 9), pin_apart(7, 1, 2)]);
        let st = state_of(
            8,
            &[(1, &[9]), (2, &[9]), (4, &[9]), (5, &[9])],
            &[(0, 3, 1), (0, 3, 2), (6, 3, 4)],
        );
        let mut repr: Vec<u32> = (0..8).collect();
        let mut round = CardRound::default();
        round.resync(&guide, &mut repr);

        // two qualifying successors, pinned apart, against a bound of one
        assert!(guide.locally_incompatible(&mut round, &st, &mut repr, 0, 7));
        assert_eq!(round.demoted, 1);
        // node 6 has one qualifying successor: the bound is satisfiable there
        assert!(!guide.locally_incompatible(&mut round, &st, &mut repr, 6, 7));
        // a concept that guards no bound is never demoted
        assert!(!guide.locally_incompatible(&mut round, &st, &mut repr, 0, 8));

        // same shape, but the successors are NOT pinned apart: identifying them
        // satisfies the bound, so the choice stays available
        let loose = CardGuide::new(&[at_most_one(7, 3, 9)]);
        let mut round = CardRound::default();
        round.resync(&loose, &mut repr);
        assert!(!loose.locally_incompatible(&mut round, &st, &mut repr, 0, 7));

        // successors that do not carry the filler are not counted
        let unqualified = state_of(8, &[(1, &[9])], &[(0, 3, 1), (0, 3, 2)]);
        let mut round = CardRound::default();
        round.resync(&guide, &mut repr);
        assert!(!guide.locally_incompatible(&mut round, &unqualified, &mut repr, 0, 7));

        // successors reached by a different role are not counted either
        let other_role = state_of(8, &[(1, &[9]), (2, &[9])], &[(0, 5, 1), (0, 5, 2)]);
        let mut round = CardRound::default();
        round.resync(&guide, &mut repr);
        assert!(!guide.locally_incompatible(&mut round, &other_role, &mut repr, 0, 7));

        // a second guard that does NOT hold at the node leaves the bound
        // inactive there, so choosing the first guard demotes nothing
        let two_guards = {
            let mut c = at_most_one(7, 3, 9);
            c.body.push(RAtom::C { cid: 13, v: 0 });
            CardGuide::new(&[c, pin_apart(7, 1, 2)])
        };
        let mut round = CardRound::default();
        round.resync(&two_guards, &mut repr);
        assert!(!two_guards.locally_incompatible(&mut round, &st, &mut repr, 0, 7));
        let guarded = state_of(
            8,
            &[(0, &[13]), (1, &[9]), (2, &[9])],
            &[(0, 3, 1), (0, 3, 2)],
        );
        let mut round = CardRound::default();
        round.resync(&two_guards, &mut repr);
        assert!(two_guards.locally_incompatible(&mut round, &guarded, &mut repr, 0, 7));
    }

    #[test]
    fn card_guide_counts_merged_successors_once() {
        // the two successors are pinned apart, but a merge has already folded
        // one into the other: the node is back inside its bound and the choice
        // must not be demoted
        let guide = CardGuide::new(&[at_most_one(7, 3, 9), pin_apart(7, 1, 2)]);
        let st = state_of(8, &[(1, &[9]), (2, &[9])], &[(0, 3, 1), (0, 3, 2)]);
        let mut repr: Vec<u32> = (0..8).collect();
        repr[2] = 1;
        let mut round = CardRound::default();
        round.resync(&guide, &mut repr);
        // the pin is already violated by the quotient, so it no longer
        // separates anything: `cert_round` is what reports that, not the guide
        assert!(round.apart.is_empty());
        assert!(!guide.locally_incompatible(&mut round, &st, &mut repr, 0, 7));
    }

    #[test]
    fn repair_rechecks_stale_cover_after_forced_residual() {
        // The inverse-position singleton is residual: every R-target must be A.
        // The same target also has the residual cover A ∨ B and A/B are
        // disjoint. A repair round can collect both violations at once. It must
        // apply the forced A first and then observe that the stale cover is
        // already true, rather than adding B in the reverse-polarity pass.
        let cs = clauses(&format!(
            "[{},{},{},{},{}]",
            cl(&[c("C", "x")], &[rf("R", "x", "f")]),
            cl(&[c("C", "x")], &[cf("D", "f", "x")]),
            cl(&[r("R", "x", "y")], &[c("A", "y")]),
            cl(&[], &[c("A", "x"), c("B", "x")]),
            cl(&[c("A", "x"), c("B", "x")], &[]),
        ));
        let res = classify_inner(cs, CertMode::Repair, false).expect("repair certifies");
        assert!(!res.inconsistent);
    }

    // -----------------------------------------------------------------------
    // ObjectPropertyDomain (`∃R.⊤ ⊑ D`) is inside EL++
    // -----------------------------------------------------------------------

    #[test]
    fn domain_axiom_is_decided_without_a_certificate() {
        // `∃R.⊤ ⊑ D` together with `A ⊑ ∃R.B` entails `A ⊑ D`. The clause set
        // must screen as pure EL and the cert-off worker must answer it: this
        // is the shape ObjectPropertyDomain normalises to, and parking it in
        // the residual sends the whole ontology to the context engine.
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[r("R", "x", "y")], &[c("D", "x")]),
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[c("D", "x")], &[c("E", "x")]),
        ));
        assert!(is_pure_el_shape(&cs), "a domain axiom is inside EL++");
        let res = classify_inner(cs, CertMode::Off, false).expect("pure EL, no residual");
        let a = subs_of(&res, "A");
        assert!(a.contains(&"D".to_string()), "A ⊑ D missing: {a:?}");
        // and the conclusion keeps flowing through the ordinary NF1 closure
        assert!(a.contains(&"E".to_string()), "A ⊑ E missing: {a:?}");
    }

    #[test]
    fn role_body_with_head_off_the_source_is_not_a_domain_axiom() {
        // `R(x,y) → D(y)` is `∃R⁻.⊤ ⊑ D` and `R(x,x) → D(x)` is a self
        // restriction. Reading either as `∃R.⊤ ⊑ D` would be unsound, so both
        // must stay in the residual and the cert-off worker must decline.
        for shape in [
            cl(&[r("R", "x", "y")], &[c("D", "y")]),
            cl(&[r("R", "x", "x")], &[c("D", "x")]),
        ] {
            let cs = clauses(&format!(
                "[{},{},{}]",
                shape,
                cl(&[c("A", "x")], &[rf("R", "x", "f")]),
                cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            ));
            assert!(!is_pure_el_shape(&cs), "{shape} must not screen as EL");
            assert!(
                classify_inner(cs, CertMode::Off, false).is_none(),
                "{shape} must defer to the context engine"
            );
        }
    }

    // ----- Edge-NF4 in-place `prop` iteration (`fire_edge_nf4`) -----

    /// An `Idx` holding only NF4 axioms `∃role.filler ⊑ sup` (given as
    /// `(role, filler, sup)` triples) plus the identity role hierarchy every
    /// edge role needs. Vectors are role-sorted, as `build_idx` guarantees for
    /// the Sub-rule's `partition_point` join.
    fn nf4_only_idx(nf4: &[(u32, u32, u32)], nroles: u32) -> Idx {
        let mut nf4_by_filler: HashMap<u32, Vec<(u32, u32)>> = HashMap::default();
        for &(role, filler, sup) in nf4 {
            nf4_by_filler.entry(filler).or_default().push((role, sup));
        }
        for axs in nf4_by_filler.values_mut() {
            axs.sort_unstable();
        }
        let role_sub = (0..nroles)
            .map(|r| {
                let mut s: HashSet<u32> = HashSet::default();
                s.insert(r);
                s
            })
            .collect();
        Idx {
            nf1_by_sub: HashMap::default(),
            nf2_by_sub: HashMap::default(),
            nf3_by_sub: HashMap::default(),
            nf4_by_filler,
            nf5_subs: HashSet::default(),
            nf7_by_pair: HashMap::default(),
            role_sub,
            reflexive_closed: HashSet::default(),
        }
    }

    fn blank_state(n: usize) -> State {
        State {
            sub_super: vec![HashSet::default(); n],
            edges: vec![HashSet::default(); n],
            in_by_role: HashMap::default(),
            in_roles: vec![Vec::new(); n],
            prop: HashMap::default(),
            worklist: VecDeque::new(),
            sub_journal: None,
            edge_epoch: 0,
        }
    }

    #[test]
    fn edge_nf4_fires_when_edge_arrives_after_propagation() {
        // ∃R.B ⊑ E. A ⊑ B is completed FIRST, registering prop[(A,R)] = [E]
        // with no edge present; the later edge (X,R,A) must fire the stored
        // propagation edge-side.
        const R: u32 = 0;
        const A: u32 = 2;
        const B: u32 = 3;
        const E: u32 = 4;
        const X: u32 = 5;
        let idx = nf4_only_idx(&[(R, B, E)], 1);
        let mut st = blank_state(6);
        st.add_sub(A, B);
        run(&idx, &mut st, &mut Prof::default());
        assert_eq!(st.prop.get(&(A, R)), Some(&vec![E]));
        assert!(!st.sub_super[X as usize].contains(&E));
        st.add_edge(X, R, A);
        run(&idx, &mut st, &mut Prof::default());
        assert!(
            st.sub_super[X as usize].contains(&E),
            "edge-side join must fire the pre-registered propagation"
        );
    }

    #[test]
    fn edge_nf4_fires_when_propagation_arrives_after_edge() {
        // Same axioms, opposite creation order: the edge (X,R,A) is completed
        // first (nothing fires), then A ⊑ B arrives and the Sub-side backward
        // join over the backward links of A must produce X ⊑ E.
        const R: u32 = 0;
        const A: u32 = 2;
        const B: u32 = 3;
        const E: u32 = 4;
        const X: u32 = 5;
        let idx = nf4_only_idx(&[(R, B, E)], 1);
        let mut st = blank_state(6);
        st.add_edge(X, R, A);
        run(&idx, &mut st, &mut Prof::default());
        assert!(!st.sub_super[X as usize].contains(&E));
        st.add_sub(A, B);
        run(&idx, &mut st, &mut Prof::default());
        assert!(
            st.sub_super[X as usize].contains(&E),
            "sub-side backward join must fire against the pre-existing edge"
        );
    }

    #[test]
    fn edge_nf4_self_edge_fires_bucket_that_grows_after_the_edge() {
        // Self-edge (A,R,A) processed while prop[(A,R)] = [E1]: the in-place
        // edge-side iteration yields A ⊑ E1, whose Sub item then grows the
        // SAME bucket (∃R.E1 ⊑ E2) and must still reach A ⊑ E2 sub-side.
        const R: u32 = 0;
        const A: u32 = 2;
        const E1: u32 = 3;
        const E2: u32 = 4;
        let idx = nf4_only_idx(&[(R, A, E1), (R, E1, E2)], 1);
        let mut st = blank_state(5);
        st.add_sub(A, A);
        run(&idx, &mut st, &mut Prof::default());
        assert_eq!(st.prop.get(&(A, R)), Some(&vec![E1]));
        st.add_edge(A, R, A);
        run(&idx, &mut st, &mut Prof::default());
        assert!(st.sub_super[A as usize].contains(&E1));
        assert!(st.sub_super[A as usize].contains(&E2));
        assert_eq!(st.prop.get(&(A, R)), Some(&vec![E1, E2]));
    }

    #[test]
    fn edge_nf4_self_edge_cascade_from_a_single_run() {
        // Everything seeded before one `run`: the self-edge and the cascade
        // ∃R.A ⊑ E1, ∃R.E1 ⊑ E2, ∃R.E2 ⊑ E3 interleave edge-side and
        // sub-side firings on the growing prop[(A,R)] bucket at c == d.
        const R: u32 = 0;
        const A: u32 = 2;
        const E1: u32 = 3;
        const E2: u32 = 4;
        const E3: u32 = 5;
        let idx = nf4_only_idx(&[(R, A, E1), (R, E1, E2), (R, E2, E3)], 1);
        let mut st = blank_state(6);
        st.add_sub(A, A);
        st.add_edge(A, R, A);
        run(&idx, &mut st, &mut Prof::default());
        for e in [E1, E2, E3] {
            assert!(st.sub_super[A as usize].contains(&e), "A ⊑ {e} missing");
        }
        assert_eq!(st.prop.get(&(A, R)), Some(&vec![E1, E2, E3]));
    }

    #[test]
    fn parallel_nf4_frontier_deduplicates_parent_conclusions_exactly() {
        const R: u32 = 0;
        const PARENT: u32 = 2;
        const E1: u32 = 3;
        const E2: u32 = 4;
        const FIRST_TARGET: u32 = 10;
        let idx = nf4_only_idx(&[(R, FIRST_TARGET, E1)], 1);
        let mut st = blank_state(300);
        for target in FIRST_TARGET..FIRST_TARGET + PAR_NF4_MIN_EDGES as u32 {
            st.prop.insert(
                (target, R),
                (0..128).map(|i| if i % 2 == 0 { E1 } else { E2 }).collect(),
            );
            st.worklist.push_back(Item::Edge(PARENT, R, target));
        }
        let mut prof = Prof::default();
        assert!(fire_edge_nf4_batch(&idx, &mut st, &mut prof, true));
        assert_eq!(prof.nf4_edge_scan, 128 * PAR_NF4_MIN_EDGES as u64);
        assert!(st.sub_super[PARENT as usize].contains(&E1));
        assert!(st.sub_super[PARENT as usize].contains(&E2));
        assert_eq!(st.sub_super[PARENT as usize].len(), 2);
        assert_eq!(
            st.worklist
                .iter()
                .filter(|item| matches!(item, Item::EdgeAfterNf4(..)))
                .count(),
            PAR_NF4_MIN_EDGES
        );
        assert_eq!(
            st.worklist
                .iter()
                .filter(|item| matches!(item, Item::Sub(PARENT, E1 | E2)))
                .count(),
            2
        );
    }

    #[test]
    fn sparse_nf4_frontier_declines_once_and_keeps_the_serial_join() {
        const R: u32 = 0;
        const PARENT: u32 = 2;
        const SUP: u32 = 3;
        const FIRST_TARGET: u32 = 10;
        let idx = nf4_only_idx(&[(R, FIRST_TARGET, SUP)], 1);
        let mut st = blank_state(300);
        for target in FIRST_TARGET..FIRST_TARGET + PAR_NF4_MIN_EDGES as u32 {
            st.prop.insert((target, R), vec![SUP]);
            st.worklist.push_back(Item::Edge(PARENT, R, target));
        }
        let mut prof = Prof::default();
        assert!(fire_edge_nf4_batch(&idx, &mut st, &mut prof, true));
        assert_eq!(prof.nf4_batch_calls, 0);
        assert!(st.worklist.iter().all(|item| matches!(item, Item::EdgeSerial(..))));
        run(&idx, &mut st, &mut prof);
        assert!(st.sub_super[PARENT as usize].contains(&SUP));
        assert_eq!(prof.nf4_edge_scan, PAR_NF4_MIN_EDGES as u64);
    }

    #[test]
    fn edge_nf4_closure_is_input_order_invariant() {
        // NF1 + NF3 + NF4 + a role inclusion + a genuine self-edge (C ⊑ ∃T.C):
        // permuting the input clauses flips which of {edge, propagation} is
        // created first at each context, and the closure must not change.
        let parts = [
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[c("B", "x")], &[c("C", "x")]),
            cl(&[r("R", "x", "y"), c("C", "y")], &[c("D", "x")]),
            cl(&[r("R", "x", "y"), c("B", "y")], &[c("G", "x")]),
            cl(&[c("C", "x")], &[rf("T", "x", "g")]),
            cl(&[c("C", "x")], &[cf("C", "g", "x")]),
            cl(&[r("T", "x", "y"), c("C", "y")], &[c("D", "x")]),
            cl(&[r("T", "x", "y"), c("D", "y")], &[c("H", "x")]),
            cl(&[r("R", "x", "y")], &[r("S", "x", "y")]),
            cl(&[r("S", "x", "y"), c("C", "y")], &[c("K", "x")]),
        ];
        let n = parts.len();
        let mut baseline: Option<std::collections::BTreeMap<String, Vec<String>>> = None;
        for rot in 0..n {
            let order: Vec<String> = (0..n).map(|i| parts[(i + rot) % n].clone()).collect();
            let cs = clauses(&format!("[{}]", order.join(",")));
            let res = classify_inner(cs, CertMode::Off, false).expect("pure EL");
            let map: std::collections::BTreeMap<String, Vec<String>> = res
                .subsumptions
                .iter()
                .map(|(k, v)| {
                    let mut sups = v.clone();
                    sups.sort();
                    (k.clone(), sups)
                })
                .collect();
            match &baseline {
                None => {
                    // Spot-check the joint conclusions once: the lifted-edge
                    // NF4 (A ⊑ K via R ⊑ S), the plain edge-side/sub-side join
                    // (A ⊑ D, A ⊑ G), and the self-edge cascade (C ⊑ D ⊑ H).
                    for (sub, sup) in [
                        ("A", "D"),
                        ("A", "G"),
                        ("A", "K"),
                        ("C", "D"),
                        ("C", "H"),
                        ("B", "H"),
                    ] {
                        assert!(
                            map.get(sub).is_some_and(|s| s.contains(&sup.to_string())),
                            "{sub} ⊑ {sup} missing: {:?}",
                            map.get(sub)
                        );
                    }
                    baseline = Some(map);
                }
                Some(base) => assert_eq!(base, &map, "closure differs at rotation {rot}"),
            }
        }
    }

    // ----- Exact-role backward-link index (`in_by_role` / `in_roles`) -----

    #[test]
    fn sub_nf4_joins_only_the_exact_role_backlinks() {
        // Four backward links into A over three roles; NF4 axioms exist for R
        // and S but not Q. When A ⊑ B arrives, the sub-side join must fire each
        // axiom into exactly the parents whose edge role matches it.
        const R: u32 = 0;
        const S: u32 = 1;
        const Q: u32 = 2;
        const A: u32 = 2;
        const B: u32 = 3;
        const ER: u32 = 4;
        const ES: u32 = 5;
        const X: u32 = 6;
        const Y: u32 = 7;
        const Z: u32 = 8;
        const X2: u32 = 9;
        let idx = nf4_only_idx(&[(R, B, ER), (S, B, ES)], 3);
        let mut st = blank_state(10);
        st.add_edge(X, R, A);
        st.add_edge(Y, S, A);
        st.add_edge(Z, Q, A);
        st.add_edge(X2, R, A);
        run(&idx, &mut st, &mut Prof::default());
        for n in [X, Y, Z, X2] {
            assert!(!st.sub_super[n as usize].contains(&ER));
            assert!(!st.sub_super[n as usize].contains(&ES));
        }
        // The index mirrors the four edges: per-role parents in creation order,
        // roles in first-arrival order.
        assert_eq!(st.in_by_role.get(&(A, R)), Some(&vec![X, X2]));
        assert_eq!(st.in_by_role.get(&(A, S)), Some(&vec![Y]));
        assert_eq!(st.in_by_role.get(&(A, Q)), Some(&vec![Z]));
        assert_eq!(st.in_roles[A as usize], vec![R, S, Q]);
        st.add_sub(A, B);
        run(&idx, &mut st, &mut Prof::default());
        assert!(st.sub_super[X as usize].contains(&ER));
        assert!(st.sub_super[X2 as usize].contains(&ER));
        assert!(st.sub_super[Y as usize].contains(&ES));
        assert!(!st.sub_super[X as usize].contains(&ES));
        assert!(!st.sub_super[Y as usize].contains(&ER));
        assert!(!st.sub_super[Z as usize].contains(&ER));
        assert!(!st.sub_super[Z as usize].contains(&ES));
    }

    #[test]
    fn sub_nf4_self_edge_backlink_joins_repeatedly() {
        // A self-edge (A,R,A) is a backward link of A along R whose parent is A
        // itself. Each new subsumer of A that is an NF4 filler must join over
        // that same in-place parent slice: A ⊑ B gives A ⊑ E, whose Sub item
        // joins again for A ⊑ F.
        const R: u32 = 0;
        const A: u32 = 2;
        const B: u32 = 3;
        const E: u32 = 4;
        const F: u32 = 5;
        let idx = nf4_only_idx(&[(R, B, E), (R, E, F)], 1);
        let mut st = blank_state(6);
        st.add_edge(A, R, A);
        run(&idx, &mut st, &mut Prof::default());
        assert!(!st.sub_super[A as usize].contains(&E));
        st.add_sub(A, B);
        run(&idx, &mut st, &mut Prof::default());
        assert!(st.sub_super[A as usize].contains(&E));
        assert!(st.sub_super[A as usize].contains(&F));
        assert_eq!(st.in_by_role.get(&(A, R)), Some(&vec![A]));
    }

    #[test]
    fn bottom_backpropagates_across_every_incoming_role() {
        // The ⊥ back-propagation is an all-edge consumer: once A ⊑ ⊥ is
        // processed, every parent of A must go to ⊥ regardless of edge role,
        // via the `in_roles` walk over the role-keyed index.
        const R: u32 = 0;
        const S: u32 = 1;
        const T: u32 = 2;
        const A: u32 = 2;
        const X: u32 = 3;
        const Y: u32 = 4;
        const Z: u32 = 5;
        let idx = nf4_only_idx(&[], 3);
        let mut st = blank_state(6);
        st.add_edge(X, R, A);
        st.add_edge(Y, S, A);
        st.add_edge(Z, T, A);
        run(&idx, &mut st, &mut Prof::default());
        for n in [X, Y, Z] {
            assert!(!st.sub_super[n as usize].contains(&BOTTOM));
        }
        st.add_sub(A, BOTTOM);
        run(&idx, &mut st, &mut Prof::default());
        for n in [X, Y, Z] {
            assert!(
                st.sub_super[n as usize].contains(&BOTTOM),
                "parent {n} must inherit ⊥ across its own edge role"
            );
        }
    }

    /// An `Idx` holding only role chains `r1 ∘ r2 ⊑ s` plus the identity role
    /// hierarchy, for the NF7 all-edge consumers.
    fn nf7_only_idx(chains: &[(u32, u32, u32)], nroles: u32) -> Idx {
        let mut nf7_by_pair: HashMap<(u32, u32), Vec<u32>> = HashMap::default();
        for &(r1, r2, s) in chains {
            nf7_by_pair.entry((r1, r2)).or_default().push(s);
        }
        let role_sub = (0..nroles)
            .map(|r| {
                let mut s: HashSet<u32> = HashSet::default();
                s.insert(r);
                s
            })
            .collect();
        Idx {
            nf1_by_sub: HashMap::default(),
            nf2_by_sub: HashMap::default(),
            nf3_by_sub: HashMap::default(),
            nf4_by_filler: HashMap::default(),
            nf5_subs: HashSet::default(),
            nf7_by_pair,
            role_sub,
            reflexive_closed: HashSet::default(),
        }
    }

    #[test]
    fn role_chain_symmetric_join_reads_role_keyed_backlinks() {
        // The symmetric NF7 join consumes the backward links of the new edge's
        // SOURCE: with r1 ∘ r2 ⊑ s, the existing link (P, r1, C) plus the new
        // edge (C, r2, D) must yield (P, s, D), while the non-composing
        // backlink (W, q, C) contributes nothing.
        const R1: u32 = 0;
        const R2: u32 = 1;
        const SS: u32 = 2;
        const QQ: u32 = 3;
        const P: u32 = 2;
        const C: u32 = 3;
        const D: u32 = 4;
        const W: u32 = 5;
        let idx = nf7_only_idx(&[(R1, R2, SS)], 4);
        let mut st = blank_state(6);
        st.add_edge(P, R1, C);
        st.add_edge(W, QQ, C);
        run(&idx, &mut st, &mut Prof::default());
        assert!(!st.edges[P as usize].contains(&(SS, D)));
        st.add_edge(C, R2, D);
        run(&idx, &mut st, &mut Prof::default());
        assert!(
            st.edges[P as usize].contains(&(SS, D)),
            "chain edge (P, s, D) missing from the symmetric join"
        );
        assert_eq!(st.in_by_role.get(&(D, SS)), Some(&vec![P]));
        assert!(st.edges[W as usize].iter().all(|&(r, _)| r == QQ));
    }

    #[test]
    fn merge_redirects_backlinks_per_role_and_clears_merged_node() {
        // The repair merge is an all-edge consumer: merging B into A must
        // redirect every backward link of B (over all roles) onto A, empty B's
        // index entries, and leave the redirected links joinable by NF4.
        const R: u32 = 0;
        const S: u32 = 1;
        const A: u32 = 2;
        const B: u32 = 3;
        const X: u32 = 4;
        const Y: u32 = 5;
        const M: u32 = 6;
        const E: u32 = 7;
        let idx = nf4_only_idx(&[(R, M, E)], 2);
        let mut st = blank_state(8);
        st.add_edge(X, R, B);
        st.add_edge(Y, S, B);
        run(&idx, &mut st, &mut Prof::default());
        let mut repr: Vec<u32> = (0..8).collect();
        let mut merged: Vec<u32> = Vec::new();
        merge_nodes(&mut st, &mut repr, &mut merged, A, B);
        run(&idx, &mut st, &mut Prof::default());
        assert!(st.edges[X as usize].contains(&(R, A)));
        assert!(!st.edges[X as usize].contains(&(R, B)));
        assert!(st.edges[Y as usize].contains(&(S, A)));
        assert!(st.in_roles[B as usize].is_empty());
        assert!(st.in_by_role.get(&(B, R)).is_none());
        assert!(st.in_by_role.get(&(B, S)).is_none());
        assert_eq!(st.in_by_role.get(&(A, R)), Some(&vec![X]));
        assert_eq!(st.in_by_role.get(&(A, S)), Some(&vec![Y]));
        st.add_sub(A, M);
        run(&idx, &mut st, &mut Prof::default());
        assert!(
            st.sub_super[X as usize].contains(&E),
            "redirected backlink (X, R, A) must join sub-side at the new target"
        );
        assert!(!st.sub_super[Y as usize].contains(&E));
    }

    #[test]
    fn multi_role_backlinks_are_input_order_invariant() {
        // Three roles into the same filler target, NF4 axioms on two of them:
        // every rotation of the input clauses must reach the same closure, with
        // each axiom fired only into its exact-role parents.
        let parts = [
            cl(&[c("X", "x")], &[rf("R", "x", "f")]),
            cl(&[c("X", "x")], &[cf("M", "f", "x")]),
            cl(&[c("Y", "x")], &[rf("S", "x", "g")]),
            cl(&[c("Y", "x")], &[cf("M", "g", "x")]),
            cl(&[c("Z", "x")], &[rf("Q", "x", "h")]),
            cl(&[c("Z", "x")], &[cf("M", "h", "x")]),
            cl(&[c("M", "x")], &[c("B", "x")]),
            cl(&[r("R", "x", "y"), c("B", "y")], &[c("ER", "x")]),
            cl(&[r("S", "x", "y"), c("B", "y")], &[c("ES", "x")]),
        ];
        let n = parts.len();
        let mut baseline: Option<std::collections::BTreeMap<String, Vec<String>>> = None;
        for rot in 0..n {
            let order: Vec<String> = (0..n).map(|i| parts[(i + rot) % n].clone()).collect();
            let cs = clauses(&format!("[{}]", order.join(",")));
            let res = classify_inner(cs, CertMode::Off, false).expect("pure EL");
            let map: std::collections::BTreeMap<String, Vec<String>> = res
                .subsumptions
                .iter()
                .map(|(k, v)| {
                    let mut sups = v.clone();
                    sups.sort();
                    (k.clone(), sups)
                })
                .collect();
            match &baseline {
                None => {
                    for (sub, sup, want) in [
                        ("X", "ER", true),
                        ("Y", "ES", true),
                        ("X", "ES", false),
                        ("Y", "ER", false),
                        ("Z", "ER", false),
                        ("Z", "ES", false),
                    ] {
                        assert_eq!(
                            map.get(sub).is_some_and(|s| s.contains(&sup.to_string())),
                            want,
                            "{sub} ⊑ {sup} expected {want}: {:?}",
                            map.get(sub)
                        );
                    }
                    baseline = Some(map);
                }
                Some(base) => assert_eq!(base, &map, "closure differs at rotation {rot}"),
            }
        }
    }

    #[test]
    fn incremental_reuse_extends_backlink_index_for_new_roles() {
        // Retained-fixpoint additions: first a subsumption that makes an old
        // backlink joinable (A ⊑ B activates ∃R.B ⊑ ER over the retained edge
        // (X, R, A)), then a whole new role S into the same retained target.
        let initial = clauses(&format!(
            "[{},{},{}]",
            cl(&[c("X", "x")], &[rf("R", "x", "f")]),
            cl(&[c("X", "x")], &[cf("A", "f", "x")]),
            cl(&[r("R", "x", "y"), c("B", "y")], &[c("ER", "x")]),
        ));
        let mut inc = IncrementalElClassifier::new(initial).expect("pure EL snapshot");
        assert_eq!(inc.is_subsumed_by("X", "ER"), Some(false));

        let up1 = inc
            .add_clauses(clauses(&format!(
                "[{}]",
                cl(&[c("A", "x")], &[c("B", "x")])
            )))
            .expect("monotone addition");
        assert!(up1.reused_fixpoint, "NF1 addition must retain the fixpoint");
        assert_eq!(inc.is_subsumed_by("X", "ER"), Some(true));

        let up2 = inc
            .add_clauses(clauses(&format!(
                "[{},{},{}]",
                cl(&[c("Y", "x")], &[rf("S", "x", "g")]),
                cl(&[c("Y", "x")], &[cf("A", "g", "x")]),
                cl(&[r("S", "x", "y"), c("B", "y")], &[c("ES", "x")]),
            )))
            .expect("monotone addition");
        assert!(
            up2.reused_fixpoint,
            "new-role addition must retain the fixpoint"
        );
        assert_eq!(inc.is_subsumed_by("Y", "ES"), Some(true));
        assert_eq!(inc.is_subsumed_by("Y", "ER"), Some(false));
        assert_eq!(inc.is_subsumed_by("X", "ES"), Some(false));
    }

    #[test]
    fn incremental_restart_rebuilds_backlink_index() {
        // Completing a one-sided existential (X ⊑ ∃R.⊤ gains its filler half)
        // rewrites an NF3, so the session must restart from Init; the rebuilt
        // backlink index must serve the NF4 join in the fresh completion.
        let initial = clauses(&format!("[{}]", cl(&[c("X", "x")], &[rf("R", "x", "f")]),));
        let mut inc = IncrementalElClassifier::new(initial).expect("pure EL snapshot");
        let up = inc
            .add_clauses(clauses(&format!(
                "[{},{}]",
                cl(&[c("X", "x")], &[cf("B", "f", "x")]),
                cl(&[r("R", "x", "y"), c("B", "y")], &[c("E", "x")]),
            )))
            .expect("restart addition");
        assert!(
            !up.reused_fixpoint,
            "completing the existential must restart the completion"
        );
        assert_eq!(inc.is_subsumed_by("X", "E"), Some(true));
    }

    // -----------------------------------------------------------------------
    // Cross-round reuse of the certificate's enumeration index
    // -----------------------------------------------------------------------

    /// `body -> head` over `nvars` unpinned variables.
    fn rcl(nvars: usize, body: Vec<RAtom>, head: Vec<RAtom>) -> RClause {
        RClause {
            nvars,
            origins: (0..nvars)
                .map(|name| ROrigin::Source {
                    source: format!("v{name}"),
                    name,
                })
                .collect(),
            body,
            head,
            pins: Vec::new(),
        }
    }

    /// The index a round would build from scratch over the current structure.
    fn rebuilt_idx(rcs: &[RClause], names: &HashSet<u32>, st: &State) -> CertIdx {
        let mut idx = CertIdx::default();
        idx.refresh(rcs, names, &st.sub_super, &st.edges, None, st.edge_epoch);
        idx
    }

    /// Everything the join reads out of the index, order included.
    fn assert_same_idx(reused: &CertIdx, rebuilt: &CertIdx) {
        assert_eq!(reused.nodes, rebuilt.nodes, "domain differs");
        assert_eq!(reused.alive, rebuilt.alive, "alive flags differ");
        assert_eq!(reused.members, rebuilt.members, "`members` differs");
        assert_eq!(
            reused.edges_by_role, rebuilt.edges_by_role,
            "`edges_by_role` differs"
        );
    }

    /// Residual shape exercising both index halves: a concept body atom and a
    /// role body atom, over four named nodes.
    fn idx_fixture() -> (Vec<RClause>, HashSet<u32>, State) {
        const R: u32 = 1;
        const A: u32 = 2;
        const B: u32 = 3;
        const P: u32 = 4;
        const Q: u32 = 5;
        const S: u32 = 6;
        let rcs = vec![
            rcl(
                1,
                vec![RAtom::C { cid: A, v: 0 }],
                vec![RAtom::C { cid: B, v: 0 }],
            ),
            rcl(
                2,
                vec![RAtom::R { rid: R, s: 0, t: 1 }, RAtom::C { cid: B, v: 1 }],
                vec![RAtom::C { cid: A, v: 0 }],
            ),
        ];
        let names: HashSet<u32> = [P, Q, S, A, B].into_iter().collect();
        let mut st = blank_state(8);
        for &n in &[P, Q, S, A, B] {
            st.add_sub(n, n);
        }
        st.add_edge(P, R, Q);
        st.add_edge(Q, R, S);
        st.worklist.clear();
        (rcs, names, st)
    }

    #[test]
    fn cert_index_reuse_matches_a_rebuild_after_new_labels() {
        // The repair's own additions are the common case: labels grow, the
        // domain and the edges do not. The delta-merged `members` must be the
        // list a rebuild produces, in `nodes` order and without duplicates —
        // that order is what fixes which violations the round's cap collects.
        const A: u32 = 2;
        const B: u32 = 3;
        const P: u32 = 4;
        const Q: u32 = 5;
        const S: u32 = 6;
        let (rcs, names, mut st) = idx_fixture();
        let mut idx = CertIdx::default();
        idx.refresh(&rcs, &names, &st.sub_super, &st.edges, None, st.edge_epoch);
        assert_same_idx(&idx, &rebuilt_idx(&rcs, &names, &st));

        st.start_journal();
        // out of `nodes` order on purpose, and one addition already present
        for (n, l) in [(S, A), (P, A), (Q, B), (P, A), (S, B), (A, A)] {
            st.add_sub(n, l);
        }
        let delta = st.drain_journal().expect("journalling is on");
        idx.refresh(
            &rcs,
            &names,
            &st.sub_super,
            &st.edges,
            Some(&delta),
            st.edge_epoch,
        );
        assert_same_idx(&idx, &rebuilt_idx(&rcs, &names, &st));
        assert!(idx.members[&A].len() >= 3, "the new members must be indexed");
    }

    #[test]
    fn cert_index_reuse_rebuilds_the_edge_half_when_an_edge_arrives() {
        // A new edge can permute `edges[c]`'s iteration order, so the role
        // index cannot be patched — the epoch must force it to be rebuilt.
        const R: u32 = 1;
        const B: u32 = 3;
        const P: u32 = 4;
        const S: u32 = 6;
        let (rcs, names, mut st) = idx_fixture();
        let mut idx = CertIdx::default();
        idx.refresh(&rcs, &names, &st.sub_super, &st.edges, None, st.edge_epoch);
        let before = st.edge_epoch;

        st.start_journal();
        st.add_edge(P, R, S);
        st.add_sub(S, B);
        assert_ne!(st.edge_epoch, before, "a new edge must move the epoch");
        let delta = st.drain_journal().expect("journalling is on");
        idx.refresh(
            &rcs,
            &names,
            &st.sub_super,
            &st.edges,
            Some(&delta),
            st.edge_epoch,
        );
        assert_same_idx(&idx, &rebuilt_idx(&rcs, &names, &st));
    }

    #[test]
    fn cert_index_reuse_rebuilds_both_halves_when_a_node_dies() {
        // A node driven to ⊥ leaves the domain, so it has to leave every
        // `members` bucket and every edge pair that mentions it. That is not a
        // delta the merge can express: the refresh must fall back to a rebuild.
        const A: u32 = 2;
        const Q: u32 = 5;
        let (rcs, names, mut st) = idx_fixture();
        let mut idx = CertIdx::default();
        idx.refresh(&rcs, &names, &st.sub_super, &st.edges, None, st.edge_epoch);

        st.start_journal();
        st.add_sub(Q, A);
        st.add_sub(Q, BOTTOM);
        let delta = st.drain_journal().expect("journalling is on");
        idx.refresh(
            &rcs,
            &names,
            &st.sub_super,
            &st.edges,
            Some(&delta),
            st.edge_epoch,
        );
        assert!(!idx.nodes.contains(&Q), "the dead node must leave the domain");
        assert_same_idx(&idx, &rebuilt_idx(&rcs, &names, &st));
    }

    #[test]
    fn cert_index_reuse_tracks_a_witness_mirror_resync() {
        // The repair's merge re-syncs a merged-away node as a mirror of its
        // representative by wholesale assignment, which bypasses `add_sub` and
        // `add_edge`. The pass records that itself; here we check the two
        // signals it relies on — a moved label set is journalled, a moved edge
        // set moves the epoch — reproduce a rebuild.
        const R: u32 = 1;
        const A: u32 = 2;
        const B: u32 = 3;
        const P: u32 = 4;
        const Q: u32 = 5;
        const S: u32 = 6;
        let (rcs, names, mut st) = idx_fixture();
        st.add_sub(P, A);
        st.add_sub(P, B);
        st.add_edge(P, R, S);
        st.worklist.clear();
        let mut idx = CertIdx::default();
        idx.refresh(&rcs, &names, &st.sub_super, &st.edges, None, st.edge_epoch);

        st.start_journal();
        // exactly the mirror re-sync the repair pass performs for Q -> P
        let subs_moved = !st.sub_super[Q as usize].iter().eq(st.sub_super[P as usize].iter());
        st.sub_super[Q as usize] = st.sub_super[P as usize].clone();
        if subs_moved {
            let State {
                sub_super,
                sub_journal,
                ..
            } = &mut st;
            if let Some(j) = sub_journal.as_mut() {
                for &s in &sub_super[Q as usize] {
                    j.push((Q, s));
                }
            }
        }
        let edges_moved = !st.edges[Q as usize].iter().eq(st.edges[P as usize].iter());
        st.edges[Q as usize] = st.edges[P as usize].clone();
        if edges_moved {
            st.edge_epoch += 1;
        }
        let delta = st.drain_journal().expect("journalling is on");
        idx.refresh(
            &rcs,
            &names,
            &st.sub_super,
            &st.edges,
            Some(&delta),
            st.edge_epoch,
        );
        assert_same_idx(&idx, &rebuilt_idx(&rcs, &names, &st));
    }

    #[test]
    fn cert_index_invalidation_discards_a_stale_delta() {
        // The escape hatch the mirror re-sync uses when it would DELETE from a
        // label: after `invalidate` the next refresh must ignore whatever delta
        // it is handed and rebuild from the structure.
        const A: u32 = 2;
        const P: u32 = 4;
        const S: u32 = 6;
        let (rcs, names, mut st) = idx_fixture();
        let mut idx = CertIdx::default();
        idx.refresh(&rcs, &names, &st.sub_super, &st.edges, None, st.edge_epoch);

        // a label change the delta does not mention
        st.sub_super[P as usize].insert(A);
        idx.invalidate();
        let stale = vec![(S, A)];
        idx.refresh(
            &rcs,
            &names,
            &st.sub_super,
            &st.edges,
            Some(&stale),
            st.edge_epoch,
        );
        assert_same_idx(&idx, &rebuilt_idx(&rcs, &names, &st));
    }

    #[test]
    fn cert_index_reuse_keeps_the_multi_round_repair_verdict() {
        // End to end over a repair that needs more than one round: the same
        // clause set the stale-cover test uses, which forces a residual, then
        // re-checks the cover against the incrementally repaired state. The
        // index is now carried across those rounds, so the verdict pins that
        // the carried index still drives the same choices.
        let cs = clauses(&format!(
            "[{},{},{},{},{}]",
            cl(&[c("C", "x")], &[rf("R", "x", "f")]),
            cl(&[c("C", "x")], &[cf("D", "f", "x")]),
            cl(&[r("R", "x", "y")], &[c("A", "y")]),
            cl(&[], &[c("A", "x"), c("B", "x")]),
            cl(&[c("A", "x"), c("B", "x")], &[]),
        ));
        let res = classify_inner(cs, CertMode::Repair, false).expect("repair certifies");
        assert!(!res.inconsistent);
        assert_eq!(res.unresolved, vec!["D".to_string()]);
    }

    // -----------------------------------------------------------------------
    // Inverse-bridge canonicalisation: what the completion may and may not do
    //
    // The frontend emits `InverseObjectProperties(R,S)` as the swapped pair
    // `R(x,y) → S(y,x)` and `S(x,y) → R(y,x)`. Both together entail
    // `S ≡ R⁻`, so rewriting every `S(x,y)` to `R(y,x)` is truth-preserving and
    // the two bridge clauses become tautologies. The tests below fix the three
    // facts that decide whether that rewrite may be turned into a completion
    // strategy: it is conservative as a rewrite, the reverse-oriented rules it
    // produces cannot be run on this node space, and one-way bridges are not
    // definitions. See docs/INVERSE-BRIDGE-CANONICALISATION.md.
    // -----------------------------------------------------------------------

    #[test]
    fn reciprocal_bridge_rewrite_is_conservative_when_the_dropped_role_is_idle() {
        // `S` occurs only in the two bridges, so rewriting `S(x,y) := R(y,x)`
        // deletes both clauses and leaves a pure-EL set. The rewritten set must
        // answer exactly what the certified original answers -- the rewrite
        // itself neither adds nor drops a named subsumption.
        let original = clauses(&format!(
            "[{},{},{},{},{},{}]",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[r("R", "x", "y"), c("B", "y")], &[c("G", "x")]),
            cl(&[c("G", "x")], &[c("H", "x")]),
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
        ));
        let rewritten = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[r("R", "x", "y"), c("B", "y")], &[c("G", "x")]),
            cl(&[c("G", "x")], &[c("H", "x")]),
        ));
        let before = classify_inner(original, CertMode::Repair, false)
            .expect("the idle bridge pair is repairable");
        let after = classify_inner(rewritten, CertMode::Off, false)
            .expect("the rewritten set is pure EL");
        assert_eq!(before.subsumptions, after.subsumptions);
        assert!(subs_of(&after, "A").contains(&"H".to_string()));
    }

    #[test]
    fn a_bridge_whose_body_role_is_never_derived_is_discharged_by_the_base_model() {
        // ORE 1194 carries two bridges of this shape (`has_distal_part` and
        // `has_proximal_part` occur in no other clause). Nothing ever adds an
        // edge to the body role, so the clause is satisfied by the base model
        // with no mirror at all and the plain check answers.
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[r("T", "x", "y")], &[r("U", "y", "x")]),
            cl(&[c("C", "x")], &[c("D", "x")]),
        ));
        let res = classify_inner(cs, CertMode::Check, false)
            .expect("an underived bridge body is vacuously satisfied");
        assert!(subs_of(&res, "C").contains(&"D".to_string()));
        assert!(!res.inconsistent);
    }

    #[test]
    fn a_reverse_rule_at_a_shared_witness_would_assert_a_named_subsumption() {
        // The completion gives every filler concept ONE node, so the node for
        // `B` is at once the witness of `A ⊑ ∃R.B` for every context that
        // inherits `A`, and the named class `B` itself. Canonicalising
        // `S := R⁻` turns `∃S.C ⊑ D` into a reverse rule that fires at that
        // node from one predecessor, and writing `D` there is exactly the
        // axiom `B ⊑ D`.
        //
        // The sharing here comes from INHERITANCE, not from a repeated axiom:
        // ORE 1194 has 130,268 witness nodes of which only 8 carry more than
        // one existential axiom, but 43.9 M backward links over 202,617
        // distinct (node, role) keys.
        //
        // `A1 ⊑ E` is entailed; `A2 ⊑ E` is not. Counter-model:
        //   a1: A1,A,C   b_1: B,D   R(a1,b_1)  S(b_1,a1)
        //   a2: A2,A     b_2: B     R(a2,b_2)  S(b_2,a2)
        // `b_2` has no C-labelled S-successor, so it is not D and `a2` is not E.
        let el_part = format!(
            "{},{},{},{},{},{}",
            cl(&[c("A", "x")], &[rf("R", "x", "f")]),
            cl(&[c("A", "x")], &[cf("B", "f", "x")]),
            cl(&[c("A1", "x")], &[c("A", "x")]),
            cl(&[c("A2", "x")], &[c("A", "x")]),
            cl(&[c("A1", "x")], &[c("C", "x")]),
            cl(&[r("R", "x", "y"), c("D", "y")], &[c("E", "x")]),
        );
        let with_bridges = clauses(&format!(
            "[{},{},{},{}]",
            el_part,
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")]),
            cl(&[r("S", "x", "y"), c("C", "y")], &[c("D", "x")]),
        ));
        // The base model has no S-edge, so the plain certificate refuses. This
        // is the only correct verdict available on this node space.
        assert!(classify_inner(with_bridges, CertMode::Check, false).is_none());

        // What the reverse rule would write into the node for `B`, spelled as
        // the axiom it actually is. It leaks straight onto `A2`.
        let as_named_axiom = clauses(&format!(
            "[{},{}]",
            el_part,
            cl(&[c("B", "x")], &[c("D", "x")])
        ));
        let leaked = classify_inner(as_named_axiom, CertMode::Off, false)
            .expect("the strengthened set is pure EL");
        assert!(subs_of(&leaked, "A2").contains(&"E".to_string()));
    }

    #[test]
    fn a_one_way_bridge_is_not_a_role_definition() {
        // `R(x,y) → S(y,x)` alone says `R⁻ ⊑ S`, not `S ≡ R⁻`: `S` may hold
        // where the transpose of `R` does not. Reading it as a definition adds
        // the converse, and the converse changes the taxonomy -- here a
        // reflexive `S` forces a reflexive `R`, which the domain axiom turns
        // into a subsumer of everything.
        let shared = format!(
            "{},{},{},{}",
            cl(&[], &[r("S", "x", "x")]),
            cl(&[r("R", "x", "y")], &[c("Z", "x")]),
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[r("R", "x", "y")], &[r("S", "y", "x")]),
        );
        let one_way = clauses(&format!("[{}]", shared));
        let defined = clauses(&format!(
            "[{},{}]",
            shared,
            cl(&[r("S", "x", "y")], &[r("R", "y", "x")])
        ));
        let weak = classify_inner(one_way, CertMode::Repair, false)
            .expect("the one-way bridge is satisfied with no R-edge at all");
        assert!(
            !subs_of(&weak, "A").contains(&"Z".to_string()),
            "R⁻ ⊑ S alone entails nothing about R, got {:?}",
            subs_of(&weak, "A")
        );
        assert_eq!(subs_of(&weak, "A"), vec!["B".to_string()]);
        assert!(weak.unresolved.is_empty());

        // Adding the converse is what a definitional reading does. It is not
        // free: the reflexive `S` now forces a reflexive `R`, the base model no
        // longer satisfies the residual, and the route can publish nothing.
        let strong = classify_inner(defined, CertMode::Repair, false)
            .expect("the reciprocal pair is repairable");
        assert!(
            strong.subsumptions.is_empty() && strong.unresolved.contains(&"A".to_string()),
            "the converse must cost the published taxonomy, got {:?} / {:?}",
            strong.subsumptions,
            strong.unresolved
        );
    }

    #[test]
    fn conjunction_aux_names_are_component_boundary_injective() {
        let left = vec!["a/b".to_string(), "c".to_string()];
        let right = vec!["a".to_string(), "b/c".to_string()];
        assert_eq!(left.join("/"), right.join("/"), "regression witness must collide");
        assert_ne!(conjunction_aux_name(&left), conjunction_aux_name(&right));
        assert_eq!(
            conjunction_aux_name(&["é".to_string(), "x/y".to_string()]),
            "__conj__2:é3:x/y"
        );
    }

    #[test]
    fn conjunction_origins_record_exact_sorted_source_prefix_ids() {
        let input = clauses(&format!(
            "[{}]",
            cl(&[c("C", "x"), c("A", "x"), c("B", "x")], &[c("D", "x")])
        ));
        let mut interner = Interner::new();
        let (nfs, residual, _) = to_nf(&input, &mut interner).expect("EL normal form");
        assert!(residual.is_empty());
        let aux = interner
            .id(&conjunction_aux_name(&["A".to_string(), "B".to_string()]))
            .expect("conjunction auxiliary");
        assert_eq!(
            nfs.conjunction_origins.get(&aux),
            Some(&vec![interner.id("A").unwrap(), interner.id("B").unwrap()])
        );
    }

    #[test]
    fn the_canonicalised_reverse_forms_are_outside_to_nf() {
        // Rewriting `S := R⁻` deletes the bridge clauses but does not delete
        // the work: `∃S.C ⊑ D` becomes `R(y,x) ∧ C(y) → D(x)`, whose head sits
        // on the role TARGET, and `P ⊑ ∃S.C` becomes `P(x) → R(f(x),x)`, whose
        // existential sits on the role SOURCE. Both are the wirings `to_nf`
        // deliberately refuses, so the rewrite trades 2 bridge clauses for a
        // reverse-oriented occurrence of every rule the dropped role carried.
        // On ORE 1194 that trade is 55,384 rules for the smallest orientation
        // of the `BFO_0000050`/`BFO_0000051` pair (engine/py/role_census.py).
        let reverse_nf4 = clauses(&format!(
            "[{}]",
            cl(&[r("R", "y", "x"), c("C", "y")], &[c("D", "x")])
        ));
        assert!(!is_pure_el_shape(&reverse_nf4));
        assert!(classify_inner(reverse_nf4, CertMode::Off, false).is_none());

        // `P(x) → R(f(x), x)` plus `P(x) → C(f(x))`: an existential whose
        // witness is the role SOURCE.
        let back_edge = format!(
            "{{\"kind\":\"role\",\"role\":\"R\",\"source\":{{\"kind\":\"fun\",\"function\":\"f\",\"arg\":{}}},\"target\":{}}}",
            v("x"),
            v("x")
        );
        let reverse_nf3 = clauses(&format!(
            "[{},{}]",
            cl(&[c("P", "x")], &[back_edge]),
            cl(&[c("P", "x")], &[cf("C", "f", "x")])
        ));
        assert!(!is_pure_el_shape(&reverse_nf3));
        assert!(classify_inner(reverse_nf3, CertMode::Off, false).is_none());
    }
}
