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
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::sync::Mutex;

use rayon::prelude::*;

use crate::json_io::{JAtom, JClause, JTerm};

// Narrow, opt-in insertion trace used to diagnose one cyclic Uberon definer.
// Both atomics remain inert unless KM_ELC_DEBUG_DERIVATION is set and the
// concept is present in the current input.
static DEBUG_ADD_SUB_CONCEPT: AtomicUsize = AtomicUsize::new(usize::MAX);
static DEBUG_ADD_SUB_NODE: AtomicUsize = AtomicUsize::new(usize::MAX);
static DEBUG_ADD_SUB_COUNT: AtomicUsize = AtomicUsize::new(0);

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
        // Fold eight bytes per step (then four, then the tail), as rustc-hash
        // does, instead of one multiply-rotate per byte: interning a 60-100
        // byte IRI drops from ~80 to ~12 hash steps. The result is still a
        // deterministic function of the byte sequence alone, so every table
        // keyed by strings keeps its exact membership semantics.
        let mut words = bytes.chunks_exact(8);
        for word in &mut words {
            self.add(u64::from_le_bytes(word.try_into().expect("8-byte chunk")));
        }
        let mut halves = words.remainder().chunks_exact(4);
        for half in &mut halves {
            self.add(u64::from(u32::from_le_bytes(
                half.try_into().expect("4-byte chunk"),
            )));
        }
        for &b in halves.remainder() {
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
    // Share each immutable symbol allocation between the forward and reverse
    // tables. OWL IRIs are commonly tens of bytes long, so retaining two owned
    // Strings per concept/role needlessly duplicated the EL signature's bytes.
    map: HashMap<Arc<str>, u32>,
    names: Vec<Arc<str>>,
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
        let name: Arc<str> = Arc::from(s);
        self.names.push(Arc::clone(&name));
        self.map.insert(name, id);
        id
    }

    fn name(&self, id: u32) -> &str {
        self.names[id as usize].as_ref()
    }

    fn maybe_name(&self, id: u32) -> Option<&str> {
        self.names.get(id as usize).map(AsRef::as_ref)
    }

    fn debug_name(&self, id: u32) -> String {
        self.maybe_name(id)
            .map(str::to_owned)
            .unwrap_or_else(|| format!("#fresh_node_{id}"))
    }

    /// Non-creating lookup (P1 hoisting reads ids of already-seen concepts only).
    fn id(&self, s: &str) -> Option<u32> {
        self.map.get(s).copied()
    }

    fn len(&self) -> usize {
        self.names.len()
    }

    /// Transfer the shared symbol table after saturation has finished. Dropping
    /// the forward map leaves one `Arc` per symbol without copying every IRI.
    fn into_names(self) -> Vec<Arc<str>> {
        let Interner { map, names } = self;
        drop(map);
        names
    }

    fn cloned_names(&self) -> Vec<String> {
        self.names.iter().map(|name| name.to_string()).collect()
    }

    fn cloned_shared_names(&self) -> Vec<Arc<str>> {
        self.names.clone()
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
            (
                JTerm::Aux {
                    root: r1,
                    label: l1,
                },
                JTerm::Aux {
                    root: r2,
                    label: l2,
                },
            ) => r1 == r2 && l1 == l2,
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
        (
            JAtom::Eq {
                left: l1,
                right: r1,
            },
            JAtom::Eq {
                left: l2,
                right: r2,
            },
        ) => term_eq(l1, l2) && term_eq(r1, r2),
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

    // Per-clause atom partitions. Declared once and cleared per clause so the
    // scan does not allocate (and free) four vectors per clause: on a 440k
    // clause terminology that was 1.8M allocations inside `to_nf` alone.
    let mut bc: Vec<&JAtom> = Vec::new();
    let mut br: Vec<&JAtom> = Vec::new();
    let mut hc: Vec<&JAtom> = Vec::new();
    let mut hr: Vec<&JAtom> = Vec::new();
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
        bc.clear();
        bc.extend(b.iter().filter(|a| concept_of(a).is_some()));
        br.clear();
        br.extend(b.iter().filter(|a| matches!(a, JAtom::Role { .. })));
        hc.clear();
        hc.extend(h.iter().filter(|a| concept_of(a).is_some()));
        hr.clear();
        hr.extend(h.iter().filter(|a| matches!(a, JAtom::Role { .. })));

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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

impl Item {
    /// The context an item belongs to: the subject of a subsumption or the
    /// source of an edge. Processing the item reads and extends that context's
    /// own label, out-edge set and backward-link roles; everything else it
    /// touches is read-only index data or the remote endpoint of an edge.
    #[inline]
    fn context(self) -> u32 {
        match self {
            Item::Sub(c, _)
            | Item::Edge(c, _, _)
            | Item::EdgeSerial(c, _, _)
            | Item::EdgeAfterNf4(c, _, _) => c,
        }
    }
}

/// Empty per-context chain in [`ContextQueue::head`].
const NO_ITEM: u32 = u32::MAX;
/// No context is being drained (`ContextQueue::current`).
const NO_CONTEXT: u32 = u32::MAX;

/// The completion worklist and its scheduling discipline.
///
/// The historical discipline is one global FIFO: every conclusion of every
/// context is appended to a single queue, so consecutive items belong to
/// different contexts most of the time and each item pays cold cache misses
/// on its context's label (`sub_super[c]`, a separate hash table per context),
/// its edge set and its backward-link roles. On the ORE EL terminologies that
/// miss the wall targets (100k-260k symbols, one table per symbol) those
/// tables do not fit the cache, and the retained profiles put the saturation
/// at memory latency rather than at rule speed.
///
/// `Contextual` is ELK's scheduling (Kazakov, Krötzsch, Simančík, JAR 2014,
/// §4: a context is *activated* when it receives its first pending item and
/// is then processed until its queue is empty). Items are chained per context
/// and `pop` drains the activated context completely, including the items its
/// own processing produces, before moving on to the next activated context in
/// activation order. A context's whole burst of conclusions is therefore
/// processed while its tables are hot, and the tables are fetched from memory
/// once per activation instead of once per item.
///
/// This is scheduling only. Every fact enters the state through `add_sub` or
/// `add_edge`, which queue exactly one item for it, and `run` processes every
/// queued item exactly once with rule code shared by both disciplines; the
/// backward links, propagations and labels a rule joins against are updated
/// when a fact is inserted, so every (backward link, propagation), (edge, ⊥)
/// and (edge, edge) pair fires from whichever side arrives second under any
/// order. The completion is a finite monotone closure, so the set of derived
/// facts, the number of items and the number of rule instances fired are the
/// same under either discipline; only the order in which conclusions are
/// queued differs.
///
/// The parallel NF4 frontier batch (`fire_edge_nf4_batch`, armed with
/// `KM_ELC_PAR_NF4` for one giant profile) reads a run of consecutive edge
/// items off the front of one global queue, so that mode keeps the FIFO;
/// `KM_ELC_FIFO` selects it explicitly for A/B measurement.
enum Worklist {
    /// One global first-in first-out queue.
    Fifo(VecDeque<Item>),
    /// Per-context chains drained one activated context at a time.
    Contextual(ContextQueue),
}

/// Per-context item chains plus the activation queue of [`Worklist::Contextual`].
struct ContextQueue {
    /// The most recently queued pending item of each context (`NO_ITEM` when
    /// the context has none); the rest of the context's items chain through
    /// `slots`. Four bytes per symbol, dense, so the push of a cross-context
    /// conclusion touches one cache line of this table and nothing else.
    head: Vec<u32>,
    /// Item arena: `(item, next item of the same context)`. Freed slots are
    /// recycled last-freed first, so the conclusions a context produces while
    /// it is being drained land in the lines its previous items just left.
    /// The arena never holds more than the peak number of simultaneously
    /// pending items, which is far below the global FIFO's peak because a
    /// context's own conclusions are consumed as soon as they are produced.
    slots: Vec<(Item, u32)>,
    free: Vec<u32>,
    /// Contexts holding pending items, in activation order.
    active: VecDeque<u32>,
    /// Whether a context is in `active` or is the one being drained, so an
    /// item queued for it does not activate it a second time.
    queued: Vec<bool>,
    /// The context being drained, `NO_CONTEXT` between activations. A
    /// context stays current until a `pop` finds its chain empty, so items it
    /// queues for itself are processed in the same activation.
    current: u32,
    len: usize,
    /// Activations so far (KM_ELC_PROFILE `ctx_activations`).
    activations: u64,
}

impl ContextQueue {
    fn new(n: usize) -> ContextQueue {
        ContextQueue {
            head: vec![NO_ITEM; n],
            slots: Vec::new(),
            free: Vec::new(),
            active: VecDeque::new(),
            queued: vec![false; n],
            current: NO_CONTEXT,
            len: 0,
            activations: 0,
        }
    }

    /// Admit contexts up to `n` (symbols an incremental transaction appends).
    fn grow(&mut self, n: usize) {
        if n > self.head.len() {
            self.head.resize(n, NO_ITEM);
            self.queued.resize(n, false);
        }
    }

    #[inline]
    fn push(&mut self, item: Item) {
        let c = item.context() as usize;
        let next = self.head[c];
        let slot = match self.free.pop() {
            Some(slot) => {
                self.slots[slot as usize] = (item, next);
                slot
            }
            None => {
                self.slots.push((item, next));
                (self.slots.len() - 1) as u32
            }
        };
        self.head[c] = slot;
        self.len += 1;
        if !self.queued[c] {
            self.queued[c] = true;
            self.active.push_back(c as u32);
        }
    }

    /// The next item: the current context's most recently queued item while
    /// it has any, else the first item of the next activated context.
    #[inline]
    fn pop(&mut self) -> Option<Item> {
        loop {
            if self.current != NO_CONTEXT {
                let c = self.current as usize;
                let slot = self.head[c];
                if slot != NO_ITEM {
                    let (item, next) = self.slots[slot as usize];
                    self.head[c] = next;
                    self.free.push(slot);
                    self.len -= 1;
                    return Some(item);
                }
                self.queued[c] = false;
                self.current = NO_CONTEXT;
            }
            let c = self.active.pop_front()?;
            self.current = c;
            self.activations += 1;
        }
    }

    #[cfg(test)]
    fn clear(&mut self) {
        self.head.iter_mut().for_each(|h| *h = NO_ITEM);
        self.queued.iter_mut().for_each(|q| *q = false);
        self.slots.clear();
        self.free.clear();
        self.active.clear();
        self.current = NO_CONTEXT;
        self.len = 0;
    }

    /// Every pending item in the order `pop` would return it.
    #[cfg(test)]
    fn items(&self) -> Vec<Item> {
        let mut out = Vec::with_capacity(self.len);
        let chain = |c: u32, out: &mut Vec<Item>| {
            let mut slot = self.head[c as usize];
            while slot != NO_ITEM {
                let (item, next) = self.slots[slot as usize];
                out.push(item);
                slot = next;
            }
        };
        if self.current != NO_CONTEXT {
            chain(self.current, &mut out);
        }
        for &c in &self.active {
            chain(c, &mut out);
        }
        out
    }
}

impl Worklist {
    fn contextual(n: usize) -> Worklist {
        Worklist::Contextual(ContextQueue::new(n))
    }

    fn fifo() -> Worklist {
        Worklist::Fifo(VecDeque::new())
    }

    /// The discipline the environment selects for a state of `n` symbols:
    /// the global FIFO when the parallel NF4 frontier batch is armed
    /// (`KM_ELC_PAR_NF4`) or asked for outright (`KM_ELC_FIFO`), else the
    /// context-local queue.
    fn from_env(n: usize) -> Worklist {
        if std::env::var_os("KM_ELC_PAR_NF4").is_some() || std::env::var_os("KM_ELC_FIFO").is_some()
        {
            Worklist::fifo()
        } else {
            Worklist::contextual(n)
        }
    }

    /// An empty worklist with the same discipline and symbol width.
    fn new_like(&self) -> Worklist {
        match self {
            Worklist::Fifo(_) => Worklist::fifo(),
            Worklist::Contextual(queue) => Worklist::contextual(queue.head.len()),
        }
    }

    #[inline]
    fn push(&mut self, item: Item) {
        match self {
            Worklist::Fifo(queue) => queue.push_back(item),
            Worklist::Contextual(queue) => queue.push(item),
        }
    }

    /// Queue `item` so that it is processed next: at the front of the FIFO,
    /// or on top of its context's chain (the frontier batch hands the edges
    /// it took back this way, in their original order).
    fn push_next(&mut self, item: Item) {
        match self {
            Worklist::Fifo(queue) => queue.push_front(item),
            Worklist::Contextual(queue) => queue.push(item),
        }
    }

    #[inline]
    fn pop(&mut self) -> Option<Item> {
        match self {
            Worklist::Fifo(queue) => queue.pop_front(),
            Worklist::Contextual(queue) => queue.pop(),
        }
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn len(&self) -> usize {
        match self {
            Worklist::Fifo(queue) => queue.len(),
            Worklist::Contextual(queue) => queue.len,
        }
    }

    #[cfg(test)]
    fn clear(&mut self) {
        match self {
            Worklist::Fifo(queue) => queue.clear(),
            Worklist::Contextual(queue) => queue.clear(),
        }
    }

    /// Admit contexts up to `n` (a no-op for the FIFO, which is not indexed
    /// by context).
    fn grow(&mut self, n: usize) {
        if let Worklist::Contextual(queue) = self {
            queue.grow(n);
        }
    }

    /// Context activations so far (0 under the FIFO).
    fn activations(&self) -> u64 {
        match self {
            Worklist::Fifo(_) => 0,
            Worklist::Contextual(queue) => queue.activations,
        }
    }

    /// Every pending item in the order `pop` would return it.
    #[cfg(test)]
    fn items(&self) -> Vec<Item> {
        match self {
            Worklist::Fifo(queue) => queue.iter().copied().collect(),
            Worklist::Contextual(queue) => queue.items(),
        }
    }
}

/// Every completion rule triggered by one newly derived subsumer `d`: the NF1
/// conclusions, the NF2 candidates, the NF3 existentials, the NF4 axioms whose
/// filler is `d`, and the NF5 flag. A borrowed view of one record of
/// `Idx::pool`, where the four lists of a trigger sit back to back behind a
/// header of [`RULE_HEADER_WORDS`] words. The Sub arm of `run` reaches a
/// record through one dense slot (`Idx::rules_of`) and then reads one
/// contiguous run of memory per item, where a record used to be a 72-byte
/// struct of four separately allocated boxed slices (up to five cache lines
/// scattered over the heap, and four allocations to build and free per
/// rule-bearing symbol).
#[derive(Clone, Copy)]
struct ConceptRules<'a> {
    /// NF1 `d ⊑ E`: the conclusions `E`, in axiom order.
    nf1_sups: &'a [u32],
    /// NF2 `d ⊓ X ⊑ E`, with `d` in either operand position, as `[X, E]`,
    /// SORTED by `X` so the label-side join can binary-search a partner.
    nf2_cand: &'a [[u32; 2]],
    /// NF3 `d ⊑ ∃R.F` as `[R, F]`, in axiom order.
    nf3_edges: &'a [[u32; 2]],
    /// NF4 `∃R.d ⊑ E` as `[R, E]`, SORTED by role so the sub-side join visits
    /// one contiguous exact-role group per backward-link bucket.
    nf4_axioms: &'a [[u32; 2]],
    /// NF5 `d ⊑ ⊥`.
    bottom: bool,
}

/// `Idx::rule_slot` entry of a symbol that triggers no rule.
const NO_RULES: u32 = u32::MAX;
/// Words of a record header in `Idx::pool`: the NF1, NF2, NF3 and NF4 list
/// lengths in entries (pairs count once), with the NF5 flag in the top bit of
/// the NF1 word.
const RULE_HEADER_WORDS: usize = 4;
const RULE_BOTTOM_FLAG: u32 = 1 << 31;

/// An even-length run of pool words read as pairs.
#[inline]
fn pool_pairs(words: &[u32]) -> &[[u32; 2]] {
    let (pairs, rest) = words.as_chunks::<2>();
    debug_assert!(rest.is_empty(), "pool pair run has odd length");
    pairs
}

/// Read-only indexes over the normal forms; built once, never mutated during the
/// loop, so the hot path can iterate their slices directly (no per-item clone).
struct Idx {
    /// Symbol id -> offset of its record in `pool`, or `NO_RULES`. Dense (four
    /// bytes per interned symbol) so the per-item lookup of the Sub arm stays
    /// in cache, while records exist only for symbols that trigger a rule.
    rule_slot: Vec<u32>,
    /// Every rule record back to back, in ascending trigger order: a header of
    /// `RULE_HEADER_WORDS` words, then the trigger's NF1 conclusions, NF2
    /// candidate pairs, NF3 pairs and NF4 pairs. One allocation for the whole
    /// terminology; a typical trigger's record spans a cache line or two.
    pool: Vec<u32>,
    /// Whether any NF4 axiom exists: the edge-side join and its frontier batch
    /// are skipped entirely otherwise.
    has_nf4: bool,
    nf7_by_pair: HashMap<(u32, u32), Vec<u32>>, // (r1,r2) -> [sup]
    role_sub: Vec<HashSet<u32>>,                // role -> {super roles} (computed once)
    // Reflexive roles closed up the hierarchy: every super-role of a declared
    // reflexive role is also reflexive (R(x,x) ∧ R⊑S ⟹ S(x,x)).
    reflexive_closed: HashSet<u32>,
}

impl Idx {
    /// Number of records in `pool` (symbols that trigger at least one rule).
    #[cfg(test)]
    fn rule_count(&self) -> usize {
        self.rule_slot
            .iter()
            .filter(|&&slot| slot != NO_RULES)
            .count()
    }

    /// Super-roles of `r` (always includes `r`, since every role in the signature
    /// is pre-seeded with itself and every edge role lies in that signature).
    fn role_supers(&self, r: u32) -> &HashSet<u32> {
        &self.role_sub[r as usize]
    }

    /// The rules triggered by the newly derived subsumer `d`, if any. A symbol
    /// outside the index (never produced by `to_nf`, but harmless) triggers
    /// nothing.
    #[inline]
    fn rules_of(&self, d: u32) -> Option<ConceptRules<'_>> {
        match self.rule_slot.get(d as usize) {
            Some(&slot) if slot != NO_RULES => Some(self.record_at(slot as usize)),
            _ => None,
        }
    }

    /// The record whose header starts at `offset` in `pool`.
    #[inline]
    fn record_at(&self, offset: usize) -> ConceptRules<'_> {
        let pool = &self.pool;
        let head = pool[offset];
        let n1 = (head & !RULE_BOTTOM_FLAG) as usize;
        let n2 = pool[offset + 1] as usize;
        let n3 = pool[offset + 2] as usize;
        let n4 = pool[offset + 3] as usize;
        let start = offset + RULE_HEADER_WORDS;
        let body = &pool[start..start + n1 + 2 * (n2 + n3 + n4)];
        let (nf1_sups, rest) = body.split_at(n1);
        let (nf2, rest) = rest.split_at(2 * n2);
        let (nf3, nf4) = rest.split_at(2 * n3);
        ConceptRules {
            nf1_sups,
            nf2_cand: pool_pairs(nf2),
            nf3_edges: pool_pairs(nf3),
            nf4_axioms: pool_pairs(nf4),
            bottom: head & RULE_BOTTOM_FLAG != 0,
        }
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
    // Pending items, scheduled per context by default (see `Worklist`): the
    // rules of one activated context run back to back while its label and
    // edge tables are hot, instead of interleaving every context's items
    // through one global queue.
    worklist: Worklist,
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

/// Source-specific witnesses for selected existential roles. Canonical EL
/// completion may share one filler context across sources. That sharing is a
/// useful least-model optimization, but a rooted countermodel sometimes needs
/// the standard EL unravelling even without inverse functionality: unrelated
/// obligations attached to the shared filler can otherwise kill every legal
/// side of a covering choice. This allocator is enabled only in the
/// fail-closed rooted certificate route.
#[derive(Clone)]
struct FreshInverseWitnesses {
    roles: HashSet<u32>,
    unrestricted_roles: HashSet<u32>,
    selected_pairs: HashSet<(u32, u32)>,
    deep_unrestricted_roles: HashSet<u32>,
    deep_selected_pairs: HashSet<(u32, u32)>,
    selective_deep: bool,
    active_sources: HashSet<u32>,
    depth: HashMap<u32, usize>,
    max_depth: Option<usize>,
    existential_pairs: HashSet<(u32, u32)>,
    nodes: HashMap<(u32, u32, u32), u32>,
    origins: HashMap<u32, (u32, u32, u32)>,
    limit: usize,
    exhausted: bool,
}

impl FreshInverseWitnesses {
    /// Inspect a failed search candidate without affecting allocation or closure.
    /// Redirect counts cover only existing edges; NF3 can allocate many more
    /// witnesses during closure, so report the actual allocator population.
    fn report_population(&self, st: &State, it: &Interner) {
        let mut groups: HashMap<(usize, u32, u32), (usize, usize)> = HashMap::default();
        let mut depths: HashMap<usize, usize> = HashMap::default();
        for (&node, &(source, role, filler)) in &self.origins {
            let depth = self.depth[&node];
            *depths.entry(depth).or_default() += 1;
            let group = groups.entry((depth, role, filler)).or_default();
            group.0 += 1;
            group.1 += usize::from(st.sub_super[source as usize].contains(&BOTTOM));
        }
        let mut depths: Vec<_> = depths.into_iter().collect();
        depths.sort_unstable();
        eprintln!(
            "KM_ELC_CERT fresh population: allocated={} active_sources={} by_depth={depths:?}",
            self.nodes.len(), self.active_sources.len(),
        );
        let mut groups: Vec<_> = groups.into_iter().collect();
        groups.sort_unstable_by_key(|&(key, (count, _))| (std::cmp::Reverse(count), key));
        for ((depth, role, filler), (count, dead_sources)) in groups.into_iter().take(20) {
            eprintln!(
                "KM_ELC_CERT fresh population group: depth={depth} role={} filler={} count={count} bottom_sources={dead_sources}",
                it.debug_name(role), it.debug_name(filler),
            );
        }
    }

    #[inline]
    fn route_selected(&self, source: u32, role: u32, filler: u32) -> bool {
        let source_depth = self.depth.get(&source).copied().unwrap_or(0);
        let (unrestricted_roles, selected_pairs) =
            if self.selective_deep && source_depth > 0 {
                (&self.deep_unrestricted_roles, &self.deep_selected_pairs)
            } else {
                (&self.unrestricted_roles, &self.selected_pairs)
            };
        self.active_sources.contains(&source)
            && self.roles.contains(&role)
            && (unrestricted_roles.contains(&role) || selected_pairs.contains(&(role, filler)))
    }

    #[inline]
    fn selected(&self, source: u32, role: u32, filler: u32) -> bool {
        self.route_selected(source, role, filler)
            && self
                .max_depth
                .is_none_or(|limit| self.depth.get(&source).copied().unwrap_or(0) < limit)
    }

    fn target(&mut self, st: &mut State, source: u32, role: u32, filler: u32) -> u32 {
        if !self.selected(source, role, filler) {
            return filler;
        }
        let key = (source, role, filler);
        if let Some(&node) = self.nodes.get(&key) {
            return node;
        }
        // This allocator constructs a candidate model, not the EL lower bound.
        // A source containing bottom cannot inhabit that model. Keep existing
        // witness identities above, but spend no new allocations on its other
        // existential edges. Returning the canonical filler still lets normal
        // closure propagate bottom and lets the protected-root check reject
        // the candidate. Live sources retain the ordinary allocation/cap path.
        if st.sub_super[source as usize].contains(&BOTTOM) {
            return filler;
        }
        if self.nodes.len() >= self.limit {
            self.exhausted = true;
            return filler;
        }
        let node = st.sub_super.len() as u32;
        st.sub_super.push(HashSet::default());
        st.edges.push(HashSet::default());
        st.in_roles.push(Vec::new());
        st.worklist.grow(st.sub_super.len());
        st.add_sub(node, TOP);
        st.add_sub(node, filler);
        self.nodes.insert(key, node);
        self.origins.insert(node, (source, role, filler));
        self.depth
            .insert(node, self.depth.get(&source).copied().unwrap_or(0) + 1);
        // The witness participates in the same closure invocation that created
        // it.  Activate it immediately so a depth-N unravelling also freshens
        // existential edges generated while closing levels 1..N-1.  Waiting
        // for the later rooted-domain expansion made a dying level-1 witness
        // ineligible for admission and silently collapsed every finite depth
        // greater than one back to depth one.
        self.active_sources.insert(node);
        node
    }
}

// ---------------------------------------------------------------------------
// Lean ELC certificate wire model
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanElStep {
    Refl {
        a: u32,
    },
    Top {
        a: u32,
    },
    Nf1 {
        a: u32,
        sub: u32,
        sup: u32,
    },
    Nf2 {
        a: u32,
        left: u32,
        right: u32,
        sup: u32,
    },
    Nf5 {
        a: u32,
        sub: u32,
    },
    Nf4 {
        a: u32,
        target: u32,
        filler: u32,
        sup: u32,
        role: u32,
    },
    BottomEdge {
        a: u32,
        target: u32,
        role: u32,
    },
    Nf3 {
        a: u32,
        sub: u32,
        filler: u32,
        role: u32,
    },
    Nf6 {
        a: u32,
        target: u32,
        sub: u32,
        sup: u32,
    },
    Nf7 {
        a: u32,
        middle: u32,
        target: u32,
        first: u32,
        second: u32,
        sup: u32,
    },
    Reflexive {
        a: u32,
        role: u32,
    },
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
    Var {
        name: u32,
    },
    Fun {
        function: u32,
        argument: Box<LeanRawTerm>,
    },
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanRawAtom {
    Concept {
        concept: u32,
        term: LeanRawTerm,
    },
    Role {
        role: u32,
        source: LeanRawTerm,
        target: LeanRawTerm,
    },
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum LeanResidualAtom {
    Concept {
        concept: u32,
        term: LeanRawTerm,
    },
    Role {
        role: u32,
        source: LeanRawTerm,
        target: LeanRawTerm,
    },
    Eq {
        left: LeanRawTerm,
        right: LeanRawTerm,
    },
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
    Concept {
        concept: u32,
        slot: usize,
    },
    Role {
        role: u32,
        source: usize,
        target: usize,
    },
    Eq {
        left: usize,
        right: usize,
    },
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
struct LeanCanonicalWitnessRecord {
    sub: u32,
    role: u32,
    filler: u32,
    witness: u32,
    function: u32,
    role_variable: u32,
    filler_variable: u32,
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
    source_ontology: Vec<LeanResidualClause>,
    raw_ontology: Vec<LeanRawClause>,
    witness_records: Vec<LeanCanonicalWitnessRecord>,
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
            compact: None,
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
    witness_records: Vec<LeanCanonicalWitnessRecord>,
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
                    steps.push(LeanElStep::Nf1 {
                        a,
                        sub: nf.sub,
                        sup: nf.sup,
                    });
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
                if role == nf.role
                    && subs.contains(&(target, nf.filler))
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
                    if role == nf.r1 && second == nf.r2 && edges.insert((a, nf.sup, end)) {
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
    ontology.extend(nfs.nf1.iter().map(|x| LeanElClause::Nf1 {
        sub: x.sub,
        sup: x.sup,
    }));
    ontology.extend(nfs.nf2.iter().map(|x| LeanElClause::Nf2 {
        left: x.sub1,
        right: x.sub2,
        sup: x.sup,
    }));
    ontology.extend(nfs.nf3.iter().map(|x| LeanElClause::Nf3 {
        sub: x.sub,
        role: x.role,
        filler: x.filler,
    }));
    ontology.extend(nfs.nf4.iter().map(|x| LeanElClause::Nf4 {
        role: x.role,
        filler: x.filler,
        sup: x.sup,
    }));
    ontology.extend(nfs.nf5.iter().map(|&sub| LeanElClause::Nf5 { sub }));
    ontology.extend(nfs.nf6.iter().map(|x| LeanElClause::Nf6 {
        sub: x.sub,
        sup: x.sup,
    }));
    ontology.extend(nfs.nf7.iter().map(|x| LeanElClause::Nf7 {
        first: x.r1,
        second: x.r2,
        sup: x.sup,
    }));
    ontology.extend(
        nfs.reflexive_roles
            .iter()
            .map(|&role| LeanElClause::Reflexive { role }),
    );
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
        rust_subsumptions.extend(
            st.sub_super[sub as usize]
                .iter()
                .map(|&sup| LeanElSubFact { sub, sup }),
        );
        rust_edges.extend(
            st.edges[sub as usize]
                .iter()
                .map(|&(role, target)| LeanElEdgeFact {
                    source: sub,
                    role,
                    target,
                }),
        );
    }
    rust_subsumptions.sort_unstable_by_key(|fact| (fact.sub, fact.sup));
    rust_edges.sort_unstable_by_key(|fact| (fact.source, fact.role, fact.target));
    let mut public_subsumptions: Vec<_> = rust_subsumptions
        .iter()
        .filter(|fact| {
            fact.sub != TOP && fact.sub != BOTTOM && fact.sup != fact.sub && fact.sup != TOP
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
                function: interner
                    .id(function)
                    .ok_or_else(|| format!("uninterned function {function}"))?,
                argument: Box::new(raw_term(arg, interner, variables)?),
            }),
            JTerm::Ind { .. } | JTerm::Aux { .. } => {
                Err("non-EL raw term in Lean certificate".into())
            }
        }
    }
    fn raw_atom(
        atom: &JAtom,
        interner: &Interner,
        variables: &mut HashMap<String, u32>,
    ) -> Result<LeanRawAtom, String> {
        match atom {
            JAtom::Concept { concept, term } => Ok(LeanRawAtom::Concept {
                concept: interner
                    .id(concept)
                    .ok_or_else(|| format!("uninterned concept {concept}"))?,
                term: raw_term(term, interner, variables)?,
            }),
            JAtom::Role {
                role,
                source,
                target,
            } => Ok(LeanRawAtom::Role {
                role: interner
                    .id(role)
                    .ok_or_else(|| format!("uninterned role {role}"))?,
                source: raw_term(source, interner, variables)?,
                target: raw_term(target, interner, variables)?,
            }),
            JAtom::Eq { .. } => Err("equality atom in Lean ELC certificate".into()),
        }
    }
    let mut raw_ontology = Vec::with_capacity(raw_clauses.len());
    for clause in raw_clauses {
        raw_ontology.push(LeanRawClause {
            body: clause
                .body
                .iter()
                .map(|a| raw_atom(a, interner, &mut variables))
                .collect::<Result<_, _>>()?,
            head: clause
                .head
                .iter()
                .map(|a| raw_atom(a, interner, &mut variables))
                .collect::<Result<_, _>>()?,
        });
    }
    let mut source_ontology: Vec<_> = raw_ontology
        .iter()
        .map(|clause| LeanResidualClause {
            body: clause
                .body
                .iter()
                .map(|atom| match atom {
                    LeanRawAtom::Concept { concept, term } => LeanResidualAtom::Concept {
                        concept: *concept,
                        term: term.clone(),
                    },
                    LeanRawAtom::Role {
                        role,
                        source,
                        target,
                    } => LeanResidualAtom::Role {
                        role: *role,
                        source: source.clone(),
                        target: target.clone(),
                    },
                })
                .collect(),
            head: clause
                .head
                .iter()
                .map(|atom| match atom {
                    LeanRawAtom::Concept { concept, term } => LeanResidualAtom::Concept {
                        concept: *concept,
                        term: term.clone(),
                    },
                    LeanRawAtom::Role {
                        role,
                        source,
                        target,
                    } => LeanResidualAtom::Role {
                        role: *role,
                        source: source.clone(),
                        target: target.clone(),
                    },
                })
                .collect(),
        })
        .collect();
    for record in &witness_records {
        let role_variable = LeanRawTerm::Var {
            name: record.role_variable,
        };
        let filler_variable = LeanRawTerm::Var {
            name: record.filler_variable,
        };
        source_ontology.push(LeanResidualClause {
            body: vec![LeanResidualAtom::Concept {
                concept: record.sub,
                term: role_variable.clone(),
            }],
            head: vec![LeanResidualAtom::Role {
                role: record.role,
                source: role_variable.clone(),
                target: LeanRawTerm::Fun {
                    function: record.function,
                    argument: Box::new(role_variable),
                },
            }],
        });
        source_ontology.push(LeanResidualClause {
            body: vec![LeanResidualAtom::Concept {
                concept: record.sub,
                term: filler_variable.clone(),
            }],
            head: vec![LeanResidualAtom::Concept {
                concept: record.filler,
                term: LeanRawTerm::Fun {
                    function: record.function,
                    argument: Box::new(filler_variable),
                },
            }],
        });
    }
    source_ontology.extend(
        residual_compilations
            .iter()
            .map(|compilation| compilation.raw.clone()),
    );
    // The wire variable universe covers the complete source partition, not
    // only the direct clauses and canonical witnesses. Residual raw clauses
    // can introduce additional variables, including below function terms.
    fn variable_bound(term: &LeanRawTerm) -> Result<u32, String> {
        match term {
            LeanRawTerm::Var { name } => name.checked_add(1)
                .ok_or_else(|| "source variable id exceeds certificate range".into()),
            LeanRawTerm::Fun { argument, .. } => variable_bound(argument),
        }
    }
    let variable_count = source_ontology.iter()
        .flat_map(|clause| clause.body.iter().chain(&clause.head))
        .try_fold(0u32, |bound, atom| -> Result<u32, String> {
            let count = match atom {
                LeanResidualAtom::Concept { term, .. } => variable_bound(term)?,
                LeanResidualAtom::Role { source, target, .. } =>
                    variable_bound(source)?.max(variable_bound(target)?),
                LeanResidualAtom::Eq { left, right } =>
                    variable_bound(left)?.max(variable_bound(right)?),
            };
            Ok(bound.max(count))
        })?;
    let mut concept_origins = vec![LeanConceptOrigin::Source; symbol_count];
    for (&id, prefix_ids) in &nfs.conjunction_origins {
        let slot = concept_origins
            .get_mut(id as usize)
            .ok_or_else(|| format!("origin id {id} out of bounds"))?;
        *slot = LeanConceptOrigin::Conjunction {
            prefix_ids: prefix_ids.clone(),
        };
    }
    Ok(LeanElCertificate {
        version: 5,
        symbol_count: symbol_count as u32,
        top: TOP,
        bottom: BOTTOM,
        variable_count,
        source_ontology,
        raw_ontology,
        witness_records,
        residual_compilations,
        concept_origins,
        ontology,
        trace: steps,
        active_concepts,
        rust_subsumptions,
        rust_edges,
        public_subsumptions,
        symbols: interner.cloned_names(),
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
    #[track_caller]
    fn add_sub_parts(
        sub_super: &mut [HashSet<u32>],
        worklist: &mut Worklist,
        journal: &mut Option<Vec<(u32, u32)>>,
        c: u32,
        d: u32,
    ) {
        if sub_super[c as usize].insert(d) {
            if c as usize == DEBUG_ADD_SUB_NODE.load(Ordering::Relaxed)
                && d as usize == DEBUG_ADD_SUB_CONCEPT.load(Ordering::Relaxed)
                && DEBUG_ADD_SUB_COUNT.fetch_add(1, Ordering::Relaxed) < 32
            {
                let caller = std::panic::Location::caller();
                eprintln!(
                    "KM_ELC_CERT target insertion: concept={d} node={c} caller={}:{}",
                    caller.file(),
                    caller.line(),
                );
            }
            worklist.push(Item::Sub(c, d));
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
    #[track_caller]
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
            self.worklist.push(Item::Edge(c, r, d));
        }
    }

    fn remove_edge(&mut self, c: u32, r: u32, d: u32) -> bool {
        if !self.edges[c as usize].remove(&(r, d)) {
            return false;
        }
        self.edge_epoch += 1;
        let key = (d, r);
        let mut empty = false;
        if let Some(parents) = self.in_by_role.get_mut(&key) {
            parents.retain(|&parent| parent != c);
            empty = parents.is_empty();
        }
        if empty {
            self.in_by_role.remove(&key);
            self.in_roles[d as usize].retain(|&role| role != r);
        }
        true
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
            worklist: self.worklist.new_like(),
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
/// Append one pair at a record list's write cursor.
#[inline]
fn pool_push_pair(pool: &mut [u32], at: &mut u32, first: u32, second: u32) {
    let p = *at as usize;
    pool[p] = first;
    pool[p + 1] = second;
    *at += 2;
}

/// Build the read-only rule indexes (including the role-hierarchy closure).
fn build_idx(nfs: &Nfs, n: usize) -> Idx {
    // ----- per-trigger rule records, back to back in one pool -----
    // Two linear passes over the normal forms: count the entries of every
    // trigger's four lists, then place each record at its offset and fill
    // the lists in axiom order. Each per-trigger sequence is exactly the one
    // the previous construction pushed into four growing vectors per trigger
    // inside a hash map and then boxed (about four allocations per
    // rule-bearing symbol plus their growth steps, and as many frees at
    // release); here the whole index is one allocation.
    let width = nfs
        .nf1
        .iter()
        .map(|a| a.sub)
        .chain(nfs.nf2.iter().flat_map(|a| [a.sub1, a.sub2]))
        .chain(nfs.nf3.iter().map(|a| a.sub))
        .chain(nfs.nf4.iter().map(|a| a.filler))
        .chain(nfs.nf5.iter().copied())
        .map(|trigger| trigger as usize + 1)
        .max()
        .map_or(n, |last| n.max(last));
    let mut counts = vec![[0u32; 4]; width];
    for a in &nfs.nf1 {
        counts[a.sub as usize][0] += 1;
    }
    for a in &nfs.nf2 {
        // Indexed under both operands; each entry stores the OTHER operand and
        // the conclusion, so whichever operand is derived second finds the
        // first one already in the label (R⊓ needs both). The join itself
        // (`fire_nf2`) enumerates the smaller of the two sides, so a hub
        // operand shared by thousands of conjunctions costs one label scan
        // per arrival rather than a rescan of every incident axiom.
        counts[a.sub1 as usize][1] += 1;
        counts[a.sub2 as usize][1] += 1;
    }
    for a in &nfs.nf3 {
        counts[a.sub as usize][2] += 1;
    }
    // NF4 (∃R.D⊑E) indexed by filler D -> [(role R, sup E)]. The Sub rule reads
    // it to register propagations; the Edge rule consults the `prop` store the
    // Sub rule fills, so no `(role,filler)` index is needed.
    for a in &nfs.nf4 {
        counts[a.filler as usize][3] += 1;
    }
    let mut bottom = vec![false; width];
    for &sub in &nfs.nf5 {
        bottom[sub as usize] = true;
    }
    let has_nf4 = !nfs.nf4.is_empty();
    // Records are laid out in ascending symbol order (a deterministic layout
    // that keeps neighbouring triggers adjacent).
    let mut rule_slot = vec![NO_RULES; width];
    let mut total = 0usize;
    for (d, &[n1, n2, n3, n4]) in counts.iter().enumerate() {
        if n1 | n2 | n3 | n4 == 0 && !bottom[d] {
            continue;
        }
        debug_assert!(
            n1 & RULE_BOTTOM_FLAG == 0,
            "NF1 list length collides with the NF5 flag"
        );
        rule_slot[d] = total as u32;
        total += RULE_HEADER_WORDS + n1 as usize + 2 * (n2 as usize + n3 as usize + n4 as usize);
    }
    assert!(
        total < NO_RULES as usize,
        "EL rule pool of {total} words exceeds the u32 offset range"
    );
    let mut pool = vec![0u32; total];
    // Write the headers and turn the counters into write cursors: the absolute
    // pool position of the next free entry of each of the trigger's lists.
    let mut cursor = counts;
    for (d, &slot) in rule_slot.iter().enumerate() {
        if slot == NO_RULES {
            continue;
        }
        let o = slot as usize;
        let [n1, n2, n3, n4] = cursor[d];
        pool[o] = n1 | if bottom[d] { RULE_BOTTOM_FLAG } else { 0 };
        pool[o + 1] = n2;
        pool[o + 2] = n3;
        pool[o + 3] = n4;
        let nf1 = o + RULE_HEADER_WORDS;
        let nf2 = nf1 + n1 as usize;
        let nf3 = nf2 + 2 * n2 as usize;
        let nf4 = nf3 + 2 * n3 as usize;
        cursor[d] = [nf1 as u32, nf2 as u32, nf3 as u32, nf4 as u32];
    }
    drop(bottom);
    // Fill in axiom order.
    for a in &nfs.nf1 {
        let at = &mut cursor[a.sub as usize][0];
        pool[*at as usize] = a.sup;
        *at += 1;
    }
    for a in &nfs.nf2 {
        pool_push_pair(&mut pool, &mut cursor[a.sub1 as usize][1], a.sub2, a.sup);
        pool_push_pair(&mut pool, &mut cursor[a.sub2 as usize][1], a.sub1, a.sup);
    }
    for a in &nfs.nf3 {
        pool_push_pair(&mut pool, &mut cursor[a.sub as usize][2], a.role, a.filler);
    }
    for a in &nfs.nf4 {
        pool_push_pair(&mut pool, &mut cursor[a.filler as usize][3], a.role, a.sup);
    }
    drop(cursor);
    // Sorting the candidate lists changes index order, not the set of axioms
    // or conclusions: NF2 by partner for the label-side binary search, NF4 by
    // role so the sub-side join visits only the exact-role range of a
    // backward-link bucket instead of scanning and rejecting every axiom
    // attached to the filler.
    for &slot in &rule_slot {
        if slot == NO_RULES {
            continue;
        }
        let o = slot as usize;
        let n1 = (pool[o] & !RULE_BOTTOM_FLAG) as usize;
        let n2 = pool[o + 1] as usize;
        let n3 = pool[o + 2] as usize;
        let n4 = pool[o + 3] as usize;
        let nf2 = o + RULE_HEADER_WORDS + n1;
        let nf3 = nf2 + 2 * n2;
        let nf4 = nf3 + 2 * n3;
        pool[nf2..nf3].as_chunks_mut::<2>().0.sort_unstable();
        pool[nf4..nf4 + 2 * n4]
            .as_chunks_mut::<2>()
            .0
            .sort_unstable();
    }
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
        rule_slot,
        pool,
        has_nf4,
        nf7_by_pair,
        role_sub,
        reflexive_closed,
    }
}

/// Fresh state seeded with the Init rule R₀: C ⊑ C and C ⊑ ⊤ for every concept.
/// The worklist discipline is the environment's (`Worklist::from_env`).
fn init_state(nfs: &Nfs, n: usize) -> State {
    init_state_with(nfs, n, Worklist::from_env(n))
}

/// `init_state` over an explicit worklist (the differential tests run the
/// same terminology under both disciplines).
fn init_state_with(nfs: &Nfs, n: usize, worklist: Worklist) -> State {
    let mut st = State {
        sub_super: vec![HashSet::default(); n],
        edges: vec![HashSet::default(); n],
        in_by_role: HashMap::default(),
        in_roles: vec![Vec::new(); n],
        prop: HashMap::default(),
        worklist,
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
    nf2_scan: u64, // NF2 candidates (direct scan) or label members (label-side join) examined
    nf2_label_side: u64, // Sub items whose R⊓ join enumerated the label instead of the candidates
    nf3_scan: u64,
    nf4_sub_scan: u64,  // exact-role (backward link, axiom) pairs fired sub-side
    nf4_edge_scan: u64, // (super_role, d_super) lookups in the Edge-NF4 rule
    nf7_scan: u64,      // out-edges scanned in the NF7 rule
    botback: u64,
    nf4_batch_calls: u64,
    nf4_batch_edges: u64,
    nf4_batch_groups: u64,
    nf4_batch_missing: u64,
    ctx_activations: u64, // context activations of the contextual worklist (0 under the FIFO)
    // Context-parallel saturation only (see `Shard`). `link_items` counts the
    // target half of the edge rules, which the serial engine runs inside the
    // Edge item counted by `edge_items`, so the two are equal and both equal
    // the number of derived edges.
    link_items: u64,
    par_workers: u64,
    par_batches: u64,
    par_messages: u64,
}

impl Prof {
    /// Fold a worker's counters into the run's. The item and per-item scan
    /// counters are additive over the workers because every fact is derived,
    /// and hence processed, by exactly one of them.
    fn merge(&mut self, other: &Prof) {
        self.sub_items += other.sub_items;
        self.edge_items += other.edge_items;
        self.nf1_scan += other.nf1_scan;
        self.nf2_scan += other.nf2_scan;
        self.nf2_label_side += other.nf2_label_side;
        self.nf3_scan += other.nf3_scan;
        self.nf4_sub_scan += other.nf4_sub_scan;
        self.nf4_edge_scan += other.nf4_edge_scan;
        self.nf7_scan += other.nf7_scan;
        self.botback += other.botback;
        self.nf4_batch_calls += other.nf4_batch_calls;
        self.nf4_batch_edges += other.nf4_batch_edges;
        self.nf4_batch_groups += other.nf4_batch_groups;
        self.nf4_batch_missing += other.nf4_batch_missing;
        self.ctx_activations += other.ctx_activations;
        self.link_items += other.link_items;
        self.par_batches += other.par_batches;
        self.par_messages += other.par_messages;
    }
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
fn fire_edge_nf4_batch(idx: &Idx, st: &mut State, prof: &mut Prof, parallel_nf4: bool) -> bool {
    if !parallel_nf4 || !idx.has_nf4 {
        return false;
    }
    // The batch is defined over a consecutive edge frontier at the front of
    // one global queue. The context-local discipline has no such frontier
    // (each context joins its own edges while its label is hot), so it keeps
    // the ordinary edge-side join.
    let Worklist::Fifo(queue) = &st.worklist else {
        return false;
    };
    let edge_count = queue
        .iter()
        .take(PAR_NF4_MAX_EDGES)
        .take_while(|item| matches!(item, Item::Edge(..)))
        .count();
    if edge_count < PAR_NF4_MIN_EDGES {
        return false;
    }

    let mut edges = Vec::with_capacity(edge_count);
    for _ in 0..edge_count {
        let Some(Item::Edge(c, r, d)) = st.worklist.pop() else {
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
            st.worklist.push_next(Item::EdgeSerial(c, r, d));
        }
        return true;
    }

    let mut by_parent: HashMap<u32, Vec<(u32, u32)>> = HashMap::default();
    for &(c, r, d) in &edges {
        by_parent.entry(c).or_default().push((r, d));
    }
    if by_parent.len().saturating_mul(2) > edge_count {
        for (c, r, d) in edges.into_iter().rev() {
            st.worklist.push_next(Item::EdgeSerial(c, r, d));
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
        st.worklist.push_next(Item::EdgeAfterNf4(c, r, d));
    }
    true
}

/// A Sub item enumerates its context's label instead of its NF2 candidate
/// list once the list is more than this many times longer than the label.
/// Each label-side step is a binary search (a handful of comparisons) where a
/// direct step is one hash probe, so the label side must be clearly smaller
/// to pay; the bound keeps the join within a small constant of the cheaper
/// side in either regime.
const NF2_LABEL_SIDE_RATIO: usize = 8;

/// R⊓ for one newly derived subsumer of `c` whose candidate list is `cands`
/// (`(partner, conclusion)`, sorted by partner). The rule needs the join of
/// that list with the label of `c`; this enumerates whichever side is smaller
/// (ELK's `ObjectIntersectionFromConjunctRule` does the same). Both branches
/// fire exactly the conclusions `E` with `(X, E) ∈ cands` and `X ∈ label(c)`,
/// so the derived set is identical either way; only the order in which those
/// conclusions are queued differs, which the finite monotone closure does not
/// see. The label side collects into `scratch` while the label is borrowed
/// and applies the conclusions afterwards.
#[inline]
fn fire_nf2(cands: &[[u32; 2]], st: &mut State, scratch: &mut Vec<u32>, prof: &mut Prof, c: u32) {
    let label_len = st.sub_super[c as usize].len();
    if cands.len() <= label_len.saturating_mul(NF2_LABEL_SIDE_RATIO) {
        prof.nf2_scan += cands.len() as u64;
        for &[other, sup] in cands {
            if st.sub_super[c as usize].contains(&other) {
                st.add_sub(c, sup);
            }
        }
        return;
    }
    prof.nf2_scan += label_len as u64;
    prof.nf2_label_side += 1;
    debug_assert!(scratch.is_empty());
    for &present in st.sub_super[c as usize].iter() {
        let from = cands.partition_point(|&[other, _]| other < present);
        for &[other, sup] in &cands[from..] {
            if other != present {
                break;
            }
            scratch.push(sup);
        }
    }
    for sup in scratch.drain(..) {
        st.add_sub(c, sup);
    }
}

/// Drop a dead, allocation-heavy value. By default this is the ordinary inline
/// drop. With `KM_ELC_BG_DROP` set the frees run on a detached thread, so the
/// completion no longer waits on its critical path for the millions of small
/// `free` calls of a parsed clause set or of the saturation indexes.
/// Scheduling only: nothing derived depends on when memory is returned, the
/// value is unreachable either way, and a failed spawn drops the closure (and
/// so the value) inline exactly as without the flag.
fn release<T: Send + 'static>(value: T, background: bool) {
    if !background {
        drop(value);
        return;
    }
    let _ = std::thread::Builder::new()
        .name("elc-release".into())
        .spawn(move || drop(value));
}

/// Run the completion rules to fixpoint over whatever is on `st`'s worklist.
/// Re-entrant: the certificate repair re-enters with extra seeded facts and the
/// SAME `idx` (the rule set never changes), so a repaired structure is again
/// closed under every EL rule — i.e. it stays a model of the EL clause set.
/// The order in which items are processed is the worklist's discipline (see
/// `Worklist`); the rule code below is the same under either.
fn run(idx: &Idx, st: &mut State, prof: &mut Prof) {
    run_inner(idx, st, prof, None);
}

fn run_with_fresh_inverse(
    idx: &Idx,
    st: &mut State,
    prof: &mut Prof,
    fresh: &mut FreshInverseWitnesses,
) {
    run_inner(idx, st, prof, Some(fresh));
}

fn run_inner(
    idx: &Idx,
    st: &mut State,
    prof: &mut Prof,
    mut fresh: Option<&mut FreshInverseWitnesses>,
) {
    // Empty fallback so an unindexed role still yields the empty super-set
    // without a per-lookup allocation (it never occurs for edge roles in
    // practice, but keeps the borrow simple).
    let empty: HashSet<u32> = HashSet::default();
    // Conclusions gathered while the label of the current context is being
    // iterated (the label-side join in `fire_nf2`), applied once that borrow
    // ends. Kept across items so the join stops allocating after first use.
    let mut nf2_scratch: Vec<u32> = Vec::new();

    // ----- Main loop -----
    // `idx` is borrowed immutably throughout; `st` mutably. Because they are
    // distinct objects, a rule can scan an index slice while pushing into the
    // state. Snapshots (`.collect()`) are taken only when iterating one of the
    // state's *own* mutated collections (sub_super[d], edges[d], the backward
    // links of c).
    let parallel_nf4 = std::env::var_os("KM_ELC_PAR_NF4").is_some();
    let activations_before = st.worklist.activations();
    loop {
        if fire_edge_nf4_batch(idx, st, prof, parallel_nf4) {
            continue;
        }
        let Some(item) = st.worklist.pop() else {
            break;
        };
        match item {
            Item::Sub(c, d) => {
                prof.sub_items += 1;
                // One dense lookup serves every rule keyed by the new subsumer
                // `d`. The rules keep their established firing order (NF1,
                // NF2, NF5, NF3, ⊥ back-propagation, NF4), so NF1 conclusions
                // are visible to NF2 immediately just as before.
                let rules = idx.rules_of(d);
                if let Some(rules) = rules {
                    // R⊑ : C ⊑ D, D ⊑ E ⟹ C ⊑ E  (NF1)
                    prof.nf1_scan += rules.nf1_sups.len() as u64;
                    for &sup in rules.nf1_sups.iter() {
                        if c as usize == DEBUG_ADD_SUB_NODE.load(Ordering::Relaxed)
                            && sup as usize == DEBUG_ADD_SUB_CONCEPT.load(Ordering::Relaxed)
                            && !st.sub_super[c as usize].contains(&sup)
                        {
                            eprintln!(
                                "KM_ELC_CERT target NF1 trigger: node={c} sub={d} sup={sup}"
                            );
                        }
                        st.add_sub(c, sup);
                    }
                    // R⊓ : C ⊑ D, C ⊑ D', D ⊓ D' ⊑ E ⟹ C ⊑ E  (NF2)
                    if !rules.nf2_cand.is_empty() {
                        fire_nf2(rules.nf2_cand, st, &mut nf2_scratch, prof, c);
                    }
                    // R⊥ : D ⊑ ⊥ axiomatically (NF5) ⟹ C ⊑ ⊥
                    if rules.bottom {
                        st.add_sub(c, BOTTOM);
                    }
                    // R∃ : C ⊑ D, D ⊑ ∃R.E ⟹ edge (C,R,E)  (NF3)
                    prof.nf3_scan += rules.nf3_edges.len() as u64;
                    for &[role, filler] in rules.nf3_edges {
                        let target = match fresh.as_deref_mut() {
                            Some(fresh) => fresh.target(st, c, role, filler),
                            None => filler,
                        };
                        st.add_edge(c, role, target);
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
                if let Some(rules) = rules {
                    let axs: &[[u32; 2]] = rules.nf4_axioms;
                    if !axs.is_empty() {
                        for &[s, e] in axs {
                            // No dedup: each (c,s,e) propagation is pushed ~once in EL
                            // (measured bucket-duplication on the 8737 giant is <0.5%),
                            // so ELK's `propagatedSubsumers_` Set buys nothing here and
                            // a `contains` guard only adds cost. The residual `add_sub`
                            // re-fires are confluence (the same `c⊑E` reached via many
                            // edges), which ELK's join pays identically.
                            st.prop.entry((c, s)).or_default().push(e);
                        }
                        // A context with no backward links at all has nothing to
                        // join sub-side yet; the propagations registered above
                        // serve its future edges. Skip the exact-role bucket
                        // probes instead of missing them one role at a time.
                        if !st.in_roles[c as usize].is_empty() {
                            let State {
                                sub_super,
                                in_by_role,
                                worklist,
                                sub_journal,
                                ..
                            } = &mut *st;
                            // `axs` is role-sorted (build_idx), so each iteration
                            // handles one contiguous exact-role group [lo..hi).
                            let mut lo = 0;
                            while lo < axs.len() {
                                let role = axs[lo][0];
                                let hi = axs.partition_point(|&[s, _]| s <= role);
                                if let Some(parents) = in_by_role.get(&(c, role)) {
                                    prof.nf4_sub_scan += (parents.len() * (hi - lo)) as u64;
                                    for &parent in parents {
                                        for &[_, e] in &axs[lo..hi] {
                                            if parent as usize
                                                == DEBUG_ADD_SUB_NODE.load(Ordering::Relaxed)
                                                && e as usize
                                                    == DEBUG_ADD_SUB_CONCEPT.load(Ordering::Relaxed)
                                                && !sub_super[parent as usize].contains(&e)
                                            {
                                                eprintln!(
                                                    "KM_ELC_CERT target NF4 trigger: parent={parent} \
                                                     role={role} filler_node={c} filler_sup={d} sup={e}"
                                                );
                                            }
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
                }
            }
            Item::Edge(c, r, d) | Item::EdgeSerial(c, r, d) | Item::EdgeAfterNf4(c, r, d) => {
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
                if !nf4_already_fired && idx.has_nf4 {
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
    prof.ctx_activations += st.worklist.activations() - activations_before;
}

// ---------------------------------------------------------------------------
// Context-parallel saturation
// ---------------------------------------------------------------------------
//
// The serial completion above already decomposes the work by *context*: an
// item belongs to the subject of a subsumption or the source of an edge, and
// `Worklist::Contextual` drains one activated context at a time (see
// `Worklist`). This section runs that decomposition on several threads.
//
// Ownership. Context `c` is owned by worker `c % W` and stored at slot
// `c / W` of that worker's dense tables. A worker holds the whole mutable
// state of the contexts it owns and nothing else: the label `sub_super[c]`,
// the forward edges `edges[c]`, the backward links `in_by_role[(c, ·)]` with
// their role list `in_roles[c]`, and the propagations `prop[(c, ·)]`. Nothing
// is shared and nothing is locked on the rule path; the rule indexes (`Idx`)
// are immutable and read by every worker.
//
// Locality of the rules. A conclusion about another context is a message to
// its owner, exactly as in ELK's concurrent saturation (Kazakov, Krötzsch,
// Simančík, JAR 2014, §5). This is possible because every join of the
// calculus has both of its premises in ONE context, once the edge rules are
// split into the two halves that the serial arm fuses:
//
//   * `PItem::Sub(c, d)` runs at `c`: NF1, NF2 and NF5 read and extend the
//     label of `c`; NF3 extends the forward edges of `c`; the NF4 filler
//     registration extends `prop[(c, ·)]` and joins it against the backward
//     links `in_by_role[(c, ·)]`; ⊥ back-propagation walks the same links.
//     The conclusions that leave `c` (`⊥` and the NF4 conclusions of the
//     predecessors) are `Msg::Sub`.
//   * `PItem::Fwd(c, r, d)` runs at the SOURCE `c` of a new edge: the role
//     lift `R ⊑ S`, and the NF7 compositions whose middle context is `c`
//     (backward links of `c` composed with this new forward link). Both
//     premises are at `c`; the conclusions are edges of the predecessors,
//     sent as `Msg::Edge`.
//   * `PItem::Link(c, r, d)` runs at the TARGET `d` of the same new edge: the
//     edge-side NF4 join against `prop[(d, r)]`, the ⊥ check on the label of
//     `d`, and the NF7 compositions whose middle context is `d` (this new
//     backward link composed with the forward edges of `d`). Both premises
//     are at `d`; the conclusions belong to `c` and are sent as `Msg::Sub`
//     and `Msg::Edge`.
//
// The serial Edge arm performs the `Link` half at the source while reading
// the target's `prop`, label and edge set; splitting it moves those three
// reads into the context that owns them. No rule reads a context it does not
// own.
//
// Confluence. The completion is a finite monotone closure, so the least
// fixpoint does not depend on the order in which rule instances fire, only on
// every applicable instance firing at least once. Every fact is inserted into
// the owning worker's table exactly once (the insert guards on
// `HashSet::insert` / the new-edge branch) and queues exactly one item, so
// each rule instance with a single premise fires exactly once. Each two-premise
// join is intra-context, hence totally ordered by its owner's thread, and both
// sides register before they scan:
//
//   * NF2 (`D ⊓ D' ⊑ E` at `c`): both premises are members of `sub_super[c]`;
//     the item for a member is queued after the member is inserted, and scans
//     the label for the partner.
//   * NF4 (`∃R.X ⊑ E` at `d`): `prop[(d, R)]` is extended by the `Sub` item of
//     the filler `X`, which then scans `in_by_role[(d, R)]`; a backward link is
//     appended to `in_by_role[(d, R)]` by the message that queues the `Link`
//     item, which then scans `prop[(d, R)]`.
//   * ⊥ over an edge (at `d`): `Sub(d, ⊥)` scans the backward links; a `Link`
//     item scans the label for `⊥`.
//   * NF7 (`R ∘ S ⊑ T` at the middle context `m`): a `Link` item is queued
//     after its link is in `in_by_role[(m, ·)]` and scans `edges[m]`; a `Fwd`
//     item is queued after its edge is in `edges[m]` and scans
//     `in_by_role[(m, ·)]`.
//
// In each case, if the side that arrived first missed the second, the second
// cannot miss the first: the first was in its own table before the second was
// created (all four sequences happen on one thread). So every join fires, and
// the derived set is the same least fixpoint the serial `run` computes.
//
// Termination. A worker holds one *busy* credit in `ParShared::credit` while
// it has anything to do, and each published message batch holds one credit of
// its own, taken before the batch becomes visible and released by the receiver
// after the batch has been applied (the receiver re-takes its busy credit
// first). A worker releases its busy credit only when its queue is empty, its
// outgoing buffers are flushed and its inbox is empty. `credit == 0` therefore
// certifies that no worker is running, no item is queued and no message is in
// flight; and since new work is only ever created while holding a credit, zero
// is stable. Workers exit exactly on that observation.
//
// Determinism. The fixpoint is unique, but the *iteration order* of a label
// depends on the order its members arrived, which a parallel run does not fix.
// Each worker therefore rebuilds the label sets of its contexts from a sorted
// vector before it exits, so `sub_super` iterates in ascending id order and
// the classification output is byte-identical for any worker count and any
// interleaving. The remaining tables (edges, links, propagations) are consumed
// as sets by the rules and are released before the output is built.
//
// Scope. The mode is opt-in (`KM_ELC_PAR_CTX`) and declines wherever the
// serial engine's ORDER is load-bearing rather than its result: the FIFO
// disciplines (`KM_ELC_PAR_NF4`'s frontier batch and `KM_ELC_FIFO`) and every
// certificate mode, whose repair pass forks the state and picks representatives
// and blame witnesses in construction order. Those keep the serial engine
// exactly as before.

/// A conclusion for a context this worker does not own. Sent to that context's
/// owner, which applies it to its own tables.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Msg {
    /// `d` is a subsumer of `c`. Applied by the owner of `c`.
    Sub(u32, u32),
    /// The edge `(c, r, d)` holds. Applied by the owner of `c`, which owns the
    /// forward edge set of `c`.
    Edge(u32, u32, u32),
    /// The edge `(c, r, d)` holds. Applied by the owner of `d` as a backward
    /// link of `d`; sent by the owner of `c` when the forward edge is new, so
    /// exactly one link is registered per distinct edge.
    Link(u32, u32, u32),
}

/// A pending item of an owned context.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PItem {
    /// `d` was just added to the label of `c`: the Sub rules of `c`.
    Sub(u32, u32),
    /// `(c, r, d)` was just added to the forward edges of `c`: the source half
    /// of the edge rules (role lift, NF7 with `c` as the middle context).
    Fwd(u32, u32, u32),
    /// `(c, r, d)` was just added to the backward links of `d`: the target half
    /// of the edge rules (NF4 propagation join, ⊥ check, NF7 with `d` as the
    /// middle context).
    Link(u32, u32, u32),
}

/// Per-owned-context item chains plus the activation queue, the shard-local
/// counterpart of [`ContextQueue`]. Indexed by the owner's dense slot
/// (`c / workers`) rather than by the context id, so the tables of a shard
/// cost one entry per context it owns and nothing for the others.
struct ShardQueue {
    head: Vec<u32>,
    slots: Vec<(PItem, u32)>,
    free: Vec<u32>,
    active: VecDeque<u32>,
    queued: Vec<bool>,
    current: u32,
    len: usize,
    activations: u64,
}

impl ShardQueue {
    fn new(owned: usize) -> ShardQueue {
        ShardQueue {
            head: vec![NO_ITEM; owned],
            slots: Vec::new(),
            free: Vec::new(),
            active: VecDeque::new(),
            queued: vec![false; owned],
            current: NO_CONTEXT,
            len: 0,
            activations: 0,
        }
    }

    #[inline]
    fn push(&mut self, slot: usize, item: PItem) {
        let next = self.head[slot];
        let cell = match self.free.pop() {
            Some(cell) => {
                self.slots[cell as usize] = (item, next);
                cell
            }
            None => {
                self.slots.push((item, next));
                (self.slots.len() - 1) as u32
            }
        };
        self.head[slot] = cell;
        self.len += 1;
        if !self.queued[slot] {
            self.queued[slot] = true;
            self.active.push_back(slot as u32);
        }
    }

    /// The next item: the current context's most recently queued item while it
    /// has any, else the first item of the next activated context.
    #[inline]
    fn pop(&mut self) -> Option<PItem> {
        loop {
            if self.current != NO_CONTEXT {
                let slot = self.current as usize;
                let cell = self.head[slot];
                if cell != NO_ITEM {
                    let (item, next) = self.slots[cell as usize];
                    self.head[slot] = next;
                    self.free.push(cell);
                    self.len -= 1;
                    return Some(item);
                }
                self.queued[slot] = false;
                self.current = NO_CONTEXT;
            }
            let slot = self.active.pop_front()?;
            self.current = slot;
            self.activations += 1;
        }
    }
}

/// One worker's inbox. `len` is a lock-free "has batches" hint maintained under
/// the mutex, so the hot idle check costs one atomic load.
struct Mailbox {
    batches: Mutex<Vec<Vec<Msg>>>,
    len: AtomicUsize,
}

/// State shared by the workers: the inboxes, the termination credit and the
/// startup handshake.
struct ParShared {
    boxes: Vec<Mailbox>,
    /// One credit per busy worker plus one per published, unconsumed batch.
    /// Zero certifies global quiescence (see the section header).
    credit: AtomicUsize,
    /// Set once every worker thread has been spawned. A worker that observes
    /// `abort` before `started` exits without touching the state, so a failed
    /// spawn cannot leave the already-spawned workers waiting for a worker that
    /// will never run.
    started: AtomicBool,
    abort: AtomicBool,
}

impl ParShared {
    fn new(workers: usize) -> ParShared {
        ParShared {
            boxes: (0..workers)
                .map(|_| Mailbox {
                    batches: Mutex::new(Vec::new()),
                    len: AtomicUsize::new(0),
                })
                .collect(),
            credit: AtomicUsize::new(workers),
            started: AtomicBool::new(false),
            abort: AtomicBool::new(false),
        }
    }
}

/// Messages a worker buffers before it publishes what it has. Larger batches
/// amortize the receiver's mutex and the credit atomics; smaller ones keep a
/// receiver from idling while the sender is in a long burst.
const PAR_FLUSH_MESSAGES: usize = 1024;

/// Emptied inbox buffers a worker keeps to refill its own outgoing buffers.
/// Uncapped, a worker that receives more than it sends would hold every batch
/// buffer that ever reached it.
const PAR_SPARE_BUFFERS: usize = 8;

/// Items a worker processes before it looks at its inbox again. A context's
/// chain can run for millions of items without emptying the queue, and the
/// conclusions the other workers send meanwhile are mostly facts the receiver
/// already has (the serial engine rejects them at `HashSet::insert`; a sender
/// cannot know). Polling bounds the backlog by the arrival rate over this many
/// items instead of by the whole run: applying a message is one hash probe and
/// turns a stream of duplicates into at most one queued item per derived fact.
const PAR_INBOX_POLL: usize = 256;

/// Conclusion sink over the pieces of a [`Shard`] a rule may extend while it
/// scans another of the shard's tables (its backward links, its propagations,
/// its edges). Keeping the sink to these fields is what lets the rule bodies
/// iterate the shard's own indexes in place, exactly as the serial arms do.
struct Sink<'s> {
    id: usize,
    workers: usize,
    sub_super: &'s mut Vec<HashSet<u32>>,
    edges: &'s mut Vec<HashSet<(u32, u32)>>,
    queue: &'s mut ShardQueue,
    out: &'s mut Vec<Vec<Msg>>,
    /// Backward links for contexts of THIS shard, registered once the rule that
    /// created the edge has stopped iterating (`in_by_role` is the one table a
    /// rule may be scanning while it creates an edge).
    self_links: &'s mut Vec<(u32, u32, u32)>,
    pending: &'s mut usize,
    edges_total: &'s mut u64,
}

impl Sink<'_> {
    #[inline]
    fn owner(&self, c: u32) -> usize {
        c as usize % self.workers
    }

    #[inline]
    fn slot(&self, c: u32) -> usize {
        c as usize / self.workers
    }

    /// `c ⊑ d`, wherever `c` lives.
    #[inline]
    fn sub(&mut self, c: u32, d: u32) {
        let owner = self.owner(c);
        if owner == self.id {
            let slot = self.slot(c);
            if self.sub_super[slot].insert(d) {
                self.queue.push(slot, PItem::Sub(c, d));
            }
        } else {
            self.out[owner].push(Msg::Sub(c, d));
            *self.pending += 1;
        }
    }

    /// The edge `(c, r, d)`, wherever `c` lives. A new edge queues the source
    /// half here and the target half at the owner of `d`.
    #[inline]
    fn edge(&mut self, c: u32, r: u32, d: u32) {
        let owner = self.owner(c);
        if owner != self.id {
            self.out[owner].push(Msg::Edge(c, r, d));
            *self.pending += 1;
            return;
        }
        let slot = self.slot(c);
        if !self.edges[slot].insert((r, d)) {
            return;
        }
        *self.edges_total += 1;
        self.queue.push(slot, PItem::Fwd(c, r, d));
        let target = self.owner(d);
        if target == self.id {
            self.self_links.push((c, r, d));
        } else {
            self.out[target].push(Msg::Link(c, r, d));
            *self.pending += 1;
        }
    }

    /// R⊓ (NF2) for the new subsumer of `c`, the shard-local mirror of
    /// [`fire_nf2`]: enumerate the smaller of the candidate list and the label,
    /// firing exactly the conclusions whose partner is already in the label.
    fn nf2(&mut self, c: u32, cands: &[[u32; 2]], scratch: &mut Vec<u32>, prof: &mut Prof) {
        let slot = self.slot(c);
        let label_len = self.sub_super[slot].len();
        if cands.len() <= label_len.saturating_mul(NF2_LABEL_SIDE_RATIO) {
            prof.nf2_scan += cands.len() as u64;
            for &[other, sup] in cands {
                if self.sub_super[slot].contains(&other) {
                    self.sub(c, sup);
                }
            }
            return;
        }
        prof.nf2_scan += label_len as u64;
        prof.nf2_label_side += 1;
        debug_assert!(scratch.is_empty());
        for &present in self.sub_super[slot].iter() {
            let from = cands.partition_point(|&[other, _]| other < present);
            for &[other, sup] in &cands[from..] {
                if other != present {
                    break;
                }
                scratch.push(sup);
            }
        }
        for i in 0..scratch.len() {
            let sup = scratch[i];
            self.sub(c, sup);
        }
        scratch.clear();
    }
}

/// One worker: the contexts it owns, their pending items, and its outgoing
/// message buffers. The rule indexes are shared and immutable.
struct Shard<'a> {
    id: usize,
    workers: usize,
    idx: &'a Idx,
    shared: &'a ParShared,
    /// Label of the owned context at slot `i`, i.e. of context `i * W + id`.
    sub_super: Vec<HashSet<u32>>,
    edges: Vec<HashSet<(u32, u32)>>,
    in_roles: Vec<Vec<u32>>,
    in_by_role: HashMap<(u32, u32), Vec<u32>>,
    prop: HashMap<(u32, u32), Vec<u32>>,
    queue: ShardQueue,
    /// Outgoing buffer per destination worker (`out[id]` stays empty: a
    /// conclusion for an owned context is applied in place).
    out: Vec<Vec<Msg>>,
    /// Buffers recycled from consumed inboxes, reused for outgoing batches.
    spare: Vec<Vec<Msg>>,
    pending: usize,
    self_links: Vec<(u32, u32, u32)>,
    link_drain: Vec<(u32, u32, u32)>,
    nf2_scratch: Vec<u32>,
    pred_scratch: Vec<(u32, u32)>,
    edge_scratch: Vec<(u32, u32)>,
    edges_total: u64,
    prof: Prof,
}

impl<'a> Shard<'a> {
    fn new(id: usize, workers: usize, n: usize, idx: &'a Idx, shared: &'a ParShared) -> Shard<'a> {
        // Contexts `id, id + W, id + 2W, ...` below `n`.
        let owned = if id < n {
            (n - id).div_ceil(workers)
        } else {
            0
        };
        Shard {
            id,
            workers,
            idx,
            shared,
            sub_super: vec![HashSet::default(); owned],
            edges: vec![HashSet::default(); owned],
            in_roles: vec![Vec::new(); owned],
            in_by_role: HashMap::default(),
            prop: HashMap::default(),
            queue: ShardQueue::new(owned),
            out: (0..workers).map(|_| Vec::new()).collect(),
            spare: Vec::new(),
            pending: 0,
            self_links: Vec::new(),
            link_drain: Vec::new(),
            nf2_scratch: Vec::new(),
            pred_scratch: Vec::new(),
            edge_scratch: Vec::new(),
            edges_total: 0,
            prof: Prof::default(),
        }
    }

    #[inline]
    fn owner(&self, c: u32) -> usize {
        c as usize % self.workers
    }

    #[inline]
    fn slot(&self, c: u32) -> usize {
        c as usize / self.workers
    }

    #[inline]
    fn owns(&self, c: u32) -> bool {
        self.owner(c) == self.id
    }

    /// R₀ (Init) over the owned contexts, plus the EL++ reflexive self-edges:
    /// the same seeds as `init_state` and `seed_reflexive_edges`, restricted to
    /// this shard. Every context is seeded by exactly one worker.
    fn seed(&mut self, nfs: &Nfs) {
        for &c in &nfs.concept_names {
            if c == BOTTOM || !self.owns(c) {
                continue;
            }
            let slot = self.slot(c);
            if self.sub_super[slot].insert(c) {
                self.queue.push(slot, PItem::Sub(c, c));
            }
            if self.sub_super[slot].insert(TOP) {
                self.queue.push(slot, PItem::Sub(c, TOP));
            }
        }
        let idx = self.idx;
        if idx.reflexive_closed.is_empty() {
            return;
        }
        for &c in &nfs.concept_names {
            if c == BOTTOM || !self.owns(c) {
                continue;
            }
            for &r in &idx.reflexive_closed {
                self.create_edge(c, r, c);
            }
        }
    }

    /// Apply a message for one of this shard's contexts.
    #[inline]
    fn apply(&mut self, msg: Msg) {
        match msg {
            Msg::Sub(c, d) => {
                let slot = self.slot(c);
                if self.sub_super[slot].insert(d) {
                    self.queue.push(slot, PItem::Sub(c, d));
                }
            }
            Msg::Edge(c, r, d) => self.create_edge(c, r, d),
            Msg::Link(c, r, d) => self.register_link(c, r, d),
        }
    }

    /// Record the forward edge `(c, r, d)` at the owned source `c`, queue its
    /// source half, and hand the backward link to the owner of `d`. Same
    /// effect as [`Sink::edge`] for an owned source, without the deferral (no
    /// table of this shard is being iterated here).
    fn create_edge(&mut self, c: u32, r: u32, d: u32) {
        let slot = self.slot(c);
        if !self.edges[slot].insert((r, d)) {
            return;
        }
        self.edges_total += 1;
        self.queue.push(slot, PItem::Fwd(c, r, d));
        if self.owns(d) {
            self.register_link(c, r, d);
        } else {
            let target = self.owner(d);
            self.out[target].push(Msg::Link(c, r, d));
            self.pending += 1;
        }
    }

    /// Record the backward link of the owned target `d` and queue its target
    /// half. Called once per distinct edge, so the parent lists hold no
    /// duplicates, exactly as in `State::add_edge`.
    fn register_link(&mut self, c: u32, r: u32, d: u32) {
        let slot = self.slot(d);
        let parents = self.in_by_role.entry((d, r)).or_default();
        if parents.is_empty() {
            self.in_roles[slot].push(r);
        }
        parents.push(c);
        self.queue.push(slot, PItem::Link(c, r, d));
    }

    /// Register the backward links a rule deferred while it was iterating.
    #[inline]
    fn drain_self_links(&mut self) {
        if self.self_links.is_empty() {
            return;
        }
        std::mem::swap(&mut self.self_links, &mut self.link_drain);
        for i in 0..self.link_drain.len() {
            let (c, r, d) = self.link_drain[i];
            self.register_link(c, r, d);
        }
        self.link_drain.clear();
    }

    /// The Sub rules at `c` for its new subsumer `d`: the same rule bodies, in
    /// the same order, as the `Item::Sub` arm of [`run`].
    fn process_sub(&mut self, c: u32, d: u32) {
        let idx = self.idx;
        let rules = idx.rules_of(d);
        let slot = self.slot(c);
        let Shard {
            id,
            workers,
            sub_super,
            edges,
            queue,
            out,
            pending,
            self_links,
            edges_total,
            in_roles,
            in_by_role,
            prop,
            nf2_scratch,
            prof,
            ..
        } = self;
        prof.sub_items += 1;
        let mut sink = Sink {
            id: *id,
            workers: *workers,
            sub_super,
            edges,
            queue,
            out,
            self_links,
            pending,
            edges_total,
        };
        if let Some(rules) = rules {
            // R⊑ (NF1)
            prof.nf1_scan += rules.nf1_sups.len() as u64;
            for &sup in rules.nf1_sups.iter() {
                sink.sub(c, sup);
            }
            // R⊓ (NF2)
            if !rules.nf2_cand.is_empty() {
                sink.nf2(c, rules.nf2_cand, nf2_scratch, prof);
            }
            // R⊥ (NF5)
            if rules.bottom {
                sink.sub(c, BOTTOM);
            }
            // R∃ (NF3)
            prof.nf3_scan += rules.nf3_edges.len() as u64;
            for &[role, filler] in rules.nf3_edges {
                sink.edge(c, role, filler);
            }
        }
        // R⊥-edge, backwards: every predecessor of an unsatisfiable context is
        // unsatisfiable. Reads this shard's own backward links.
        if d == BOTTOM {
            for &role in &in_roles[slot] {
                if let Some(parents) = in_by_role.get(&(c, role)) {
                    prof.botback += parents.len() as u64;
                    for &parent in parents {
                        sink.sub(parent, BOTTOM);
                    }
                }
            }
        }
        // R∃⁻ (NF4): register the propagations of the new filler `d` at `c` for
        // future backward links, and join them with the links already there.
        if let Some(rules) = rules {
            let axs: &[[u32; 2]] = rules.nf4_axioms;
            if axs.is_empty() {
                return;
            }
            for &[s, e] in axs {
                prop.entry((c, s)).or_default().push(e);
            }
            if in_roles[slot].is_empty() {
                return;
            }
            let mut lo = 0;
            while lo < axs.len() {
                let role = axs[lo][0];
                let hi = axs.partition_point(|&[s, _]| s <= role);
                if let Some(parents) = in_by_role.get(&(c, role)) {
                    prof.nf4_sub_scan += (parents.len() * (hi - lo)) as u64;
                    for &parent in parents {
                        for &[_, e] in &axs[lo..hi] {
                            sink.sub(parent, e);
                        }
                    }
                }
                lo = hi;
            }
        }
    }

    /// The source half of the edge rules for the new edge `(c, r, d)`: the NF7
    /// compositions whose middle context is `c`, then the role-hierarchy lift.
    fn process_fwd(&mut self, c: u32, r: u32, d: u32) {
        let idx = self.idx;
        let slot = self.slot(c);
        let Shard {
            id,
            workers,
            sub_super,
            edges,
            queue,
            out,
            pending,
            self_links,
            edges_total,
            in_roles,
            in_by_role,
            pred_scratch,
            prof,
            ..
        } = self;
        prof.edge_items += 1;
        let mut sink = Sink {
            id: *id,
            workers: *workers,
            sub_super,
            edges,
            queue,
            out,
            self_links,
            pending,
            edges_total,
        };
        // R∘ (NF7) with `c` in the middle: a backward link of `c` composed with
        // this new forward link. Only the roles that actually compose with `r`
        // are read out of the backward-link index.
        if !idx.nf7_by_pair.is_empty() {
            let empty: HashSet<u32> = HashSet::default();
            pred_scratch.clear();
            for &r0 in &in_roles[slot] {
                if !idx.nf7_by_pair.contains_key(&(r0, r)) {
                    continue;
                }
                if let Some(ps) = in_by_role.get(&(c, r0)) {
                    pred_scratch.extend(ps.iter().map(|&p| (p, r0)));
                }
            }
            for i in 0..pred_scratch.len() {
                let (parent, r0) = pred_scratch[i];
                if let Some(sups) = idx.nf7_by_pair.get(&(r0, r)) {
                    for &nfsup in sups {
                        for &super_role in idx.role_sub.get(nfsup as usize).unwrap_or(&empty) {
                            sink.edge(parent, super_role, d);
                        }
                    }
                }
            }
        }
        // Role-hierarchy lift: an R-edge is also an S-edge for R ⊑ S.
        for &super_role in idx.role_supers(r) {
            if super_role != r {
                sink.edge(c, super_role, d);
            }
        }
    }

    /// The target half of the edge rules for the new edge `(c, r, d)`, run at
    /// `d`: the edge-side NF4 join against the propagations stored at `d`, the
    /// ⊥ check on the label of `d`, and the NF7 compositions whose middle
    /// context is `d`. These are the three reads the serial Edge arm makes into
    /// the target's tables.
    fn process_link(&mut self, c: u32, r: u32, d: u32) {
        let idx = self.idx;
        let slot = self.slot(d);
        let Shard {
            id,
            workers,
            sub_super,
            edges,
            queue,
            out,
            pending,
            self_links,
            edges_total,
            prop,
            edge_scratch,
            prof,
            ..
        } = self;
        prof.link_items += 1;
        let mut sink = Sink {
            id: *id,
            workers: *workers,
            sub_super,
            edges,
            queue,
            out,
            self_links,
            pending,
            edges_total,
        };
        // R∃⁻ (NF4), ELK backward-link join: the propagations already stored at
        // `d` for this exact role fire into the source `c`.
        if idx.has_nf4 {
            if let Some(es) = prop.get(&(d, r)) {
                prof.nf4_edge_scan += es.len() as u64;
                for &sup in es {
                    sink.sub(c, sup);
                }
            }
        }
        // R⊥-edge: an edge into a known-unsatisfiable target propagates.
        if sink.sub_super[slot].contains(&BOTTOM) {
            sink.sub(c, BOTTOM);
        }
        // R∘ (NF7) with `d` in the middle: this new backward link composed with
        // the forward edges of `d`.
        if !idx.nf7_by_pair.is_empty() {
            let empty: HashSet<u32> = HashSet::default();
            edge_scratch.clear();
            edge_scratch.extend(sink.edges[slot].iter().copied());
            prof.nf7_scan += edge_scratch.len() as u64;
            for i in 0..edge_scratch.len() {
                let (r2, e) = edge_scratch[i];
                if let Some(sups) = idx.nf7_by_pair.get(&(r, r2)) {
                    for &nfsup in sups {
                        for &super_role in idx.role_sub.get(nfsup as usize).unwrap_or(&empty) {
                            sink.edge(c, super_role, e);
                        }
                    }
                }
            }
        }
    }
}

impl Shard<'_> {
    /// Publish the buffered messages for one destination. The credit is taken
    /// BEFORE the batch becomes visible, so the global count never drops to
    /// zero between the sender releasing its own credit and the receiver taking
    /// the batch.
    fn publish(&mut self, to: usize) {
        let shared = self.shared;
        let refill = self.spare.pop().unwrap_or_default();
        let batch = std::mem::replace(&mut self.out[to], refill);
        self.prof.par_batches += 1;
        self.prof.par_messages += batch.len() as u64;
        shared.credit.fetch_add(1, Ordering::SeqCst);
        let mailbox = &shared.boxes[to];
        let mut queued = mailbox.batches.lock().expect("elc parallel mailbox");
        queued.push(batch);
        mailbox.len.store(queued.len(), Ordering::SeqCst);
    }

    /// Publish every non-empty outgoing buffer.
    fn flush(&mut self) {
        for to in 0..self.workers {
            if to == self.id || self.out[to].is_empty() {
                continue;
            }
            self.publish(to);
        }
        self.pending = 0;
    }

    /// Apply everything addressed to this shard. Returns whether anything was
    /// taken. The caller holds a busy credit throughout, so the batch credits
    /// released here cannot bring the global count to zero while their
    /// conclusions are still being applied.
    fn take_inbox(&mut self) -> bool {
        let shared = self.shared;
        let mailbox = &shared.boxes[self.id];
        if mailbox.len.load(Ordering::SeqCst) == 0 {
            return false;
        }
        let mut batches = {
            let mut queued = mailbox.batches.lock().expect("elc parallel mailbox");
            let taken = std::mem::take(&mut *queued);
            mailbox.len.store(0, Ordering::SeqCst);
            taken
        };
        if batches.is_empty() {
            return false;
        }
        shared.credit.fetch_sub(batches.len(), Ordering::SeqCst);
        for mut batch in batches.drain(..) {
            for i in 0..batch.len() {
                self.apply(batch[i]);
                self.drain_self_links();
            }
            if self.spare.len() < PAR_SPARE_BUFFERS {
                batch.clear();
                self.spare.push(batch);
            }
        }
        true
    }

    /// Release the busy credit and wait for work or for global quiescence.
    /// Returns `true` when the saturation is over for every worker.
    fn wait(&mut self) -> bool {
        let shared = self.shared;
        shared.credit.fetch_sub(1, Ordering::SeqCst);
        let mailbox = &shared.boxes[self.id];
        let mut spins = 0u32;
        loop {
            if mailbox.len.load(Ordering::SeqCst) != 0 {
                // Take the busy credit back before consuming, so the count
                // never passes through zero while this worker has work.
                shared.credit.fetch_add(1, Ordering::SeqCst);
                return false;
            }
            if shared.credit.load(Ordering::SeqCst) == 0 {
                return true;
            }
            if shared.abort.load(Ordering::SeqCst) {
                return true;
            }
            spins += 1;
            if spins < 128 {
                std::hint::spin_loop();
            } else if spins < 1024 {
                std::thread::yield_now();
            } else {
                std::thread::sleep(std::time::Duration::from_micros(100));
            }
        }
    }

    /// Saturate: drain the owned contexts, publish, consume, and idle until the
    /// whole worker set is quiescent.
    fn saturate(&mut self) {
        loop {
            let mut since_poll = 0usize;
            while let Some(item) = self.queue.pop() {
                match item {
                    PItem::Sub(c, d) => self.process_sub(c, d),
                    PItem::Fwd(c, r, d) => self.process_fwd(c, r, d),
                    PItem::Link(c, r, d) => self.process_link(c, r, d),
                }
                self.drain_self_links();
                if self.pending >= PAR_FLUSH_MESSAGES {
                    self.flush();
                }
                since_poll += 1;
                if since_poll >= PAR_INBOX_POLL {
                    since_poll = 0;
                    self.take_inbox();
                }
            }
            // Consume before publishing: a worker whose own conclusions keep
            // coming back to it would otherwise publish a batch per drained
            // queue, which is one mutex and one buffer per handful of
            // messages. What is still buffered when it runs out of work is
            // published below, before it can go idle.
            if self.take_inbox() {
                continue;
            }
            self.flush();
            // Nothing is produced between here and the credit release, so a
            // worker never goes idle holding an unpublished conclusion.
            if self.wait() {
                break;
            }
        }
        self.prof.ctx_activations = self.queue.activations;
    }

    /// Rebuild the labels of the owned contexts from sorted vectors, so their
    /// iteration order (which the classification output follows row by row) is
    /// a function of the derived set alone and not of the arrival order of the
    /// conclusions. Runs on the worker that owns the contexts.
    fn canonicalize(&mut self) {
        let mut sorted: Vec<u32> = Vec::new();
        for set in self.sub_super.iter_mut() {
            if set.len() < 2 {
                continue;
            }
            sorted.clear();
            sorted.extend(set.iter().copied());
            sorted.sort_unstable();
            let mut fresh: HashSet<u32> =
                HashSet::with_capacity_and_hasher(sorted.len(), FxBuild::default());
            for &d in sorted.iter() {
                fresh.insert(d);
            }
            *set = fresh;
        }
    }
}

// Test-only worker-count override, so the differential and stress tests can
// drive `classify` on several worker counts without touching the process
// environment other tests read concurrently. Thread-local: it applies to the
// classification the test itself starts and to nothing else.
#[cfg(test)]
thread_local! {
    static TEST_PAR_WORKERS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Auto worker count ceiling: past this the message traffic of the shared
/// conclusions dominates, and the EL route is one worker of a classify run
/// that may already be racing other processes.
const PAR_CTX_AUTO_CAP: usize = 8;

/// The worker count `KM_ELC_PAR_CTX` asks for (`0` = the serial engine).
/// `auto` follows the machine, capped at [`PAR_CTX_AUTO_CAP`].
fn requested_par_workers() -> usize {
    #[cfg(test)]
    {
        let override_workers = TEST_PAR_WORKERS.with(|w| w.get());
        if override_workers != 0 {
            return override_workers;
        }
    }
    match std::env::var("KM_ELC_PAR_CTX") {
        Ok(value) => {
            let value = value.trim().to_ascii_lowercase();
            if value == "auto" {
                std::thread::available_parallelism()
                    .map_or(1, |p| p.get())
                    .min(PAR_CTX_AUTO_CAP)
            } else {
                value.parse::<usize>().unwrap_or(0)
            }
        }
        Err(_) => 0,
    }
}

/// How many workers the context-parallel saturation may use, or `None` for the
/// serial engine. Pure, so the policy is testable without the environment.
///
/// The parallel engine reaches the same fixpoint but not the same construction
/// ORDER, so it declines wherever the order is load-bearing: the FIFO
/// disciplines (`KM_ELC_PAR_NF4`'s consecutive edge frontier and the
/// `KM_ELC_FIFO` A/B baseline) and every certificate mode, whose repair pass
/// forks the saturated state and picks merge representatives and blame
/// witnesses in construction order.
fn context_parallel_plan(
    requested: usize,
    par_nf4: bool,
    fifo: bool,
    cert: CertMode,
    lean_cert_requested: bool,
    symbols: usize,
    available: usize,
) -> Option<usize> {
    if requested < 2 || par_nf4 || fifo || cert != CertMode::Off || lean_cert_requested {
        return None;
    }
    let workers = requested.min(available.max(1)).min(symbols);
    (workers >= 2).then_some(workers)
}

/// The plan for this process and this classification.
fn context_parallel_workers(
    cert: CertMode,
    lean_cert_requested: bool,
    symbols: usize,
) -> Option<usize> {
    context_parallel_plan(
        requested_par_workers(),
        std::env::var_os("KM_ELC_PAR_NF4").is_some(),
        std::env::var_os("KM_ELC_FIFO").is_some(),
        cert,
        lean_cert_requested,
        symbols,
        std::thread::available_parallelism().map_or(1, |p| p.get()),
    )
}

/// Saturate on `workers` threads and return the same state the serial
/// `init_state` + `seed_reflexive_edges` + [`run`] sequence produces, with the
/// labels in canonical iteration order. `None` means the worker threads could
/// not be started and the caller must run the serial engine.
fn run_context_parallel(
    nfs: &Nfs,
    idx: &Idx,
    n: usize,
    workers: usize,
    prof: &mut Prof,
) -> Option<State> {
    let shared = ParShared::new(workers);
    let mut shards: Vec<Shard<'_>> = (0..workers)
        .map(|id| Shard::new(id, workers, n, idx, &shared))
        .collect();
    let spawned = std::thread::scope(|scope| {
        let mut shards = shards.iter_mut();
        let first = shards.next().expect("at least one worker");
        let mut handles = Vec::with_capacity(workers - 1);
        let mut spawned = true;
        for shard in shards {
            let builder = std::thread::Builder::new().name(format!("elc-ctx-{}", shard.id));
            match builder.spawn_scoped(scope, move || {
                // Wait for the whole worker set: a shard that started while a
                // later spawn failed would otherwise wait for a worker that
                // never runs.
                while !shard.shared.started.load(Ordering::SeqCst) {
                    if shard.shared.abort.load(Ordering::SeqCst) {
                        return;
                    }
                    std::thread::yield_now();
                }
                shard.seed(nfs);
                shard.saturate();
                shard.canonicalize();
            }) {
                Ok(handle) => handles.push(handle),
                Err(error) => {
                    eprintln!("KM_ELC_PAR_CTX cannot start a worker ({error}); running serially");
                    shared.abort.store(true, Ordering::SeqCst);
                    spawned = false;
                    break;
                }
            }
        }
        if !spawned {
            return false;
        }
        shared.started.store(true, Ordering::SeqCst);
        first.seed(nfs);
        first.saturate();
        first.canonicalize();
        drop(handles);
        true
    });
    if !spawned {
        return None;
    }
    debug_assert_eq!(shared.credit.load(Ordering::SeqCst), 0);
    Some(collect_shards(shards, n, workers, prof))
}

/// Move the shards' tables into the shape the rest of the module expects. The
/// contexts of a shard are `id, id + W, ...`, so every entry lands at its own
/// index and the maps are merged over disjoint key sets.
fn collect_shards(shards: Vec<Shard<'_>>, n: usize, workers: usize, prof: &mut Prof) -> State {
    let mut sub_super: Vec<HashSet<u32>> = vec![HashSet::default(); n];
    let mut edges: Vec<HashSet<(u32, u32)>> = vec![HashSet::default(); n];
    let mut in_roles: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut in_by_role: HashMap<(u32, u32), Vec<u32>> = HashMap::default();
    let mut prop: HashMap<(u32, u32), Vec<u32>> = HashMap::default();
    let mut edge_epoch = 0u64;
    for (id, shard) in shards.into_iter().enumerate() {
        for (slot, label) in shard.sub_super.into_iter().enumerate() {
            sub_super[slot * workers + id] = label;
        }
        for (slot, out) in shard.edges.into_iter().enumerate() {
            edges[slot * workers + id] = out;
        }
        for (slot, roles) in shard.in_roles.into_iter().enumerate() {
            in_roles[slot * workers + id] = roles;
        }
        in_by_role.extend(shard.in_by_role);
        prop.extend(shard.prop);
        edge_epoch += shard.edges_total;
        prof.merge(&shard.prof);
    }
    prof.par_workers = workers as u64;
    State {
        sub_super,
        edges,
        in_by_role,
        in_roles,
        prop,
        // Empty: the fixpoint is reached. The discipline is the environment's,
        // so a later re-entry (an incremental replay over this state) behaves
        // exactly as after a serial saturation.
        worklist: Worklist::from_env(n),
        sub_journal: None,
        edge_epoch,
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
    /// (pinned variable, generating concept, source-argument variable).
    /// The pin is active only where its source existential is active.
    pin_guards: Vec<(usize, u32, usize)>,
}

#[derive(Clone, Debug)]
struct LazyComplement {
    cover_clause: usize,
    positive: u32,
    negative: u32,
    consumers: HashMap<u32, Vec<u32>>,
    local_consumers: Vec<(u32, u32)>,
}

/// Recognize the narrow complement fragment whose negative extension can stay
/// implicit in a rooted model. The negative definer may occur only in its
/// universal cover, its exact disjointness clause, explicit producer rules,
/// an existential filler, and NF2/NF4 body consumers that the rooted closure
/// handles below. Every other occurrence rejects the optimization.
fn regular_lazy_complements(
    rcs: &[RClause],
    nfs: &Nfs,
    known_bottom: &HashSet<u32>,
    it: &Interner,
) -> Vec<LazyComplement> {
    let mut out = Vec::new();
    for (cover_clause, rc) in rcs.iter().enumerate() {
        if !(rc.body.is_empty()
            || rc
                .body
                .iter()
                .all(|atom| matches!(atom, RAtom::C { cid, .. } if *cid == TOP)))
            || rc.head.len() != 2
        {
            continue;
        }
        let (RAtom::C { cid: left, v: lv }, RAtom::C { cid: right, v: rv }) =
            (rc.head[0], rc.head[1])
        else {
            continue;
        };
        if lv != rv {
            continue;
        }
        let left_internal = crate::calc::is_internal_concept(it.name(left));
        let right_internal = crate::calc::is_internal_concept(it.name(right));
        let (positive, negative) = match (left_internal, right_internal) {
            (false, true) => (left, right),
            (true, false) => (right, left),
            _ => continue,
        };
        let exact_residual_disjoint = |other: &RClause| {
            if !other.head.is_empty() || other.body.len() != 2 || !other.pins.is_empty() {
                return false;
            }
            let (RAtom::C { cid: a, v: av }, RAtom::C { cid: b, v: bv }) =
                (other.body[0], other.body[1])
            else {
                return false;
            };
            av == bv && ((a == positive && b == negative) || (a == negative && b == positive))
        };
        let residual_disjoint_count = rcs
            .iter()
            .enumerate()
            .filter(|(rci, other)| *rci != cover_clause && exact_residual_disjoint(other))
            .count();
        let residual_body_occurs_elsewhere = rcs.iter().enumerate().any(|(rci, other)| {
            rci != cover_clause
                && !exact_residual_disjoint(other)
                && other
                    .body
                    .iter()
                    .any(|atom| matches!(atom, RAtom::C { cid, .. } if *cid == negative))
        });
        // Producers of the negative concept remain explicit EL rules. Only
        // body occurrences consume its implicit extension and need support.
        let bad_nf1 = nfs.nf1.iter().any(|nf| nf.sub == negative);
        let bad_nf2 = nfs
            .nf2
            .iter()
            .any(|nf| nf.sub1 == negative && nf.sub2 == negative);
        let bad_nf3 = nfs.nf3.iter().any(|nf| nf.sub == negative);
        let bad_nf5 = nfs.nf5.contains(&negative);
        if residual_body_occurs_elsewhere || bad_nf1 || bad_nf2 || bad_nf3 || bad_nf5 {
            continue;
        }
        let has_disjointness = nfs.nf2.iter().any(|nf| {
            ((nf.sub1 == positive && nf.sub2 == negative)
                || (nf.sub1 == negative && nf.sub2 == positive))
                && known_bottom.contains(&nf.sup)
        });
        let mut consumers: HashMap<u32, Vec<u32>> = HashMap::default();
        for nf in &nfs.nf4 {
            if nf.filler == negative {
                consumers.entry(nf.role).or_default().push(nf.sup);
            }
        }
        let local_consumers: Vec<(u32, u32)> = nfs
            .nf2
            .iter()
            .filter_map(|nf| {
                let exact_disjoint = known_bottom.contains(&nf.sup)
                    && ((nf.sub1 == positive && nf.sub2 == negative)
                        || (nf.sub1 == negative && nf.sub2 == positive));
                if exact_disjoint {
                    None
                } else if nf.sub1 == negative {
                    Some((nf.sub2, nf.sup))
                } else if nf.sub2 == negative {
                    Some((nf.sub1, nf.sup))
                } else {
                    None
                }
            })
            .collect();
        if residual_disjoint_count <= 1 && (has_disjointness || residual_disjoint_count == 1) {
            out.push(LazyComplement {
                cover_clause,
                positive,
                negative,
                consumers,
                local_consumers,
            });
        }
    }
    out
}

/// Fire exactly the observable part of a recognized implicit complement. In
/// the rooted interpretation `negative` denotes the complement of `positive`;
/// outside explicit producers the supported observations of the negative
/// extension are local NF2 and role-target NF4 tests. Those conclusions are
/// queued directly when the relevant carrier node lacks `positive`. The
/// implicit negative label is deliberately not stored on shared targets.
///
/// Returns the number of newly queued labels. The caller closes them under all
/// EL rules and repeats until this operation adds nothing. Representatives are
/// used after repair merges, and dead targets are outside the model domain.
fn fire_lazy_complement_consumers(
    lazy: &[LazyComplement],
    domain: &HashSet<u32>,
    st: &mut State,
    repr: &mut [u32],
    nfs: &Nfs,
    known_bottom: &HashSet<u32>,
    banned: &HashSet<(u32, usize, u32)>,
    prov: &mut HashMap<(u32, u32), usize>,
    chrono: &mut Vec<(u32, usize, u32)>,
    choose_clash_avoiding_positive: bool,
    it: &Interner,
) -> usize {
    let mut by_role: HashMap<u32, Vec<(u32, u32, usize)>> = HashMap::default();
    for complement in lazy {
        for (&role, supers) in &complement.consumers {
            for &sup in supers {
                by_role
                    .entry(role)
                    .or_default()
                    .push((complement.positive, sup, complement.cover_clause));
            }
        }
    }
    // Do not store the implicit Q label on a shared canonical target: ordinary
    // NF4 propagation would then wake every full-model predecessor of that
    // target, including parents outside this rooted interpretation. Fire the
    // equivalent NF4 conclusion only at source edges in the rooted carrier.
    let mut additions: Vec<(u32, u32)> = Vec::new();
    let mut positive_choices: Vec<(u32, usize, u32)> = Vec::new();
    for &raw_source in domain {
        let source = uf_find(repr, raw_source);
        if st.sub_super[source as usize].contains(&BOTTOM) {
            continue;
        }
        for &(role, raw_target) in &st.edges[source as usize] {
            let Some(consumers) = by_role.get(&role) else {
                continue;
            };
            let target = uf_find(repr, raw_target);
            if st.sub_super[target as usize].contains(&BOTTOM) {
                continue;
            }
            for &(positive, sup, cover_clause) in consumers {
                if !st.sub_super[target as usize].contains(&positive)
                    && !st.sub_super[source as usize].contains(&sup)
                {
                    // `negative` is represented by absence of `positive` in
                    // this rooted model. Materialising a negative consumer is
                    // non-monotone: a later closure step may add `positive`.
                    // If the negative conclusion would immediately complete
                    // a conjunction already known to be bottom, choose the
                    // positive side of the exact cover instead. This is an
                    // ordinary model choice with provenance and can be
                    // backtracked; it is not treated as a logical consequence.
                    let negative_clashes = known_bottom.contains(&sup)
                        || nfs.nf2.iter().any(|nf| {
                            known_bottom.contains(&nf.sup)
                                && (nf.sub1 == sup || nf.sub2 == sup)
                        });
                    let positive_choice = (target, cover_clause, positive);
                    if std::env::var_os("KM_ELC_DEBUG_DERIVATION").is_some()
                        && it.name(sup) == "Q_36024"
                    {
                        eprintln!(
                            "KM_ELC_CERT lazy Q_36024 decision: source={} target={} \
                             positive={} structural_clash={} choose={} banned={}",
                            it.debug_name(source),
                            it.debug_name(target),
                            it.name(positive),
                            negative_clashes,
                            choose_clash_avoiding_positive,
                            banned.contains(&positive_choice),
                        );
                    }
                    if negative_clashes {
                        if choose_clash_avoiding_positive
                            && !banned.contains(&positive_choice)
                        {
                            positive_choices.push(positive_choice);
                        }
                    } else {
                        additions.push((source, sup));
                    }
                }
            }
        }
    }
    // Local conjunction consumer: G(x) & negative(x) -> S(x). Under the
    // implicit interpretation this fires exactly when G is explicit and the
    // same carrier node lacks `positive`.
    for &raw_node in domain {
        let node = uf_find(repr, raw_node);
        if st.sub_super[node as usize].contains(&BOTTOM) {
            continue;
        }
        for complement in lazy {
            if st.sub_super[node as usize].contains(&complement.positive) {
                continue;
            }
            for &(guard, sup) in &complement.local_consumers {
                if st.sub_super[node as usize].contains(&guard)
                    && !st.sub_super[node as usize].contains(&sup)
                {
                    let negative_clashes = known_bottom.contains(&sup)
                        || nfs.nf2.iter().any(|nf| {
                            known_bottom.contains(&nf.sup)
                                && (nf.sub1 == sup || nf.sub2 == sup)
                        });
                    let positive_choice =
                        (node, complement.cover_clause, complement.positive);
                    if negative_clashes {
                        if choose_clash_avoiding_positive
                            && !banned.contains(&positive_choice)
                        {
                            positive_choices.push(positive_choice);
                        }
                    } else {
                        additions.push((node, sup));
                    }
                }
            }
        }
    }
    additions.sort_unstable();
    additions.dedup();
    positive_choices.sort_unstable();
    positive_choices.dedup();
    let mut before = additions.len();
    for (target, cover_clause, positive) in positive_choices {
        if !st.sub_super[target as usize].contains(&positive) {
            st.add_sub(target, positive);
            prov.entry((target, positive)).or_insert(cover_clause);
            chrono.push((target, cover_clause, positive));
            before += 1;
        }
    }
    for (source, sup) in additions {
        st.add_sub(source, sup);
    }
    before
}

/// Recognize `R(x,z) ∧ R(y,z) → x=y`. Such a residual makes canonical
/// EL sharing of one existential filler across distinct sources observable.
fn inverse_functional_role(rc: &RClause) -> Option<u32> {
    if rc.body.len() != 2 || rc.head.len() != 1 || !rc.pins.is_empty() {
        return None;
    }
    let RAtom::Eq { s: es, t: et } = rc.head[0] else {
        return None;
    };
    let (
        RAtom::R {
            rid: r1,
            s: s1,
            t: t1,
        },
        RAtom::R {
            rid: r2,
            s: s2,
            t: t2,
        },
    ) = (rc.body[0], rc.body[1])
    else {
        return None;
    };
    (r1 == r2 && t1 == t2 && ((s1 == es && s2 == et) || (s1 == et && s2 == es))).then_some(r1)
}

struct CompiledResidual {
    clauses: Vec<RClause>,
    /// One dedicated canonical concept for every Skolem function whose value
    /// occurs in a compiled residual clause.
    skolem_witnesses: HashMap<u32, u32>,
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
) -> Option<CompiledResidual> {
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
        let mut pin_guards: Vec<(usize, u32, usize)> = Vec::new();
        let mut body = Vec::with_capacity(c.body.len());
        let mut head = Vec::with_capacity(c.head.len());
        // a term: plain variable, or a skolem `f(x)` pinned to its filler node
        macro_rules! term_v {
            ($t:expr) => {
                match $t {
                    JTerm::Var { name } => vid(&mut vars, ResidualVarKey::Source(name)),
                    JTerm::Fun { function, arg } => {
                        let JTerm::Var { name: arg_name } = arg.as_ref() else {
                            bail!(c, "nested fun term");
                        };
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
                        let arg_v = vid(&mut vars, ResidualVarKey::Source(arg_name));
                        if !pin_guards.iter().any(|&(pv, _, _)| pv == v) {
                            pin_guards.push((v, sub, arg_v));
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
        // Every Skolem occurrence we conditionally pin must retain the exact
        // generating concept on its source argument in this clause's body.
        // Decline otherwise: treating an unguarded function occurrence as
        // vacuous when its original existential source is bottom is unsound.
        if pin_guards.iter().any(|&(_, guard, arg_v)| {
            !body
                .iter()
                .any(|a| matches!(*a, RAtom::C { cid, v } if cid == guard && v == arg_v))
        }) {
            bail!(
                c,
                "fun term without its generating source guard in the body"
            );
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
            pin_guards,
        });
    }
    Some(CompiledResidual {
        clauses: out,
        skolem_witnesses: skolem_witness,
    })
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
                    ROrigin::Source {
                        source,
                        name: source_name,
                    } if source == name => Some(*source_name),
                    _ => None,
                });
                // A variable occurring only as the ignored argument of a
                // constant Skolem interpretation need not own a compiled slot.
                let name = source_name
                    .or_else(|| (clause.nvars > 0).then_some(0))
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
            JAtom::Role {
                role,
                source,
                target,
            } => Ok(LeanResidualAtom::Role {
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

/// Recover the exact source partition consumed by the Lean wire-v5 checker.
/// Residual clauses are matched as a multiset first. Every Skolem function
/// rewritten by `compile_residual` then claims its original NF3 role/filler
/// pair. All remaining clauses stay in the direct EL normalization input.
fn build_lean_source_partition(
    source: &[JClause],
    residual: &[JClause],
    skolem_target: &HashMap<u32, (u32, u32, u32)>,
    skolem_witnesses: &HashMap<u32, u32>,
    interner: &Interner,
) -> Result<(Vec<JClause>, Vec<LeanCanonicalWitnessRecord>), String> {
    let mut claimed = vec![false; source.len()];
    for clause in residual {
        let Some(index) = source
            .iter()
            .enumerate()
            .position(|(index, candidate)| !claimed[index] && candidate == clause)
        else {
            return Err("residual clause is absent from retained source stream".into());
        };
        claimed[index] = true;
    }

    fn source_var(term: &JTerm) -> Option<&str> {
        match term {
            JTerm::Var { name } => Some(name),
            _ => None,
        }
    }
    fn matching_fun(term: &JTerm, function: &str, variable: &str) -> bool {
        matches!(term,
            JTerm::Fun { function: candidate, arg }
                if candidate == function && source_var(arg) == Some(variable))
    }
    fn is_role_half(clause: &JClause, sub: &str, role: &str, function: &str) -> bool {
        let [JAtom::Concept { concept, term }] = clause.body.as_slice() else {
            return false;
        };
        let Some(variable) = source_var(term) else {
            return false;
        };
        let [JAtom::Role {
            role: candidate_role,
            source,
            target,
        }] = clause.head.as_slice()
        else {
            return false;
        };
        concept == sub
            && candidate_role == role
            && source_var(source) == Some(variable)
            && matching_fun(target, function, variable)
    }
    fn is_filler_half(clause: &JClause, sub: &str, filler: &str, function: &str) -> bool {
        let [JAtom::Concept { concept, term }] = clause.body.as_slice() else {
            return false;
        };
        let Some(variable) = source_var(term) else {
            return false;
        };
        let [JAtom::Concept {
            concept: candidate_filler,
            term: target,
        }] = clause.head.as_slice()
        else {
            return false;
        };
        concept == sub && candidate_filler == filler && matching_fun(target, function, variable)
    }

    let mut witnesses: Vec<_> = skolem_witnesses.iter().collect();
    witnesses.sort_unstable_by_key(|&(function, _)| *function);
    let mut records = Vec::with_capacity(witnesses.len());
    for (&function, &witness) in witnesses {
        let &(sub, role, filler) = skolem_target
            .get(&function)
            .ok_or_else(|| format!("rewritten Skolem function {function} has no NF3 target"))?;
        let function_name = interner.name(function);
        let sub_name = interner.name(sub);
        let role_name = interner.name(role);
        let filler_name = interner.name(filler);
        let mut found_role = false;
        let mut found_filler = false;
        for (index, clause) in source.iter().enumerate() {
            if claimed[index] {
                continue;
            }
            if is_role_half(clause, sub_name, role_name, function_name) {
                claimed[index] = true;
                found_role = true;
            } else if is_filler_half(clause, sub_name, filler_name, function_name) {
                claimed[index] = true;
                found_filler = true;
            }
        }
        if !found_role || !found_filler {
            return Err(format!(
                "rewritten Skolem function {function_name} is missing its exact source pair"
            ));
        }
        records.push(LeanCanonicalWitnessRecord {
            sub,
            role,
            filler,
            witness,
            function,
            // Variables are scoped by their clause. Canonical zero-based
            // renaming keeps the emitted source pair alpha-equivalent to the
            // retained JSON clauses and minimizes the wire domain.
            role_variable: 0,
            filler_variable: 0,
        });
    }

    let direct = source
        .iter()
        .enumerate()
        .filter(|(index, _)| !claimed[*index])
        .map(|(_, clause)| clause.clone())
        .collect();
    Ok((direct, records))
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
    /// Source guards that make the corresponding pinned pair semantically
    /// relevant. Empty means unconditionally active.
    pinned_guards: Vec<Vec<u32>>,
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
        let mut pinned_guards: Vec<Vec<u32>> = Vec::new();
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
                pinned_guards.push(rc.pin_guards.iter().map(|&(_, guard, _)| guard).collect());
            }
        }
        CardGuide {
            pinned_apart,
            pinned_guards,
            bounds,
            by_guard,
        }
    }

    /// Nothing recognised: every query below is inert, so the search runs
    /// exactly as it did before this guidance existed.
    fn is_inert(&self) -> bool {
        self.pinned_apart.is_empty() && self.by_guard.is_empty()
    }

    /// Materialize a legal at-most partition side when the current quotient
    /// already has no more qualifying successors than its bound. These are
    /// model choices, not logical consequences. Record their cover-clause
    /// provenance and chronology so conflict search can revisit them.
    /// If later closure creates more
    /// successors, the ordinary residual at-most clause must merge them or
    /// the final certificate fails.
    fn choose_low_sides(
        &self,
        domain: &HashSet<u32>,
        st: &mut State,
        repr: &mut [u32],
        it: &Interner,
        complement_covers: &HashMap<u32, (u32, usize)>,
        prefer_positive_guards: &HashSet<u32>,
        globally_avoided_sides: &HashSet<(usize, u32)>,
        banned: &HashSet<(u32, usize, u32)>,
        eager_seeded: bool,
        pass_label: usize,
        prov: &mut HashMap<(u32, u32), usize>,
        chrono: &mut Vec<(u32, usize, u32)>,
    ) -> usize {
        let mut additions = Vec::new();
        for (&guard, bounds) in &self.by_guard {
            if !crate::calc::is_internal_concept(it.name(guard)) {
                continue;
            }
            let Some(&(positive, cover_clause)) = complement_covers.get(&guard) else {
                // Without an exact binary complement cover there is no sound
                // alternative to attribute and revisit. Leave this guard to
                // the ordinary residual search.
                continue;
            };
            for &candidate in domain {
                let node = uf_find(repr, candidate);
                if st.sub_super[node as usize].contains(&BOTTOM)
                    || st.sub_super[node as usize].contains(&guard)
                    || st.sub_super[node as usize].contains(&positive)
                {
                    continue;
                }
                let legal = bounds.iter().all(|&bi| {
                    let bound = &self.bounds[bi];
                    bound
                        .guards
                        .iter()
                        .all(|&g| g == guard || st.sub_super[node as usize].contains(&g))
                        && qualifying_successor_count(st, repr, node, bound) <= bound.bound
                });
                if legal {
                    let low = (node, cover_clause, guard);
                    let high = (node, cover_clause, positive);
                    let exhausted = banned.contains(&(node, cover_clause, u32::MAX));
                    let available = |choice: &(u32, usize, u32)| {
                        !banned.contains(choice)
                            && !globally_avoided_sides.contains(&(choice.1, choice.2))
                    };
                    let locally_available = |choice: &(u32, usize, u32)| {
                        !banned.contains(choice)
                    };
                    let choice = if exhausted {
                        // Checkpoint compaction replaces a fully tried local
                        // binary cover with a sentinel. Reconstruct a stable
                        // node-mixed assignment here; otherwise the cardinality
                        // preselector ignores the sentinel and recreates one
                        // uniform polarity on every restart.
                        let alternatives = [low, high];
                        Some(alternatives[repair_choice_mix(node, cover_clause, pass_label) % 2])
                    } else if prefer_positive_guards.contains(&guard) {
                        // A regular lazy-complement guard is the negative side
                        // of an exact cover.  Choosing it here can seed the
                        // very cyclic negative existential that the lazy
                        // consumer deliberately left implicit.  Try the
                        // positive side first; if conflict learning later bans
                        // it, retain the negative side as the complete-search
                        // fallback rather than excluding a model.
                        [high, low]
                            .into_iter()
                            .find(available)
                            .or_else(|| [high, low].into_iter().find(locally_available))
                    } else if eager_seeded {
                        let alternatives = [low, high];
                        let start = repair_choice_mix(node, cover_clause, pass_label) % 2;
                        (0..2)
                            .map(|offset| alternatives[(start + offset) % 2])
                            .find(available)
                            .or_else(|| {
                                (0..2)
                                    .map(|offset| alternatives[(start + offset) % 2])
                                    .find(locally_available)
                            })
                    } else if available(&low) {
                        Some(low)
                    } else if available(&high) {
                        Some(high)
                    } else if !banned.contains(&low) {
                        Some(low)
                    } else if !banned.contains(&high) {
                        Some(high)
                    } else {
                        // Both sides have already failed in learned contexts.
                        // The ordinary residual chooser retains its established
                        // tier-3 fallback and causal backjump path.
                        None
                    };
                    if let Some(choice) = choice {
                        additions.push(choice);
                    }
                }
            }
        }
        let before = additions.len();
        for (node, cover_clause, choice) in additions {
            st.add_sub(node, choice);
            prov.entry((node, choice)).or_insert(cover_clause);
            chrono.push((node, cover_clause, choice));
        }
        before
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

fn qualifying_successor_count(
    st: &State,
    repr: &mut [u32],
    node: u32,
    bound: &AtMostBound,
) -> usize {
    let mut successors = HashSet::default();
    for &(role, target) in &st.edges[node as usize] {
        if role != bound.role {
            continue;
        }
        let target = uf_find(repr, target);
        if bound
            .fillers
            .iter()
            .all(|filler| st.sub_super[target as usize].contains(filler))
        {
            successors.insert(target);
        }
    }
    successors.len()
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

    /// Rooted-model variant of [`Self::resync`]. A Skolem disequality guarded
    /// by an empty source class is vacuous in this carrier, so it must not
    /// prevent an equality required by inverse functionality or an at-most
    /// restriction. The complete residual check remains authoritative.
    fn resync_active(
        &mut self,
        guide: &CardGuide,
        repr: &mut [u32],
        st: &State,
        domain: &HashSet<u32>,
    ) {
        self.apart.clear();
        self.memo.clear();
        for (i, &(x, y)) in guide.pinned_apart.iter().enumerate() {
            let active = guide.pinned_guards[i].iter().all(|&guard| {
                domain.iter().any(|&candidate| {
                    let node = uf_find(repr, candidate);
                    !st.sub_super[node as usize].contains(&BOTTOM)
                        && st.sub_super[node as usize].contains(&guard)
                })
            });
            if !active {
                continue;
            }
            let (a, b) = (uf_find(repr, x), uf_find(repr, y));
            if a != b {
                self.apart.insert((a.min(b), a.max(b)));
            }
        }
    }
}

/// Default cap on violations recorded per repair round. The uncollected
/// remainder is caught by the recheck after this round's repairs.
const REPAIR_VIOL_CAP: usize = 100_000;

/// Repair-frontier cap for one residual check. Larger values amortize an EL
/// re-closure over more independent choices on very large covering theories;
/// smaller values bound the temporary binding vector more tightly. This is a
/// schedule/resource choice only: every recorded instance receives the same
/// repair, and acceptance still requires a complete residual recheck after EL
/// closure. Keep the established cap by default and bound explicit overrides
/// so a malformed environment cannot request an unbounded allocation.
fn repair_viol_cap_from(value: Option<&str>) -> usize {
    value
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(REPAIR_VIOL_CAP)
        .clamp(1, 5_000_000)
}

fn repair_viol_cap() -> usize {
    let value = std::env::var("KM_ELC_REPAIR_VIOL_CAP").ok();
    repair_viol_cap_from(value.as_deref())
}

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
#[derive(Clone, Default)]
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
fn residual_clause_active_in(
    rc: &RClause,
    alive: &[bool],
    members: Option<&HashMap<u32, Vec<u32>>>,
) -> bool {
    rc.pin_guards.iter().all(|&(_, guard, _)| match members {
        Some(members) => members.get(&guard).is_some_and(|nodes| !nodes.is_empty()),
        None => alive.get(guard as usize).copied().unwrap_or(false),
    })
}

#[cfg(test)]
fn residual_clause_active(rc: &RClause, alive: &[bool]) -> bool {
    residual_clause_active_in(rc, alive, None)
}

fn residual_pins_are_alive_in(
    rcs: &[RClause],
    alive: &[bool],
    members: Option<&HashMap<u32, Vec<u32>>>,
) -> bool {
    rcs.iter().all(|rc| {
        !residual_clause_active_in(rc, alive, members)
            || rc
                .pins
                .iter()
                .all(|&(_, node)| alive.get(node as usize).copied().unwrap_or(false))
    })
}

/// Extend a rooted certificate carrier until it is closed under outgoing
/// model edges and under witnesses of residual clauses whose exact source
/// guards are inhabited in that carrier. Returns the number of admitted raw
/// node ids. This is used only by the publication-disabled rooted diagnostic.
fn expand_rooted_domain(
    domain: &mut HashSet<u32>,
    st: &State,
    rcs: &[RClause],
    repr: &mut [u32],
) -> usize {
    let before = domain.len();
    loop {
        let mut additions: Vec<u32> = Vec::new();
        for &candidate in domain.iter() {
            let node = uf_find(repr, candidate);
            if st.sub_super[node as usize].contains(&BOTTOM) {
                continue;
            }
            additions.extend(st.edges[node as usize].iter().map(|&(_, target)| target));
        }
        for rc in rcs {
            let active = rc.pin_guards.iter().all(|&(_, guard, _)| {
                domain.iter().any(|&candidate| {
                    let node = uf_find(repr, candidate);
                    !st.sub_super[node as usize].contains(&BOTTOM)
                        && st.sub_super[node as usize].contains(&guard)
                })
            });
            if active {
                additions.extend(rc.pins.iter().map(|&(_, node)| node));
            }
        }
        let old_len = domain.len();
        domain.extend(additions.into_iter().filter(|&node| node != BOTTOM));
        if domain.len() == old_len {
            break;
        }
    }
    domain.len() - before
}

/// Redirect inverse-functional existential edges that came from the canonical
/// base model before fresh-witness mode was enabled. Returns the number of
/// redirected edges. New NF3 firings already allocate fresh targets in
/// [`run_with_fresh_inverse`].
fn freshen_rooted_inverse_edges(
    domain: &HashSet<u32>,
    st: &mut State,
    fresh: &mut FreshInverseWitnesses,
    role_supers: &[HashSet<u32>],
) -> usize {
    let mut rewrite: Vec<(u32, u32, u32)> = Vec::new();
    for &source in domain {
        // `target` intentionally reuses canonical fillers for a bottom source.
        // Rewriting those edges would remove and reinsert exactly the same
        // targets, reporting progress forever to the carrier-expansion loop.
        if st.sub_super[source as usize].contains(&BOTTOM) {
            continue;
        }
        rewrite.extend(
            st.edges[source as usize]
                .iter()
                .copied()
                .filter(|&(role, target)| {
                    fresh.selected(source, role, target)
                        && fresh.existential_pairs.contains(&(role, target))
                })
                .map(|(role, target)| (source, role, target)),
        );
    }
    for &(source, role, filler) in &rewrite {
        if st.remove_edge(source, role, filler) {
            // The cloned base fixpoint already contains every role-super edge
            // derived from this existential. Remove those stale consequences
            // with the generating edge; ordinary edge closure below recreates
            // them at the fresh target. An independently generated edge is
            // reintroduced by its own NF3 firing.
            for &super_role in role_supers.get(role as usize).into_iter().flatten() {
                if super_role != role {
                    st.remove_edge(source, super_role, filler);
                }
            }
            let target = fresh.target(st, source, role, filler);
            st.add_edge(source, role, target);
        }
    }
    rewrite.len()
}

#[cfg(test)]
fn residual_pins_are_alive(rcs: &[RClause], alive: &[bool]) -> bool {
    residual_pins_are_alive_in(rcs, alive, None)
}

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
    // Universal covers discharged by an implicit-complement interpretation.
    // Only rooted repair supplies this set, after the narrow occurrence audit
    // in `regular_lazy_complements` and observable-target materialization.
    implicit_covers: Option<&HashSet<usize>>,
    // Negative concept -> paired positive concept for implicit head truth.
    implicit_positive: Option<&HashMap<u32, u32>>,
) -> bool {
    let repair_viol_cap = repair_viol_cap();
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

    // Pins denote elements of the canonical model, whose domain contains only
    // alive concept nodes. A dead witness cannot interpret a source Skolem
    // function. Decline instead of evaluating over a bottom-containing
    // pseudo-domain that is larger than the certified model.
    if !residual_pins_are_alive_in(rcs, alive, Some(members)) {
        if debug {
            eprintln!("KM_ELC_CERT fail: pinned witness is outside the alive canonical domain");
        }
        return false;
    }

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
        implicit_positive: Option<&HashMap<u32, u32>>,
        edges: &[HashSet<(u32, u32)>],
        repr: Option<&[u32]>,
        members: &HashMap<u32, Vec<u32>>,
        edges_by_role: &HashMap<u32, Vec<(u32, u32)>>,
        empty_m: &Vec<u32>,
        empty_e: &Vec<(u32, u32)>,
        budget: &mut u64,
        collect: &mut Option<&mut Vec<(usize, Vec<u32>)>>,
        collect_limit: usize,
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
                        implicit_positive,
                        edges,
                        repr,
                        members,
                        edges_by_role,
                        empty_m,
                        empty_e,
                        budget,
                        collect,
                        collect_limit,
                    ) {
                        asg[free] = None;
                        return false;
                    }
                }
                asg[free] = None;
                return true;
            }
            let ok = rc.head.iter().any(|a| match *a {
                RAtom::C { cid, v } => {
                    let labels = &sub_super[asg[v].unwrap() as usize];
                    labels.contains(&cid)
                        || implicit_positive
                            .and_then(|pairs| pairs.get(&cid))
                            .is_some_and(|positive| !labels.contains(positive))
                }
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
                return out.len() < collect_limit;
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
                        implicit_positive,
                        edges,
                        repr,
                        members,
                        edges_by_role,
                        empty_m,
                        empty_e,
                        budget,
                        collect,
                        collect_limit,
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
                            implicit_positive,
                            edges,
                            repr,
                            members,
                            edges_by_role,
                            empty_m,
                            empty_e,
                            budget,
                            collect,
                            collect_limit,
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
                        implicit_positive,
                        edges,
                        repr,
                        members,
                        edges_by_role,
                        empty_m,
                        empty_e,
                        budget,
                        collect,
                        collect_limit,
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
                            implicit_positive,
                            edges,
                            repr,
                            members,
                            edges_by_role,
                            empty_m,
                            empty_e,
                            budget,
                            collect,
                            collect_limit,
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
                            implicit_positive,
                            edges,
                            repr,
                            members,
                            edges_by_role,
                            empty_m,
                            empty_e,
                            budget,
                            collect,
                            collect_limit,
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
                        implicit_positive,
                        edges,
                        repr,
                        members,
                        edges_by_role,
                        empty_m,
                        empty_e,
                        budget,
                        collect,
                        collect_limit,
                    )
                }
                // unbound side: cannot evaluate — fail conservatively
                _ => false,
            },
        }
    }

    let mut clause_order: Vec<usize> = (0..rcs.len()).collect();
    if collect.is_some() && std::env::var_os("KM_ELC_REPAIR_GUARDED_FIRST").is_some() {
        clause_order.sort_by_key(|&i| {
            let rc = &rcs[i];
            let head_width = rc
                .head
                .iter()
                .filter(|atom| !matches!(atom, RAtom::Eq { .. }))
                .count();
            let universal_cover = head_width > 1
                && (rc.body.is_empty()
                    || rc
                        .body
                        .iter()
                        .all(|atom| matches!(atom, RAtom::C { cid, .. } if *cid == TOP)));
            let concept_guarded = !universal_cover
                && !rc.body.is_empty()
                && rc.body.iter().all(|atom| matches!(atom, RAtom::C { .. }));
            if concept_guarded {
                0u8
            } else if universal_cover {
                1
            } else {
                2
            }
        });
    }
    for i in clause_order {
        if implicit_covers.is_some_and(|covers| covers.contains(&i)) {
            continue;
        }
        let rc = &rcs[i];
        // A Skolemized consequence A(x) -> ...f(x)... has no instances when
        // A is empty. Its dedicated completion witness may then be bottom,
        // but the source clause is vacuous and imposes no pin requirement.
        if !residual_clause_active_in(rc, alive, Some(members)) {
            continue;
        }
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
        // A global collection cap used to let the first universal covering
        // clause consume the entire round on a large canonical domain. Later
        // guarded clauses then never contributed consequences until many stale
        // complement choices had already been made. Give every residual clause
        // a bounded slice of a repair round. Repeated rounds still enumerate all
        // remaining instances, while no clause can starve the rest.
        let fair_collect = std::env::var_os("KM_ELC_REPAIR_FAIR").is_some();
        let per_clause = if fair_collect {
            (repair_viol_cap / rcs.len().max(1)).max(1)
        } else {
            repair_viol_cap
        };
        let before = collect.as_deref().map_or(0, |out| out.len());
        let collect_limit = (before + per_clause).min(repair_viol_cap);
        let ok = join(
            rc,
            i,
            &order,
            0,
            &mut asg,
            nodes,
            alive,
            sub_super,
            implicit_positive,
            edges,
            repr,
            members,
            edges_by_role,
            &empty_m,
            &empty_e,
            budget,
            &mut collect,
            collect_limit,
        );
        if !ok {
            let slice_full = collect
                .as_deref()
                .is_some_and(|out| out.len() >= collect_limit);
            if *budget > 0 && slice_full && collect_limit < repair_viol_cap {
                continue;
            }
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
        None,
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
/// the most recent unbanned choice anywhere (chronological backtracking). When
/// a resumed soft-ban checkpoint has exhausted an instance, the tier-3 chooser
/// may reuse a banned side; return that actual choice as a final fallback so
/// the conflict application can reopen its siblings.
///
/// `None` means no choice was made at all, so the contradiction is entailed by
/// the base model and the certificate must fail rather than restart.
#[inline]
fn repair_choice_untried(
    banned: &HashSet<(u32, usize, u32)>,
    choice: (u32, usize, u32),
) -> bool {
    !banned.contains(&choice) && !banned.contains(&(choice.0, choice.1, u32::MAX))
}

#[inline]
fn repair_exhausted_choice_instances(
    banned: &HashSet<(u32, usize, u32)>,
    choices: &[(u32, usize, u32)],
    rcs: &[RClause],
) -> HashSet<(u32, usize)> {
    let instances: HashSet<(u32, usize)> = choices
        .iter()
        .map(|&(node, clause, _)| (node, clause))
        .collect();
    instances
        .into_iter()
        .filter(|&(node, clause)| {
            banned.contains(&(node, clause, u32::MAX))
                || rcs.get(clause).is_some_and(|rc| {
                    !rc.head.is_empty()
                        && rc.head.iter().all(|atom| match *atom {
                            RAtom::C { cid, .. } => {
                                banned.contains(&(node, clause, cid))
                                    || choices.iter().any(|&choice| {
                                        (choice.0, choice.1, choice.2) == (node, clause, cid)
                                    })
                            }
                            _ => false,
                        })
                })
        })
        .collect()
}

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
                if repair_choice_untried(banned, (nd, src, cid)) {
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
        .find(|&&t| conf_nodes.contains(&uf_find(repr, t.0)) && repair_choice_untried(banned, t))
        .copied()
        .or_else(|| {
            chrono
                .iter()
                .rev()
                .find(|&&t| repair_choice_untried(banned, t))
                .copied()
        })
        .or_else(|| chrono.last().copied())
}

/// Walk an EL-closure explanation backwards until it reaches a direct
/// residual-model choice. Repair provenance records only those direct choices,
/// while a protected root commonly reaches bottom several NF1/NF2/NF4 steps
/// later, or because one of its existential successors dies. This bounded
/// reconstruction is used only by the publication-disabled rooted diagnostic.
#[derive(Default)]
struct RepairTraceIdx {
    bottom_subs: Vec<u32>,
    nf1_by_sup: HashMap<u32, Vec<u32>>,
    nf2_by_sup: HashMap<u32, Vec<(u32, u32)>>,
    nf3_by_pair: HashMap<(u32, u32), Vec<u32>>,
    nf3_by_role: HashMap<u32, Vec<(u32, u32)>>,
    nf4_by_sup: HashMap<u32, Vec<(u32, u32)>>,
}

impl RepairTraceIdx {
    fn new(nfs: &Nfs) -> Self {
        let mut out = RepairTraceIdx {
            bottom_subs: nfs.nf5.clone(),
            nf1_by_sup: HashMap::default(),
            nf2_by_sup: HashMap::default(),
            nf3_by_pair: HashMap::default(),
            nf3_by_role: HashMap::default(),
            nf4_by_sup: HashMap::default(),
        };
        for nf in &nfs.nf1 {
            out.nf1_by_sup.entry(nf.sup).or_default().push(nf.sub);
        }
        for nf in &nfs.nf2 {
            out.nf2_by_sup
                .entry(nf.sup)
                .or_default()
                .push((nf.sub1, nf.sub2));
        }
        for nf in &nfs.nf3 {
            out.nf3_by_pair
                .entry((nf.role, nf.filler))
                .or_default()
                .push(nf.sub);
            out.nf3_by_role
                .entry(nf.role)
                .or_default()
                .push((nf.sub, nf.filler));
        }
        for nf in &nfs.nf4 {
            out.nf4_by_sup
                .entry(nf.sup)
                .or_default()
                .push((nf.role, nf.filler));
        }
        out
    }
}

fn trace_repair_choice(
    node: u32,
    concept: u32,
    st: &State,
    nfs: &Nfs,
    trace: &RepairTraceIdx,
    it: &Interner,
    repr: &mut [u32],
    prov: &HashMap<(u32, u32), usize>,
    banned: &HashSet<(u32, usize, u32)>,
    seen: &mut HashSet<(u32, u32)>,
    depth: usize,
) -> Option<(u32, usize, u32)> {
    // This is a search-order diagnostic, not part of model acceptance.  On a
    // large rooted carrier an already-tried explanation can fan out through
    // millions of equivalent EL derivations before reaching another direct
    // choice.  Bound that reconstruction work and let the caller fall back to
    // its chronological untried choice.  The selected branch remains a soft
    // ban, and every candidate still has to pass the complete residual-model
    // check, so this cap cannot weaken the certificate.
    const STATE_CAP: usize = 1_000;
    if depth == 0 {
        return None;
    }
    let node = uf_find(repr, node);
    if let Some(&rci) = prov.get(&(node, concept)) {
        let choice = (node, rci, concept);
        if repair_choice_untried(banned, choice) {
            return Some(choice);
        }
    }
    if seen.len() >= STATE_CAP || !seen.insert((node, concept)) {
        return None;
    }

    if concept == BOTTOM {
        for &(_, target0) in &st.edges[node as usize] {
            let target = uf_find(repr, target0);
            if st.sub_super[target as usize].contains(&BOTTOM) {
                if let Some(generator) = dedicated_witness_generator(target, node, st, it) {
                    if let Some(choice) = trace_repair_choice(
                        node, generator, st, nfs, trace, it, repr, prov, banned, seen, depth - 1,
                    ) {
                        return Some(choice);
                    }
                }
            }
        }
        for &sub in &trace.bottom_subs {
            if st.sub_super[node as usize].contains(&sub) {
                if let Some(choice) = trace_repair_choice(
                    node, sub, st, nfs, trace, it, repr, prov, banned, seen, depth - 1,
                ) {
                    return Some(choice);
                }
            }
        }
    }
    for &sub in trace.nf1_by_sup.get(&concept).into_iter().flatten() {
        if st.sub_super[node as usize].contains(&sub) {
            if let Some(choice) = trace_repair_choice(
                node, sub, st, nfs, trace, it, repr, prov, banned, seen, depth - 1,
            ) {
                return Some(choice);
            }
        }
    }
    for &(sub1, sub2) in trace.nf2_by_sup.get(&concept).into_iter().flatten() {
        if st.sub_super[node as usize].contains(&sub1)
            && st.sub_super[node as usize].contains(&sub2)
        {
            for sub in [sub1, sub2] {
                if let Some(choice) = trace_repair_choice(
                    node, sub, st, nfs, trace, it, repr, prov, banned, seen, depth - 1,
                ) {
                    return Some(choice);
                }
            }
        }
    }
    for &(nf_role, nf_filler) in trace.nf4_by_sup.get(&concept).into_iter().flatten() {
        for &(role, target0) in &st.edges[node as usize] {
            let target = uf_find(repr, target0);
            if role != nf_role || !st.sub_super[target as usize].contains(&nf_filler) {
                continue;
            }
            if let Some(generator) = dedicated_witness_generator(target, node, st, it) {
                if let Some(choice) = trace_repair_choice(
                    node, generator, st, nfs, trace, it, repr, prov, banned, seen, depth - 1,
                ) {
                    return Some(choice);
                }
            }
            for &producer_sub in trace
                .nf3_by_pair
                .get(&(role, nf_filler))
                .into_iter()
                .flatten()
            {
                if st.sub_super[node as usize].contains(&producer_sub) {
                    if let Some(choice) = trace_repair_choice(
                        node,
                        producer_sub,
                        st,
                        nfs,
                        trace,
                        it,
                        repr,
                        prov,
                        banned,
                        seen,
                        depth - 1,
                    ) {
                        return Some(choice);
                    }
                }
            }
            if let Some(choice) = trace_repair_choice(
                target,
                nf_filler,
                st,
                nfs,
                trace,
                it,
                repr,
                prov,
                banned,
                seen,
                depth - 1,
            ) {
                return Some(choice);
            }
        }
    }
    if concept == BOTTOM {
        for &(role, target0) in &st.edges[node as usize] {
            let target = uf_find(repr, target0);
            if !st.sub_super[target as usize].contains(&BOTTOM) {
                continue;
            }
            if let Some(generator) = dedicated_witness_generator(target, node, st, it) {
                if let Some(choice) = trace_repair_choice(
                    node, generator, st, nfs, trace, it, repr, prov, banned, seen, depth - 1,
                ) {
                    return Some(choice);
                }
            }
            for &(producer_sub, producer_filler) in trace
                .nf3_by_role
                .get(&role)
                .into_iter()
                .flatten()
            {
                if st.sub_super[target as usize].contains(&producer_filler)
                    && st.sub_super[node as usize].contains(&producer_sub)
                {
                    if let Some(choice) = trace_repair_choice(
                        node,
                        producer_sub,
                        st,
                        nfs,
                        trace,
                        it,
                        repr,
                        prov,
                        banned,
                        seen,
                        depth - 1,
                    ) {
                        return Some(choice);
                    }
                }
            }
            if let Some(choice) = trace_repair_choice(
                target,
                BOTTOM,
                st,
                nfs,
                trace,
                it,
                repr,
                prov,
                banned,
                seen,
                depth - 1,
            ) {
                return Some(choice);
            }
        }
    }
    None
}

/// Emit a bounded explanation tree for one closed EL membership. This is a
/// diagnostic only: it neither records provenance in the production state nor
/// affects rule firing. It reconstructs direct NF1/NF2/NF4/NF5 producers from
/// the final fixpoint so a real large-ontology clash can identify the rule
/// family that needs exact provenance.
fn debug_el_membership_producers(
    node: u32,
    concept: u32,
    st: &State,
    nfs: &Nfs,
    it: &Interner,
    prov: &HashMap<(u32, u32), usize>,
    seen: &mut HashSet<(u32, u32)>,
    depth: usize,
    lines: &mut usize,
) {
    const LINE_CAP: usize = 40;
    if depth == 0 || *lines >= LINE_CAP || !seen.insert((node, concept)) {
        return;
    }
    let indent = "  ".repeat(5usize.saturating_sub(depth));
    if let Some(&rci) = prov.get(&(node, concept)) {
        eprintln!(
            "KM_ELC_CERT target derivation: {indent}{}@{} direct residual choice clause={rci}",
            it.name(concept),
            it.debug_name(node),
        );
        *lines += 1;
    }
    if concept == BOTTOM {
        for &sub in nfs
            .nf5
            .iter()
            .filter(|&&sub| st.sub_super[node as usize].contains(&sub))
            .take(6)
        {
            eprintln!(
                "KM_ELC_CERT target derivation: {indent}{} -> bottom (NF5)",
                it.name(sub),
            );
            *lines += 1;
            debug_el_membership_producers(
                node, sub, st, nfs, it, prov, seen, depth - 1, lines,
            );
        }
    }
    for nf in nfs
        .nf1
        .iter()
        .filter(|nf| nf.sup == concept && st.sub_super[node as usize].contains(&nf.sub))
        .take(6)
    {
        eprintln!(
            "KM_ELC_CERT target derivation: {indent}{} -> {} (NF1)",
            it.name(nf.sub),
            it.name(concept),
        );
        *lines += 1;
        debug_el_membership_producers(
            node, nf.sub, st, nfs, it, prov, seen, depth - 1, lines,
        );
    }
    for nf in nfs
        .nf2
        .iter()
        .filter(|nf| {
            nf.sup == concept
                && st.sub_super[node as usize].contains(&nf.sub1)
                && st.sub_super[node as usize].contains(&nf.sub2)
        })
        .take(6)
    {
        eprintln!(
            "KM_ELC_CERT target derivation: {indent}{} & {} -> {} (NF2)",
            it.name(nf.sub1),
            it.name(nf.sub2),
            it.name(concept),
        );
        *lines += 1;
        for sub in [nf.sub1, nf.sub2] {
            debug_el_membership_producers(
                node, sub, st, nfs, it, prov, seen, depth - 1, lines,
            );
        }
    }
    for nf in nfs.nf4.iter().filter(|nf| nf.sup == concept).take(4) {
        let mut matching_edges = 0usize;
        for &(role, target) in &st.edges[node as usize] {
            if role != nf.role || !st.sub_super[target as usize].contains(&nf.filler) {
                continue;
            }
            if matching_edges >= 2 {
                break;
            }
            matching_edges += 1;
            eprintln!(
                "KM_ELC_CERT target derivation: {indent}exists {}.{} via {} -> {} (NF4); \
                 filler_choice={:?}",
                it.name(role),
                it.name(nf.filler),
                it.debug_name(target),
                it.name(concept),
                prov.get(&(target, nf.filler)),
            );
            *lines += 1;
            debug_el_membership_producers(
                target,
                nf.filler,
                st,
                nfs,
                it,
                prov,
                seen,
                depth - 1,
                lines,
            );
            for producer in nfs.nf3.iter().filter(|producer| {
                producer.role == role
                    && st.sub_super[target as usize].contains(&producer.filler)
                    && st.sub_super[node as usize].contains(&producer.sub)
            }) {
                eprintln!(
                    "KM_ELC_CERT target edge origin: {indent}{} -> exists {}.{} (NF3)",
                    it.name(producer.sub),
                    it.name(role),
                    it.debug_name(target),
                );
                *lines += 1;
                debug_el_membership_producers(
                    node,
                    producer.sub,
                    st,
                    nfs,
                    it,
                    prov,
                    seen,
                    depth - 1,
                    lines,
                );
            }
            for inclusion in nfs.nf6.iter().filter(|inclusion| inclusion.sup == role) {
                if st.edges[node as usize].contains(&(inclusion.sub, target)) {
                    eprintln!(
                        "KM_ELC_CERT target edge origin: {indent}{} edge lifted to {} (NF6)",
                        it.name(inclusion.sub),
                        it.name(role),
                    );
                    *lines += 1;
                }
            }
            for chain in nfs.nf7.iter().filter(|chain| chain.sup == role) {
                for &(first, middle) in &st.edges[node as usize] {
                    if first == chain.r1
                        && st.edges[middle as usize].contains(&(chain.r2, target))
                    {
                        eprintln!(
                            "KM_ELC_CERT target edge origin: {indent}{} o {} via {} -> {} (NF7)",
                            it.name(chain.r1),
                            it.name(chain.r2),
                            it.debug_name(middle),
                            it.name(role),
                        );
                        *lines += 1;
                        if *lines >= LINE_CAP {
                            return;
                        }
                    }
                }
            }
            debug_el_membership_producers(
                target, nf.filler, st, nfs, it, prov, seen, depth - 1, lines,
            );
            if *lines >= LINE_CAP {
                return;
            }
        }
    }
}

fn dedicated_witness_generator(target: u32, source: u32, st: &State, it: &Interner) -> Option<u32> {
    it.maybe_name(target)?
        .strip_prefix("__cert_witness__f_")
        .and_then(|name| name.rsplit_once('_').map(|(concept, _)| concept))
        .and_then(|concept| it.id(concept))
        .filter(|&generator| st.sub_super[source as usize].contains(&generator))
}

/// Human-readable residual clause for certificate-search diagnostics. This is
/// deliberately constructed only under `KM_ELC_DEBUG`: residual atoms store
/// compact ids in the hot path, while a failed search needs the original names
/// to make repeated conflict patterns actionable.
fn describe_residual_clause(rc: &RClause, it: &Interner) -> String {
    fn atom(a: &RAtom, it: &Interner) -> String {
        match *a {
            RAtom::C { cid, v } => format!("{}(v{v})", it.name(cid)),
            RAtom::R { rid, s, t } => format!("{}(v{s},v{t})", it.name(rid)),
            RAtom::Eq { s, t } => format!("v{s}=v{t}"),
        }
    }
    let side = |xs: &[RAtom], separator: &str| {
        if xs.is_empty() {
            "⊤".to_owned()
        } else {
            xs.iter()
                .map(|a| atom(a, it))
                .collect::<Vec<_>>()
                .join(separator)
        }
    };
    format!("{} -> {}", side(&rc.body, " ∧ "), side(&rc.head, " ∨ "))
}

/// Stable avalanche mixer for deterministic repair-portfolio choices.
///
/// Taking an odd multiply/add expression directly modulo a binary head only
/// observes its low bit.  That made every nominally different model seed
/// collapse to one of two node-parity assignments.  SplitMix64's finalizer
/// diffuses the node, clause, and pass bits before the modulo operation, so
/// each pass explores a genuinely different deterministic assignment.
fn repair_choice_mix(node: u32, clause: usize, pass: usize) -> usize {
    let mut x = (node as u64)
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        ^ (clause as u64).wrapping_mul(0xbf58_476d_1ce4_e5b9)
        ^ (pass as u64).wrapping_mul(0x94d0_49bb_1331_11eb);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    (x ^ (x >> 31)) as usize
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
    preserve_override: Option<&[String]>,
) -> CertOutcome {
    const MAX_ROUNDS: usize = 64;
    const PASS_BUDGET: u64 = 400_000_000;
    let n = base.sub_super.len();
    let mut is_named = vec![false; n];
    for &c in &nfs.concept_names {
        if c != TOP && c != BOTTOM && !crate::calc::is_internal_concept(it.name(c)) {
            is_named[c as usize] = true;
        }
    }
    // Concepts known empty through a unary NF1 chain. Normalisation commonly
    // represents disjointness as `A & B -> Q`, `Q -> Qbot`, `Qbot -> bottom`
    // rather than giving the NF2 rule a literal bottom head. Recovering this
    // chain lets greedy repair avoid the same impossible choice without adding
    // any consequence to the model.
    let mut known_bottom: HashSet<u32> = nfs.nf5.iter().copied().collect();
    // Bottom is itself known empty. Omitting it made direct normal forms such
    // as A & B -> bottom invisible both to disjointness guidance and to the
    // exact complement recognizer; only proxy concepts chained to bottom were
    // previously discovered.
    known_bottom.insert(BOTTOM);
    loop {
        let mut changed = false;
        for nf in &nfs.nf1 {
            if known_bottom.contains(&nf.sup) {
                changed |= known_bottom.insert(nf.sub);
            }
        }
        if !changed {
            break;
        }
    }
    // disjointness pairs (NF2 whose head is known bottom), for greedy choice
    // avoidance: prefer a disjunct that is not already incompatible with the
    // node's labels. This remains guidance only; banned choices remain
    // available in the final tier and the complete residual model is checked.
    let mut disj: HashMap<u32, HashSet<u32>> = HashMap::default();
    for f in &nfs.nf2 {
        if known_bottom.contains(&f.sup) {
            disj.entry(f.sub1).or_default().insert(f.sub2);
            disj.entry(f.sub2).or_default().insert(f.sub1);
        }
    }

    // qualified-cardinality guidance: which node pairs a `≥n` clause pins
    // apart, and which concepts activate a `≤n` bound when chosen
    let guide = CardGuide::new(rcs);
    let bulk_root_card_conflicts =
        std::env::var_os("KM_ELC_REPAIR_BULK_ROOT_CARD").is_some();
    let bulk_causal_clause_conflicts =
        std::env::var_os("KM_ELC_REPAIR_BULK_CAUSAL_CLAUSE").is_some();
    let bulk_causal_node_conflicts =
        std::env::var_os("KM_ELC_REPAIR_BULK_CAUSAL_NODE").is_some();
    let eager_causal_mix =
        std::env::var_os("KM_ELC_REPAIR_EAGER_CAUSAL_MIX").is_some();
    // Keep eager causal backtracking while independently preferring an
    // already-satisfied cardinality bound. This only orders candidate choices:
    // banned low sides, lazy-complement preferences, and exhausted covers keep
    // their existing alternatives. Publication still requires model checks.
    let cardinality_seeded = eager_causal_mix
        && std::env::var_os("KM_ELC_REPAIR_CARD_LOW_FIRST").is_none();
    let eager_continuation = eager_causal_mix
        && std::env::var_os("KM_ELC_REPAIR_EAGER_CONTINUATION").is_some();
    let causal_mix_batch: usize = std::env::var("KM_ELC_REPAIR_MIX_BATCH")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(64)
        .clamp(1, 4_096);
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
    // Diagnostic/portfolio hook: require selected named subjects to remain in
    // the domain of death-tolerant model passes. This does not certify them by
    // itself; any accepted pass still receives the complete residual-model
    // check, and failure remains fail-closed. It lets a model portfolio cover
    // satisfiable subjects that both default polarity models happen to kill.
    let configured_preserve = std::env::var("KM_ELC_PRESERVE").ok();
    let preserve_names: Vec<&str> = preserve_override
        .map(|names| names.iter().map(String::as_str).collect())
        .unwrap_or_else(|| {
            configured_preserve
                .as_deref()
                .into_iter()
                .flat_map(|names| names.split(','))
                .collect()
        });
    let preserve_named: Vec<u32> = preserve_names
        .into_iter()
        .filter_map(|name| it.id(name))
        .filter(|&c| is_named[c as usize] && !base.sub_super[c as usize].contains(&BOTTOM))
        .collect();

    // Diagnostic precursor to a rooted countermodel certificate. A model for
    // one negative taxonomy row needs only a nonempty subinterpretation rooted
    // at that subject, but it must remain closed under every existential edge
    // and retain every source pin. Build a conservative static carrier: all
    // requested roots, then admit only outgoing-edge targets and witnesses of
    // residual clauses whose exact source guards are inhabited. The carrier is
    // expanded again after every repair closure, so a newly enabled
    // existential target enters before the next residual check.
    //
    // This mode is deliberately diagnostic-only below. The existing
    // all-subject exactness proof expects one canonical node per named concept;
    // a rooted model needs a separate per-row countermodel wire before it may
    // publish anything.
    let rooted_domain =
        std::env::var_os("KM_ELC_REPAIR_ROOT_DOMAIN").is_some() && !preserve_named.is_empty();
    let mut fresh_inverse_roles: HashSet<u32> =
        if rooted_domain && std::env::var_os("KM_ELC_REPAIR_FRESH_ALL").is_some() {
            // Full source-specific unravelling for the rooted model.  NF3 is the
            // complete list of existential generators in the EL subset, so no
            // ordinary role edge is rewritten unless it has an existential
            // (role, filler) witness shape below.
            nfs.nf3.iter().map(|nf| nf.role).collect()
        } else if rooted_domain && std::env::var_os("KM_ELC_REPAIR_FRESH_INV").is_some() {
            rcs.iter().filter_map(inverse_functional_role).collect()
        } else {
            HashSet::default()
        };
    let mut unrestricted_fresh_roles = fresh_inverse_roles.clone();
    let mut selected_fresh_pairs = HashSet::default();
    let mut deep_unrestricted_fresh_roles = HashSet::default();
    let mut deep_selected_fresh_pairs = HashSet::default();
    let selective_deep = rooted_domain
        && (std::env::var_os("KM_ELC_REPAIR_FRESH_DEEP_ROLES").is_some()
            || std::env::var_os("KM_ELC_REPAIR_FRESH_DEEP_PAIRS").is_some());
    if rooted_domain {
        // A diagnostic may request the much smaller causal unravelling
        // frontier discovered from a failed rooted model. Unknown role names
        // are ignored, and `target` still rewrites only indexed NF3 witness
        // pairs, so this cannot capture asserted or residual-only edges.
        if let Ok(names) = std::env::var("KM_ELC_REPAIR_FRESH_ROLES") {
            for role in names
                .split(',')
                .map(str::trim)
                .filter(|name| !name.is_empty())
                .filter_map(|name| it.id(name))
            {
                fresh_inverse_roles.insert(role);
                unrestricted_fresh_roles.insert(role);
            }
        }
        // Exact `role=filler` pairs support causal unravelling without
        // recursively freshening every existential carried by a common role.
        if let Ok(pairs) = std::env::var("KM_ELC_REPAIR_FRESH_PAIRS") {
            for pair in pairs.split(',').map(str::trim).filter(|p| !p.is_empty()) {
                let Some((role, filler)) = pair.split_once('=') else {
                    continue;
                };
                let Some(role) = it.id(role.trim()) else {
                    continue;
                };
                let Some(filler) = it.id(filler.trim()) else {
                    continue;
                };
                fresh_inverse_roles.insert(role);
                selected_fresh_pairs.insert((role, filler));
            }
        }
        // Keep a complete source-specific first layer while restricting
        // recursive unravelling to a causal frontier. Merely defining either
        // variable enables the split; an empty value intentionally disables
        // all freshening below depth one.
        if let Ok(names) = std::env::var("KM_ELC_REPAIR_FRESH_DEEP_ROLES") {
            for role in names
                .split(',')
                .map(str::trim)
                .filter(|name| !name.is_empty())
                .filter_map(|name| it.id(name))
            {
                fresh_inverse_roles.insert(role);
                deep_unrestricted_fresh_roles.insert(role);
            }
        }
        if let Ok(pairs) = std::env::var("KM_ELC_REPAIR_FRESH_DEEP_PAIRS") {
            for pair in pairs.split(',').map(str::trim).filter(|p| !p.is_empty()) {
                let Some((role, filler)) = pair.split_once('=') else {
                    continue;
                };
                let Some(role) = it.id(role.trim()) else {
                    continue;
                };
                let Some(filler) = it.id(filler.trim()) else {
                    continue;
                };
                fresh_inverse_roles.insert(role);
                deep_selected_fresh_pairs.insert((role, filler));
            }
        }
    }
    let repair_concept_names: HashSet<u32> = if rooted_domain {
        let mut domain: HashSet<u32> = preserve_named.iter().copied().collect();
        let mut identity: Vec<u32> = (0..n as u32).collect();
        expand_rooted_domain(&mut domain, base, rcs, &mut identity);
        if debug {
            eprintln!(
                "KM_ELC_CERT rooted-domain diagnostic: roots={} carrier={} full={}",
                preserve_named.len(),
                domain.len(),
                nfs.concept_names.len(),
            );
        }
        domain
    } else {
        nfs.concept_names.clone()
    };
    // Explicit opt-in for per-row rooted certificates. A successful rooted
    // run may publish only its protected subjects; every other base-alive
    // named subject is marked unresolved and therefore omitted from output.
    let rooted_publish = rooted_domain && std::env::var_os("KM_ELC_REPAIR_ROOT_PUBLISH").is_some();
    let lazy_complements = if rooted_domain {
        regular_lazy_complements(rcs, nfs, &known_bottom, it)
    } else {
        Vec::new()
    };
    let implicit_covers: HashSet<usize> = lazy_complements
        .iter()
        .map(|complement| complement.cover_clause)
        .collect();
    let implicit_positive: HashMap<u32, u32> = lazy_complements
        .iter()
        .map(|complement| (complement.negative, complement.positive))
        .collect();
    let prefer_positive_guards: HashSet<u32> = implicit_positive.keys().copied().collect();
    // Every unambiguous universal binary concept cover gives either side a
    // concrete opposite branch. Cardinality partitions are commonly Q/Q
    // covers rather than the named/Q complements recognized above, so build
    // this map directly from the residual theory. Ambiguous concepts are
    // omitted and remain on the ordinary chooser.
    let mut cover_candidates: HashMap<u32, Option<(u32, usize)>> = HashMap::default();
    for (rci, rc) in rcs.iter().enumerate() {
        if !rc.pins.is_empty()
            || !(rc.body.is_empty()
                || rc
                    .body
                    .iter()
                    .all(|atom| matches!(atom, RAtom::C { cid, .. } if *cid == TOP)))
            || rc.head.len() != 2
        {
            continue;
        }
        let (RAtom::C { cid: left, v: lv }, RAtom::C { cid: right, v: rv }) =
            (rc.head[0], rc.head[1])
        else {
            continue;
        };
        if lv != rv || left == right {
            continue;
        }
        for (side, other) in [(left, right), (right, left)] {
            cover_candidates
                .entry(side)
                .and_modify(|slot| {
                    if *slot != Some((other, rci)) {
                        *slot = None;
                    }
                })
                .or_insert(Some((other, rci)));
        }
    }
    let universal_cover_alternatives: HashMap<u32, (u32, usize)> = cover_candidates
        .into_iter()
        .filter_map(|(side, alternative)| alternative.map(|value| (side, value)))
        .collect();
    // Causal reconstruction is a rooted-route facility.  Keep its reverse
    // indexes out of the ordinary certificate path so an Uberon-specific
    // search aid cannot tax the ORE routes that never consult it.
    let repair_trace = rooted_domain
        .then(|| RepairTraceIdx::new(nfs))
        .unwrap_or_default();
    if debug && !lazy_complements.is_empty() {
        eprintln!(
            "KM_ELC_CERT rooted-domain: {} regular complement cover(s) implicit",
            lazy_complements.len()
        );
    }
    let rooted_unverified = || {
        let protected: HashSet<u32> = preserve_named.iter().copied().collect();
        let mut unresolved: Vec<u32> = base_alive_named
            .iter()
            .copied()
            .filter(|c| !protected.contains(c))
            .collect();
        unresolved.sort_unstable();
        CertOutcome::Partial(unresolved)
    };

    enum PassOut {
        /// the base model already satisfies everything (plain certificate)
        Pristine,
        /// a complete pass model plus the provenance of its direct repair
        /// additions ((node, concept) -> choosing clause)
        Model(State, HashMap<(u32, u32), usize>),
        /// a ⊥-clause fired on a repair choice: ban that (node, clause,
        /// disjunct) triple and retry
        Conflict(Vec<(u32, usize, u32)>, Option<usize>),
        Fail,
    }

    // One repair pass under a per-clause choice-polarity vector.  Choices are
    // greedy (skip disjuncts disjoint with the node's current labels) with
    // the polarity as the tie-break, and every direct concept addition is
    // recorded so a later ⊥-violation can be traced back to the choice that
    // caused it (conflict-driven restart).
    // Rooted biomedical repairs can spend most of every conflict restart
    // rebuilding the same deterministic closure (lazy complement consumers,
    // low-cardinality partition sides, and their fresh existential witnesses).
    // That prefix is independent of polarity and the banned-choice set.  Keep
    // one fixpoint checkpoint and fork it for later attempts; only residual
    // disjunct choices are replayed.  The checkpoint contains no pending work,
    // and every accepted fork still passes the complete residual recheck.
    let mut deterministic_scaffold: Option<(
        State,
        HashSet<u32>,
        FreshInverseWitnesses,
        Vec<u32>,
    )> = None;
    let mut deterministic_scaffold_idx: Option<CertIdx> = None;
    // Rooted proof-neighbor backjumps operate on a causal chain of covering
    // clauses. Once both sides of one clause have killed the protected root,
    // trying the same clause at every isomorphic fresh carrier only repeats
    // the same failed partition. Remember that clause for this repair pass so
    // the next backjump crosses to the preceding proof decision. This is only
    // a search-order exclusion: accepted models still undergo full closure,
    // residual checking, and protected-root checking.
    let mut rooted_exhausted_backjump_clauses: HashSet<usize> = HashSet::default();
    // Number of distinct failed repair attempts that blamed each causal
    // clause. Covers represented by one explicit and one implicit-complement
    // side do not naturally acquire a per-instance "both sides tried"
    // sentinel. Remember recurrence across attempts so a two-clause cycle can
    // use the same proof-neighbor backjump path as an explicit sentinel.
    let mut rooted_clause_conflict_counts: HashMap<usize, usize> = HashMap::default();
    let mut run_pass = |polv: &[bool],
                    pass_label: usize,
                    banned: &HashSet<(u32, usize, u32)>,
                    tolerate_deaths: bool,
                    prebuilt: Option<CertIdx>|
     -> PassOut {
        let using_scaffold = deterministic_scaffold.is_some();
        let (mut st, mut repair_domain, mut fresh_inverse, mut repr) =
            if let Some((cached, domain, fresh, cached_repr)) = &deterministic_scaffold {
                (
                    cached.fork(),
                    domain.clone(),
                    fresh.clone(),
                    cached_repr.clone(),
                )
            } else {
                let repair_domain = repair_concept_names.clone();
                (
                    base.fork(),
                    repair_domain.clone(),
                    FreshInverseWitnesses {
                        roles: fresh_inverse_roles.clone(),
                        unrestricted_roles: unrestricted_fresh_roles.clone(),
                        selected_pairs: selected_fresh_pairs.clone(),
                        deep_unrestricted_roles: deep_unrestricted_fresh_roles.clone(),
                        deep_selected_pairs: deep_selected_fresh_pairs.clone(),
                        selective_deep,
                        active_sources: repair_domain,
                        depth: HashMap::default(),
                        max_depth: std::env::var("KM_ELC_REPAIR_FRESH_DEPTH")
                            .ok()
                            .and_then(|value| value.parse().ok()),
                        existential_pairs: nfs
                            .nf3
                            .iter()
                            .map(|nf| (nf.role, nf.filler))
                            .collect(),
                        nodes: HashMap::default(),
                        origins: HashMap::default(),
                        limit: std::env::var("KM_ELC_REPAIR_FRESH_INV_CAP")
                            .ok()
                            .and_then(|value| value.parse().ok())
                            .unwrap_or(100_000usize)
                            // Keep the ordinary 100k guard, but permit an
                            // explicitly memory-capped large-ontology route
                            // to unravel a second inverse-witness layer. Full
                            // Uberon reaches the former 1M ceiling before its
                            // complete residual check can run.
                            .clamp(1, 2_000_000),
                        exhausted: false,
                    },
                    (0..n as u32).collect(),
                )
            };
        // Journal label additions and reuse one enumeration index for the whole
        // pass: every round would otherwise rescan the entire structure to
        // rebuild an index a round changes only marginally (see [`CertIdx`]).
        st.start_journal();
        let mut cidx = if using_scaffold {
            deterministic_scaffold_idx.clone().unwrap_or_default()
        } else {
            prebuilt.unwrap_or_default()
        };
        // Optional scheduling knob for large residual repairs: re-close the EL
        // structure after this many additions instead of assigning an entire
        // stale violation batch first. Zero retains the established schedule.
        // This changes enumeration order only; a published model still reaches
        // the same EL fixpoint and passes the complete residual recheck.
        let close_batch: u64 = std::env::var("KM_ELC_REPAIR_CLOSE_BATCH")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        // The default bounds ordinary certificate attempts. Large biomedical
        // terminologies can have a compact residual but hundreds of thousands
        // of violating canonical-model instances per round. Permit a routed
        // high-budget attempt without changing the default or weakening the
        // fail-closed contract: exhaustion still returns `Fail`, and every
        // successful model receives the same complete residual recheck.
        let mut budget: u64 = std::env::var("KM_ELC_REPAIR_BUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(PASS_BUDGET);
        let mut adds: u64 = 0;
        let mut merged: Vec<u32> = Vec::new();
        let mut prov: HashMap<(u32, u32), usize> = HashMap::default();
        // chronological choice log (node, clause, disjunct) for blame when
        // the direct lookup misses (conflicting facts often arrive via the
        // closure, not directly)
        let mut chrono: Vec<(u32, usize, u32)> = Vec::new();
        // Promote repeated node-local conflicts into a clause-side search
        // preference. Uberon's unravelled witnesses are structurally
        // isomorphic, so learning the same bad side at hundreds of nodes one
        // full closure at a time is redundant. This set only affects preferred
        // tiers: exact node bans still govern backtracking and tier 3 still
        // admits every side before a model can be accepted.
        let global_side_threshold: usize = std::env::var("KM_ELC_REPAIR_GLOBAL_SIDE_LEARN")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(0);
        let globally_avoided_sides: HashSet<(usize, u32)> = if global_side_threshold == 0 {
            HashSet::default()
        } else {
            let mut counts: HashMap<(usize, u32), usize> = HashMap::default();
            for &(_, clause, concept) in banned {
                if concept != u32::MAX {
                    *counts.entry((clause, concept)).or_default() += 1;
                }
            }
            counts
                .into_iter()
                .filter_map(|(side, count)| (count >= global_side_threshold).then_some(side))
                .collect()
        };
        if debug && !globally_avoided_sides.is_empty() {
            eprintln!(
                "KM_ELC_CERT repair pass {pass_label}: globally avoiding {} repeatedly failing clause side(s)",
                globally_avoided_sides.len(),
            );
        }
        // quotient-dependent half of the cardinality guidance, re-lifted to the
        // current union-find representatives at the head of every round and
        // after every merge inside one
        let mut cround = CardRound::default();
        // A small close batch deliberately trades more EL fixpoints for fewer
        // stale residual choices.  Keep the production ceiling unchanged, but
        // let a routed large-ontology attempt supply enough rounds to spend its
        // configured repair budget.  This is only a search-schedule bound: a
        // successful pass still has to reach a fixpoint and satisfy the full
        // residual check.
        let max_rounds: usize = std::env::var("KM_ELC_REPAIR_MAX_ROUNDS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(MAX_ROUNDS)
            .max(1);

        // With cardinality guidance present, the old checkpoint guard had to
        // disable caching altogether: the combined loop below interleaves
        // deterministic lazy-complement consequences with revisable low/high
        // partition choices.  Build and cache the choice-free prefix first.
        // Later passes fork exactly this fixpoint, then replay every partition
        // choice under their current banned set and still undergo the ordinary
        // complete residual check.
        if rooted_domain
            && !guide.by_guard.is_empty()
            && !using_scaffold
            && deterministic_scaffold.is_none()
            && !lazy_complements.is_empty()
        {
            // Redirect canonical existential edges before any implicit
            // complement fires. Otherwise a negative label added to a shared
            // canonical filler can trigger NF4 back into the protected root;
            // redirecting the edge afterwards cannot retract that monotone
            // conclusion. This unravelling depends only on the choice-free
            // base state and remains deterministic across conflict restarts.
            loop {
                let admitted =
                    expand_rooted_domain(&mut repair_domain, &st, rcs, &mut repr);
                fresh_inverse
                    .active_sources
                    .extend(repair_domain.iter().copied());
                let redirected = if fresh_inverse.roles.is_empty() {
                    0
                } else {
                    freshen_rooted_inverse_edges(
                        &repair_domain,
                        &mut st,
                        &mut fresh_inverse,
                        &idx.role_sub,
                    )
                };
                if redirected == 0 {
                    break;
                }
                run_with_fresh_inverse(idx, &mut st, &mut Prof::default(), &mut fresh_inverse);
                if fresh_inverse.exhausted {
                    if debug {
                        eprintln!(
                            "KM_ELC_CERT repair pass {pass_label}: fresh inverse-witness cap \
                             {} exhausted during pre-complement redirection",
                            fresh_inverse.limit,
                        );
                    }
                    return PassOut::Fail;
                }
                if repr.len() < st.sub_super.len() {
                    repr.extend(repr.len() as u32..st.sub_super.len() as u32);
                }
                if debug {
                    eprintln!(
                        "KM_ELC_CERT repair pass {pass_label}: pre-complement scaffold carrier \
                         +{admitted}, redirected {redirected} existential edge(s)"
                    );
                }
            }
            loop {
                let complement_added = fire_lazy_complement_consumers(
                    &lazy_complements,
                    &repair_domain,
                    &mut st,
                    &mut repr,
                    nfs,
                    &known_bottom,
                    banned,
                    &mut prov,
                    &mut chrono,
                    false,
                    it,
                );
                if complement_added == 0 {
                    break;
                }
                run_with_fresh_inverse(idx, &mut st, &mut Prof::default(), &mut fresh_inverse);
                if fresh_inverse.exhausted {
                    if debug {
                        eprintln!(
                            "KM_ELC_CERT repair pass {pass_label}: fresh inverse-witness cap \
                             {} exhausted during lazy-complement closure",
                            fresh_inverse.limit,
                        );
                    }
                    return PassOut::Fail;
                }
                if repr.len() < st.sub_super.len() {
                    repr.extend(repr.len() as u32..st.sub_super.len() as u32);
                }
                let admitted =
                    expand_rooted_domain(&mut repair_domain, &st, rcs, &mut repr);
                fresh_inverse
                    .active_sources
                    .extend(repair_domain.iter().copied());
                if debug {
                    eprintln!(
                        "KM_ELC_CERT repair pass {pass_label}: deterministic prefix \
                         (complements +{complement_added}, carrier +{admitted})"
                    );
                }
            }
            deterministic_scaffold = Some((
                st.fork(),
                repair_domain.clone(),
                fresh_inverse.clone(),
                repr.clone(),
            ));
            if debug {
                eprintln!(
                    "KM_ELC_CERT repair: cached choice-free scaffold (nodes={}, carrier={})",
                    st.sub_super.len(),
                    repair_domain.len(),
                );
            }
        }
        for round in 1..=max_rounds {
            if !lazy_complements.is_empty() || (rooted_domain && !guide.by_guard.is_empty()) {
                loop {
                    let complement_added = fire_lazy_complement_consumers(
                        &lazy_complements,
                        &repair_domain,
                        &mut st,
                        &mut repr,
                        nfs,
                        &known_bottom,
                        banned,
                        &mut prov,
                        &mut chrono,
                        true,
                        it,
                    );
                    let cardinality_added = guide.choose_low_sides(
                        &repair_domain,
                        &mut st,
                        &mut repr,
                        it,
                        &universal_cover_alternatives,
                        &prefer_positive_guards,
                        &globally_avoided_sides,
                        banned,
                        cardinality_seeded,
                        pass_label,
                        &mut prov,
                        &mut chrono,
                    );
                    let added = complement_added + cardinality_added;
                    if added == 0 {
                        break;
                    }
                    // These insertions change the candidate model even though
                    // they occur before ordinary residual-head repair. Count
                    // them so a clean first certificate round returns Model,
                    // not Pristine: the latter bypasses the per-subject model
                    // intersection and is valid only when no repair fact was
                    // added at all.
                    adds = adds.saturating_add(added as u64);
                    run_with_fresh_inverse(idx, &mut st, &mut Prof::default(), &mut fresh_inverse);
                    if fresh_inverse.exhausted {
                        if debug {
                            eprintln!(
                                "KM_ELC_CERT repair pass {pass_label}: fresh inverse-witness cap \
                             {} exhausted during eager causal closure",
                                fresh_inverse.limit,
                            );
                            fresh_inverse.report_population(&st, it);
                        }
                        return PassOut::Fail;
                    }
                    if repr.len() < st.sub_super.len() {
                        repr.extend(repr.len() as u32..st.sub_super.len() as u32);
                    }
                    let admitted = expand_rooted_domain(&mut repair_domain, &st, rcs, &mut repr);
                    fresh_inverse
                        .active_sources
                        .extend(repair_domain.iter().copied());
                    if debug {
                        eprintln!(
                            "KM_ELC_CERT repair pass {pass_label} round {round}: implicit \
                             complements +{complement_added}, low-cardinality sides \
                             +{cardinality_added}, carrier +{admitted}"
                        );
                    }
                }
                if round == 1
                    && (!rooted_domain || guide.by_guard.is_empty())
                    && !using_scaffold
                    && deterministic_scaffold.is_none()
                {
                    deterministic_scaffold = Some((
                        st.fork(),
                        repair_domain.clone(),
                        fresh_inverse.clone(),
                        repr.clone(),
                    ));
                    if debug {
                        eprintln!(
                            "KM_ELC_CERT repair: cached deterministic scaffold (nodes={}, \
                             carrier={})",
                            st.sub_super.len(),
                            repair_domain.len(),
                        );
                    }
                }
            }
            let mut viols: Vec<(usize, Vec<u32>)> = Vec::new();
            // Repair can allocate source-specific witnesses beyond the
            // ontology interner's original concept domain. Residual equality
            // heads range over those live nodes too, so their representative
            // snapshot must cover the complete repaired state rather than
            // only `0..n`. The union-find is extended whenever fresh nodes are
            // admitted immediately above.
            let crep: Vec<u32> = (0..st.sub_super.len() as u32)
                .map(|i| uf_find(&mut repr, i))
                .collect();
            if rooted_domain {
                cround.resync_active(&guide, &mut repr, &st, &repair_domain);
            } else {
                cround.resync(&guide, &mut repr);
            }
            let delta = st.drain_journal();
            let epoch = st.edge_epoch;
            let clean = cert_round(
                rcs,
                &repair_domain,
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
                Some(&implicit_covers),
                Some(&implicit_positive),
            );
            if round == 1
                && (!rooted_domain || guide.by_guard.is_empty())
                && !using_scaffold
                && deterministic_scaffold_idx.is_none()
            {
                deterministic_scaffold_idx = Some(cidx.clone());
            }
            // A complete residual model can still have killed a protected
            // rooted subject: bottom nodes satisfy clauses vacuously. Delay
            // acceptance until after the protected-death check below, where
            // its causal choice is learned. This also keeps a repaired model
            // from bypassing the exact per-subject intersection criterion.
            if !clean && viols.is_empty() {
                // `cert_round` also returns false without violations when a
                // pinned Skolem witness has died. This is a choice conflict,
                // not budget exhaustion: a certified model must interpret
                // every source Skolem function. Feed all choices made at
                // newly dead nodes back into the next attempt, including in a
                // death-tolerant pass (which tolerates named-query deaths but
                // never dead canonical witnesses).
                let mut dead_pin = None;
                'find_dead_pin: for rc in rcs {
                    let mut active = true;
                    for &(_, guard, _) in &rc.pin_guards {
                        let guard_has_member = repair_domain.iter().any(|&candidate| {
                            let node = uf_find(&mut repr, candidate);
                            !st.sub_super[node as usize].contains(&BOTTOM)
                                && st.sub_super[node as usize].contains(&guard)
                        });
                        if !guard_has_member {
                            active = false;
                            break;
                        }
                    }
                    if !active {
                        continue;
                    }
                    for &(_, pin) in &rc.pins {
                        let node = uf_find(&mut repr, pin);
                        if st.sub_super[node as usize].contains(&BOTTOM) {
                            dead_pin = Some(pin);
                            break 'find_dead_pin;
                        }
                    }
                }
                if let Some(pin) = dead_pin {
                    let mut seen: HashSet<(u32, usize, u32)> = HashSet::default();
                    let pin_rep = uf_find(&mut repr, pin);
                    // Learn one local decision, not every historical decision
                    // at the dead representative.  The latter over-learns:
                    // several residual clauses may have been repaired at the
                    // same node before one later choice closes it to bottom.
                    // Prefer a directly disjoint chosen concept, which is an
                    // actual local explanation of the death.
                    let mut blame: Vec<(u32, usize, u32)> = chrono
                        .iter()
                        .rev()
                        .filter_map(|&triple| {
                            if !repair_choice_untried(banned, triple) {
                                return None;
                            }
                            let node = uf_find(&mut repr, triple.0);
                            (node == pin_rep
                                && disj.get(&triple.2).is_some_and(|ds| {
                                    ds.iter().any(|d| st.sub_super[node as usize].contains(d))
                                })
                                && seen.insert(triple))
                            .then_some(triple)
                        })
                        .take(1)
                        .collect();
                    if blame.is_empty() {
                        if let Some(triple) = chrono.iter().rev().find_map(|&triple| {
                            if !repair_choice_untried(banned, triple) {
                                return None;
                            }
                            (uf_find(&mut repr, triple.0) == pin_rep).then_some(triple)
                        }) {
                            blame.push(triple);
                        }
                    }
                    if blame.is_empty() {
                        let exhausted_local = chrono
                            .iter()
                            .rev()
                            .find(|&&triple| uf_find(&mut repr, triple.0) == pin_rep)
                            .copied();
                        let backjump = exhausted_local
                            .and_then(|local| {
                                chrono.iter().rev().find(|&&triple| {
                                    (triple.0, triple.1) != (local.0, local.1)
                                })
                            })
                            .copied()
                            .or(exhausted_local);
                        if let Some(triple) = backjump {
                            blame.push(triple);
                        }
                    }
                    if !blame.is_empty() {
                        if debug {
                            let first = blame[0];
                            eprintln!(
                                "KM_ELC_CERT repair pass {pass_label}: pinned witness {} died, \
                                 batching {} choice ban(s); first={:?} (node={}, concept={}); \
                                 choice_clause={}",
                                it.name(pin),
                                blame.len(),
                                first,
                                it.debug_name(first.0),
                                it.name(first.2),
                                describe_residual_clause(&rcs[first.1], it),
                            );
                        }
                        return PassOut::Conflict(blame, None);
                    }
                    if debug {
                        let chosen_here: Vec<String> = chrono
                            .iter()
                            .filter(|t| uf_find(&mut repr, t.0) == pin_rep)
                            .map(|t| {
                                format!(
                                    "{:?}:{}:{}",
                                    t,
                                    if banned.contains(t) { "banned" } else { "live" },
                                    describe_residual_clause(&rcs[t.1], it),
                                )
                            })
                            .collect();
                        eprintln!(
                            "KM_ELC_CERT repair pass {pass_label}: pinned witness {} died \
                             without a repair choice; choices_here=[{}]",
                            it.name(pin),
                            chosen_here.join(" | "),
                        );
                    }
                    return PassOut::Fail;
                }
                if debug {
                    eprintln!(
                        "KM_ELC_CERT repair pass {pass_label}: budget exhausted (round {round})"
                    );
                }
                return PassOut::Fail;
            }
            if debug && (round == 1 || round % 64 == 0) {
                let mut counts: HashMap<usize, usize> = HashMap::default();
                for &(rci, _) in &viols {
                    *counts.entry(rci).or_default() += 1;
                }
                let mut counts: Vec<(usize, usize)> = counts.into_iter().collect();
                counts.sort_unstable_by_key(|&(rci, count)| (std::cmp::Reverse(count), rci));
                let summary = counts
                    .into_iter()
                    .take(8)
                    .map(|(rci, count)| {
                        format!("{rci}:{count}:{}", describe_residual_clause(&rcs[rci], it))
                    })
                    .collect::<Vec<_>>()
                    .join(" | ");
                eprintln!(
                    "KM_ELC_CERT repair pass {pass_label} round {round}: top violations: {summary}"
                );
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
            let mut round_adds = 0u64;
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
                let concept_is_free = |nd: u32, cid: u32| {
                    let candidate_supers = &base.sub_super[cid as usize];
                    !candidate_supers.iter().any(|candidate_super| {
                        disj.get(candidate_super).is_some_and(|partners| {
                            st.sub_super[nd as usize].iter().any(|present| {
                                partners.contains(present)
                                    || base.sub_super[*present as usize]
                                        .iter()
                                        .any(|present_super| partners.contains(present_super))
                            })
                        })
                    })
                };
                // Universal covers introduced for negated definers commonly
                // have the shape `top -> Named(x) | Q_not_Named(x)`. Choosing
                // the named side at every carrier node activates an unrelated
                // taxonomy and can turn a 74-node rooted model into millions
                // of closure facts. In a rooted countermodel, prefer a legal
                // internal side regardless of seed polarity. This is only a
                // model-search heuristic: bans still redirect a bad choice,
                // EL closure still follows every selected label, and the full
                // residual theory is checked before publication.
                let universal_cover = head.len() > 1
                    && (rcs[*rci].body.is_empty()
                        || rcs[*rci]
                            .body
                            .iter()
                            .all(|atom| matches!(atom, RAtom::C { cid, .. } if *cid == TOP)));
                // A rooted ontology can contain a long sequence of universal
                // binary partitions whose uniform choices kill different
                // fresh witnesses.  Waiting until every node has tried both
                // sides reveals those partitions one at a time.  The opt-in
                // eager portfolio starts same-variable covers with a stable
                // node-dependent side instead.  This is only a candidate-model
                // schedule: explicit conflict bans still take precedence, EL
                // closure is unchanged, and publication still requires the
                // exhaustive residual check.
                let eager_mixed = if rooted_domain
                    && bulk_causal_clause_conflicts
                    && eager_causal_mix
                    && universal_cover
                    && !cands.is_empty()
                {
                    let first_var = cands.first().and_then(|atom| match **atom {
                        RAtom::C { v, .. } => Some(v),
                        _ => None,
                    });
                    first_var.and_then(|v| {
                        cands
                            .iter()
                            .all(|atom| matches!(**atom, RAtom::C { v: av, .. } if av == v))
                            .then(|| {
                                let nd = uf_find(&mut repr, asg[v]);
                                let mixed = repair_choice_mix(nd, *rci, pass_label);
                                (0..cands.len()).find_map(|offset| {
                                    let canonical_index = (mixed + offset) % cands.len();
                                    // `cands` follows the ordinary polarity
                                    // seed and is reversed when `polv[rci]` is
                                    // true. Recover canonical head order here:
                                    // otherwise polarity reversal and a changed
                                    // binary hash bit can cancel one another,
                                    // producing the same eager assignment.
                                    let atom = if polv[*rci] {
                                        cands[cands.len() - 1 - canonical_index]
                                    } else {
                                        cands[canonical_index]
                                    };
                                    let RAtom::C { cid, .. } = *atom else {
                                        unreachable!()
                                    };
                                    // Unlike the ordinary greedy tiers, an
                                    // eager portfolio seed must be allowed to
                                    // sample either unbanned side. Applying
                                    // local cardinality guidance here reduced
                                    // some binary covers to one candidate and
                                    // made every seed identical. Any bad side
                                    // still dies during closure or fails the
                                    // exhaustive residual-model check.
                                    (!banned.contains(&(nd, *rci, cid))
                                        && !globally_avoided_sides.contains(&(*rci, cid)))
                                        .then_some(atom)
                                })
                            })
                            .flatten()
                    })
                } else {
                    None
                };
                let preferred_rooted_definer = if rooted_domain && universal_cover {
                    cands.iter().find_map(|atom| match **atom {
                        RAtom::C { cid, v } => {
                            let nd = uf_find(&mut repr, asg[v]);
                            (!banned.contains(&(nd, *rci, cid))
                                && !globally_avoided_sides.contains(&(*rci, cid))
                                && crate::calc::is_internal_concept(it.name(cid))
                                && concept_is_free(nd, cid)
                                && !guide.locally_incompatible(
                                    &mut cround,
                                    &st,
                                    &mut repr,
                                    nd,
                                    cid,
                                ))
                            .then_some(*atom)
                        }
                        _ => None,
                    })
                } else {
                    None
                };
                // In the rooted fresh-witness diagnostic, prefer a legal,
                // nonclashing equality branch of a mixed cardinality head.
                // Choosing its concept alternative first commonly activates a
                // complement definer and creates an avoidable root clash. This
                // is search order only; the complete residual check is still
                // required before accepting the model.
                let preferred_eq = if preferred_rooted_definer.is_none()
                    && rooted_domain
                    && !fresh_inverse.roles.is_empty()
                {
                    head.iter().find(|atom| match **atom {
                        RAtom::Eq { s, t } => {
                            let (u, w) = (asg[s], asg[t]);
                            guide.merge_legal(&cround, &mut repr, u, w)
                                && !guide.merge_clashes(&st, &disj, &mut repr, u, w)
                        }
                        _ => false,
                    })
                } else {
                    None
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
                // A clause can exhaust both uniform polarities at every
                // carrier node.  Its bans are deliberately soft, but falling
                // through to tier 3 used to choose the same first disjunct at
                // every instance again.  For the explicit rooted causal
                // portfolio, use a stable node-dependent tie-break once every
                // concept alternative at this instance has already been
                // tried.  This exposes non-uniform models without asserting
                // any fact or weakening the final complete residual check.
                let mixed_exhausted = if rooted_domain
                    && bulk_causal_clause_conflicts
                    && !cands.is_empty()
                    && {
                        let sentinel = cands.first().is_some_and(|atom| match **atom {
                            RAtom::C { v, .. } => {
                                let nd = uf_find(&mut repr, asg[v]);
                                banned.contains(&(nd, *rci, u32::MAX))
                            }
                            _ => false,
                        });
                        sentinel
                            || cands.iter().all(|atom| match **atom {
                                RAtom::C { cid, v } => {
                                    let nd = uf_find(&mut repr, asg[v]);
                                    banned.contains(&(nd, *rci, cid))
                                }
                                _ => false,
                            })
                    }
                {
                    let RAtom::C { v, .. } = *cands[0] else {
                        unreachable!()
                    };
                    let nd = uf_find(&mut repr, asg[v]);
                    let mixed = repair_choice_mix(nd, *rci, pass_label);
                    cands.get(mixed % cands.len()).copied()
                } else {
                    None
                };
                let mut pick: Option<&RAtom> = mixed_exhausted
                    .or(eager_mixed)
                    .or(preferred_rooted_definer)
                    .or(preferred_eq);
                for tier in 0..4u8 {
                    if pick.is_some() {
                        break;
                    }
                    for a in &cands {
                        let ok = match **a {
                            RAtom::C { cid, v } => {
                                let nd = uf_find(&mut repr, asg[v]);
                                let unbanned = !banned.contains(&(nd, *rci, cid))
                                    && !globally_avoided_sides.contains(&(*rci, cid));
                                match tier {
                                    0 => {
                                        unbanned
                                            && concept_is_free(nd, cid)
                                            && !guide.locally_incompatible(
                                                &mut cround,
                                                &st,
                                                &mut repr,
                                                nd,
                                                cid,
                                            )
                                    }
                                    1 => unbanned && concept_is_free(nd, cid),
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
                        // A singleton head is a forced consequence, not a
                        // branch the repair search may revise.  Recording it
                        // as provenance made protected-root conflict learning
                        // "ban" the same unavoidable consequence at one fresh
                        // node after another.  Only a genuinely disjunctive
                        // head denotes a model choice.  Forced memberships
                        // remain available to EL closure, but attribution
                        // walks past them (or falls back to an earlier real
                        // choice) instead of learning a no-op ban.
                        if head.len() > 1 {
                            prov.entry((nd, cid)).or_insert(*rci);
                            chrono.push((nd, *rci, cid));
                        }
                    }
                    Some(&RAtom::R { rid, s, t }) => {
                        let sn = uf_find(&mut repr, asg[s]);
                        let tn = uf_find(&mut repr, asg[t]);
                        st.add_edge(sn, rid, tn);
                    }
                    Some(&RAtom::Eq { s, t }) => {
                        let (u, w) = (asg[s], asg[t]);
                        merge_nodes(&mut st, &mut repr, &mut merged, u, w);
                        cround.resync_active(&guide, &mut repr, &st, &repair_domain);
                    }
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
                                if rooted_domain {
                                    cround.resync_active(&guide, &mut repr, &st, &repair_domain);
                                } else {
                                    cround.resync(&guide, &mut repr);
                                }
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
                                            it.debug_name(triple.0),
                                            it.name(triple.2),
                                        );
                                    }
                                    return PassOut::Conflict(vec![triple], Some(viols.len()));
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
                                             — genuine inconsistency); clause={}; binding={:?}",
                                            describe_residual_clause(&rcs[*rci], it),
                                            asg.iter()
                                                .map(|&node| it.debug_name(node))
                                                .collect::<Vec<_>>(),
                                        );
                                    }
                                    return PassOut::Fail;
                                }
                            }
                        }
                    }
                }
                adds += 1;
                round_adds += 1;
                if close_batch != 0 && round_adds >= close_batch {
                    break;
                }
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
            if fresh_inverse.roles.is_empty() {
                run(idx, &mut st, &mut Prof::default());
            } else {
                run_with_fresh_inverse(idx, &mut st, &mut Prof::default(), &mut fresh_inverse);
                if fresh_inverse.exhausted {
                    if debug {
                        eprintln!(
                            "KM_ELC_CERT repair pass {pass_label}: fresh inverse-witness cap \
                             {} exhausted",
                            fresh_inverse.limit,
                        );
                    }
                    return PassOut::Fail;
                }
                if repr.len() < st.sub_super.len() {
                    repr.extend(repr.len() as u32..st.sub_super.len() as u32);
                }
            }
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
            if rooted_domain {
                loop {
                    let admitted = expand_rooted_domain(&mut repair_domain, &st, rcs, &mut repr);
                    fresh_inverse
                        .active_sources
                        .extend(repair_domain.iter().copied());
                    let redirected = if fresh_inverse.roles.is_empty() {
                        0
                    } else {
                        freshen_rooted_inverse_edges(
                            &repair_domain,
                            &mut st,
                            &mut fresh_inverse,
                            &idx.role_sub,
                        )
                    };
                    if admitted != 0 || redirected != 0 {
                        cidx.invalidate();
                        if debug {
                            eprintln!(
                                "KM_ELC_CERT repair pass {pass_label} round {round}: rooted \
                                 carrier +{admitted} -> {} node(s), redirected {redirected} \
                                 inverse-functional existential edge(s)",
                                repair_domain.len(),
                            );
                        }
                    }
                    if redirected == 0 {
                        break;
                    }
                    run_with_fresh_inverse(idx, &mut st, &mut Prof::default(), &mut fresh_inverse);
                    if fresh_inverse.exhausted {
                        if debug {
                            eprintln!(
                                "KM_ELC_CERT repair pass {pass_label}: fresh inverse-witness cap \
                                 {} exhausted during rooted carrier expansion",
                                fresh_inverse.limit,
                            );
                        }
                        return PassOut::Fail;
                    }
                    if repr.len() < st.sub_super.len() {
                        repr.extend(repr.len() as u32..st.sub_super.len() as u32);
                    }
                }
            }
            // A repair choice can cascade several base-satisfiable named
            // witnesses to bottom in the same closure. The old restart fed
            // back only one choice, then rebuilt the identical 100k-instance
            // round for every other dead node. Collect every unbanned direct
            // choice made at a newly dead node. A ban is only a preference:
            // tier 3 can still select it, and the final complete residual
            // recheck is unchanged, so batching changes search order only.
            // A rooted countermodel is required to preserve its requested
            // subject, not every unrelated canonical named witness. Requiring
            // the latter recreates the all-subject model and triggers restarts
            // for deaths outside the carrier's proof obligation. This branch
            // remains diagnostic-only and cannot publish below.
            let protected_named = if rooted_domain || tolerate_deaths {
                &preserve_named
            } else {
                &base_alive_named
            };
            if !protected_named.is_empty() {
                let first_dead = protected_named.iter().copied().find(|&c| {
                    let cr = uf_find(&mut repr, c);
                    st.sub_super[cr as usize].contains(&BOTTOM)
                });
                if let Some(c) = first_dead {
                    let mut seen: HashSet<(u32, usize, u32)> = HashSet::default();
                    let dead_reps: HashSet<u32> = protected_named
                        .iter()
                        .filter_map(|&named| {
                            let rep = uf_find(&mut repr, named);
                            (st.sub_super[rep as usize].contains(&BOTTOM)
                                && !base.sub_super[rep as usize].contains(&BOTTOM))
                            .then_some(rep)
                        })
                        .collect();
                    // At most one learned choice per dead representative.
                    // Prefer a chosen concept with a direct disjoint partner
                    // in that representative's closed label.  This retains
                    // the ontology-wide batching win without banning earlier,
                    // unrelated repairs made at the same node.
                    let mut explained: HashSet<u32> = HashSet::default();
                    let mut blame: Vec<(u32, usize, u32)> = chrono
                        .iter()
                        .rev()
                        .filter_map(|&triple| {
                            if !repair_choice_untried(banned, triple) {
                                return None;
                            }
                            let nd = uf_find(&mut repr, triple.0);
                            (dead_reps.contains(&nd)
                                && (rooted_domain || !explained.contains(&nd))
                                && base.sub_super[triple.2 as usize].iter().any(
                                    |candidate_super| {
                                        disj.get(candidate_super).is_some_and(|partners| {
                                            st.sub_super[nd as usize].iter().any(|present| {
                                                partners.contains(present)
                                                    || base.sub_super[*present as usize].iter().any(
                                                        |present_super| {
                                                            partners.contains(present_super)
                                                        },
                                                    )
                                            })
                                        })
                                    },
                                )
                                && seen.insert(triple))
                            .then_some(triple)
                        })
                        .collect();
                    for &triple in &blame {
                        explained.insert(uf_find(&mut repr, triple.0));
                    }
                    let mut direct_dead_conflict = false;
                    let mut direct_dead_clauses: HashSet<usize> = HashSet::default();
                    let mut recurrence_counted_clauses: HashSet<usize> = HashSet::default();
                    let mut proof_path_reopen = false;
                    if rooted_domain {
                        let mut causal = Vec::new();
                        let mut causal_seen = HashSet::default();
                        for &root in &dead_reps {
                            // A fresh witness can become the representative of
                            // a protected root after an equality repair. Trace
                            // through its generating existential before
                            // blaming a later choice made on the witness.
                            if let Some(&(source0, role, filler)) = fresh_inverse.origins.get(&root)
                            {
                                let source = uf_find(&mut repr, source0);
                                for producer in nfs.nf3.iter().filter(|nf| {
                                    nf.role == role
                                        && nf.filler == filler
                                        && st.sub_super[source as usize].contains(&nf.sub)
                                }) {
                                    let mut trace_seen = HashSet::default();
                                    if let Some(upstream) = trace_repair_choice(
                                        source,
                                        producer.sub,
                                        &st,
                                        nfs,
                                        &repair_trace,
                                        it,
                                        &mut repr,
                                        &prov,
                                        banned,
                                        &mut trace_seen,
                                        96,
                                    ) {
                                        proof_path_reopen = true;
                                        if causal_seen.insert(upstream) {
                                            causal.push(upstream);
                                        }
                                    }
                                }
                            }
                            for &(role, target0) in &st.edges[root as usize] {
                                let target = uf_find(&mut repr, target0);
                                if !st.sub_super[target as usize].contains(&BOTTOM) {
                                    continue;
                                }
                                // Explain the dead successor at the point
                                // where bottom was actually derived before
                                // considering any of the root's many possible
                                // existential producers. On Uberon the latter
                                // picked an incidental source path, while this
                                // target-local walk reaches the partition
                                // choice that contaminated the fresh copy.
                                let mut target_seen = HashSet::default();
                                if let Some(upstream) = trace_repair_choice(
                                    target,
                                    BOTTOM,
                                    &st,
                                    nfs,
                                    &repair_trace,
                                    it,
                                    &mut repr,
                                    &prov,
                                    banned,
                                    &mut target_seen,
                                    128,
                                ) {
                                    proof_path_reopen = true;
                                    if causal_seen.insert(upstream) {
                                        causal.push(upstream);
                                    }
                                }
                                let mut generators = Vec::new();
                                if let Some(generator) =
                                    dedicated_witness_generator(target, root, &st, it)
                                {
                                    generators.push(generator);
                                } else {
                                    // A shared canonical target can have many
                                    // independent NF3 producers. The edge dies
                                    // only after every active producer is
                                    // avoided, so learn all source decisions in
                                    // the same closed state.
                                    generators.extend(nfs.nf3.iter().filter_map(|nf| {
                                        (nf.role == role
                                            && st.sub_super[target as usize].contains(&nf.filler)
                                            && st.sub_super[root as usize].contains(&nf.sub))
                                        .then_some(nf.sub)
                                    }));
                                }
                                for generator in generators {
                                    let mut trace_seen = HashSet::default();
                                    if let Some(upstream) = trace_repair_choice(
                                        root,
                                        generator,
                                        &st,
                                        nfs,
                                        &repair_trace,
                                        it,
                                        &mut repr,
                                        &prov,
                                        banned,
                                        &mut trace_seen,
                                        96,
                                    ) {
                                        proof_path_reopen = true;
                                        if causal_seen.insert(upstream) {
                                            causal.push(upstream);
                                        }
                                    }
                                }
                            }
                        }
                        // Prefer an actual local cause of bottom over the
                        // broader existential-path explanation.  A covering
                        // choice can close to its explicitly disjoint sibling
                        // on a fresh successor.  The previous path expansion
                        // then returned every partition selected on that
                        // successor (80 bans on Uberon), sentinelized the
                        // whole assignment, and advanced to the next fresh
                        // node without ever flipping just the conflicting
                        // side.  Charge the most recent chosen concept whose
                        // closed representative contains a disjoint partner.
                        // This is ordinary conflict-directed search: the ban
                        // remains soft, and accepted models still undergo the
                        // complete residual and protected-root checks.
                        let direct_dead_choices: Vec<(u32, usize, u32)> = chrono
                            .iter()
                            .rev()
                            .copied()
                            .filter(|&triple| {
                                let node = uf_find(&mut repr, triple.0);
                                if !st.sub_super[node as usize].contains(&BOTTOM) {
                                    return false;
                                }
                                let directly_clashing = base.sub_super[triple.2 as usize]
                                    .iter()
                                    .any(|candidate_super| {
                                        disj.get(candidate_super).is_some_and(|partners| {
                                            st.sub_super[node as usize].iter().any(|present| {
                                                partners.contains(present)
                                                    || base.sub_super[*present as usize]
                                                        .iter()
                                                        .any(|present_super| {
                                                            partners.contains(present_super)
                                                        })
                                            })
                                        })
                                    });
                                directly_clashing
                                    && !repair_exhausted_choice_instances(
                                        banned,
                                        std::slice::from_ref(&triple),
                                        rcs,
                                    )
                                    .contains(&(triple.0, triple.1))
                            })
                            .collect();
                        if let Some(&direct) = direct_dead_choices.first() {
                            direct_dead_conflict = true;
                            direct_dead_clauses
                                .extend(direct_dead_choices.iter().map(|triple| triple.1));
                            causal.clear();
                            causal_seen.clear();
                            // A large unravelled model can expose several
                            // independently bad universal-cover sides in the
                            // same closed state. Group direct clashes by clause
                            // side and learn every cohort represented at least
                            // `GLOBAL_SIDE_LEARN` times. Without this batching,
                            // conflict-directed repair rediscovers one cohort
                            // per full closure. These remain soft bans and the
                            // complete fallback/final checks are unchanged.
                            let mut cohort_counts: HashMap<(usize, u32), usize> =
                                HashMap::default();
                            for &(_, clause, concept) in &direct_dead_choices {
                                *cohort_counts.entry((clause, concept)).or_default() += 1;
                            }
                            let cohort_sides: HashSet<(usize, u32)> =
                                if global_side_threshold == 0 {
                                    HashSet::default()
                                } else {
                                    cohort_counts
                                        .into_iter()
                                        .filter_map(|(side, count)| {
                                            (count >= global_side_threshold).then_some(side)
                                        })
                                        .collect()
                                };
                            if debug && !cohort_sides.is_empty() {
                                eprintln!(
                                    "KM_ELC_CERT repair pass {pass_label}: batching {} repeated direct-clash side cohort(s)",
                                    cohort_sides.len(),
                                );
                            }
                            // Learn this exact side at every already-dead
                            // instance visible in the closed pass. Future
                            // witnesses remain untouched until their own
                            // conflict is observed; this conservative schedule
                            // avoids destabilising a zero-residual assignment.
                            for &candidate in &direct_dead_choices {
                                if !cohort_sides.is_empty()
                                    && !cohort_sides.contains(&(candidate.1, candidate.2))
                                {
                                    continue;
                                }
                                if cohort_sides.is_empty()
                                    && (candidate.1 != direct.1 || candidate.2 != direct.2)
                                {
                                    continue;
                                }
                                if repair_exhausted_choice_instances(
                                    banned,
                                    std::slice::from_ref(&candidate),
                                    rcs,
                                )
                                .contains(&(candidate.0, candidate.1))
                                {
                                    continue;
                                }
                                let node = uf_find(&mut repr, candidate.0);
                                if st.sub_super[node as usize].contains(&BOTTOM)
                                    && causal_seen.insert(candidate)
                                {
                                    causal.push(candidate);
                                }
                            }
                            if causal.is_empty() {
                                causal.push(direct);
                                causal_seen.insert(direct);
                            }
                        }
                        if causal.is_empty() {
                            let mut trace_seen = HashSet::default();
                            let mut upstream = trace_repair_choice(
                                c,
                                BOTTOM,
                                &st,
                                nfs,
                                &repair_trace,
                                it,
                                &mut repr,
                                &prov,
                                banned,
                                &mut trace_seen,
                                96,
                            );
                            if upstream.is_none() {
                                // A resumed frontier can mark every choice on
                                // the real bottom derivation as exhausted. The
                                // ordinary trace then correctly finds no
                                // *untried* cause, but falling straight through
                                // to the global sentinel walk loses the proof
                                // path and scans the whole carrier. Reconstruct
                                // the currently selected provenance without
                                // the search-preference filter and let
                                // `apply_conflicts` reopen its siblings. This
                                // only chooses the next branch: closure and the
                                // complete residual/root checks are unchanged.
                                trace_seen.clear();
                                upstream = trace_repair_choice(
                                    c,
                                    BOTTOM,
                                    &st,
                                    nfs,
                                    &repair_trace,
                                    it,
                                    &mut repr,
                                    &prov,
                                    &HashSet::default(),
                                    &mut trace_seen,
                                    96,
                                );
                                // This is the selected choice on the actual
                                // bottom proof, recovered after every choice
                                // on that proof had already been marked tried.
                                // Pass it straight to chronological reopening.
                                // Treating it as an ordinary exhausted
                                // candidate below discards the proof path and
                                // enters the ontology-wide sentinel cursor.
                                proof_path_reopen = upstream.is_some();
                            }
                            if let Some(upstream) = upstream {
                                // Whether the proof trace found a new side or
                                // recovered a selected exhausted side, this is
                                // an exact cause on the protected root's
                                // bottom derivation. Do not replace it with
                                // the generic global exhausted-instance
                                // cursor below. The bounded same-clause
                                // expansion may still add sibling instances.
                                proof_path_reopen = true;
                                causal.push(upstream);
                            }
                        }
                        // Preserve the clauses reached by proof tracing before
                        // the root-cardinality portfolio broadens `causal` with
                        // every selected partition at the root. Only these
                        // directly implicated clauses should advance to a
                        // node-mixed assignment in this restart; mixing every
                        // root partition at once creates a much larger closure.
                        let directly_traced_clauses: HashSet<usize> =
                            causal.iter().map(|triple| triple.1).collect();
                        if bulk_root_card_conflicts
                            && !direct_dead_conflict
                            && !proof_path_reopen
                        {
                            // Routed search option for terminology roots with
                            // many independent cardinality partitions. Once a
                            // closed pass kills the protected root, flip every
                            // currently selected low-cardinality side at that
                            // root together instead of paying one full closure
                            // per partition. This is choice scheduling only:
                            // opposite sides are selected on restart and the
                            // resulting model still receives the complete
                            // residual check.
                            let root = uf_find(&mut repr, c);
                            for &triple in chrono.iter().rev() {
                                if !repair_choice_untried(banned, triple)
                                    || uf_find(&mut repr, triple.0) != root
                                    || !guide.by_guard.contains_key(&triple.2)
                                {
                                    continue;
                                }
                                if causal_seen.insert(triple) {
                                    causal.push(triple);
                                }
                            }
                        }
                        if bulk_causal_clause_conflicts
                            && (!eager_causal_mix || eager_continuation)
                            && !causal.is_empty()
                            && !direct_dead_conflict
                        {
                            // Portfolio schedule for a universal partition
                            // whose independently instantiated choices produce
                            // the same rooted clash. Flip all currently chosen
                            // instances of each causal clause in one restart.
                            // This does not assert or discharge anything; a
                            // candidate model still passes the exhaustive
                            // residual checker. The ordinary route remains the
                            // mixed-assignment fallback if this coarse schedule
                            // cannot produce a model.
                            let clauses: HashSet<usize> =
                                causal.iter().map(|triple| triple.1).collect();
                            let mut mixed_per_clause: HashMap<usize, usize> = HashMap::default();
                            for &triple in chrono.iter().rev() {
                                if !clauses.contains(&triple.1) {
                                    continue;
                                }
                                // A covering partition whose alternatives are
                                // all concepts of the same variable otherwise
                                // spends another closure selecting its opposite
                                // side uniformly. Advance only a bounded number
                                // of its instances to node-mixed search in each
                                // restart: mixing an ontology-wide partition at
                                // every node at once can make the next closure
                                // needlessly large. These remain soft search
                                // bans; model acceptance is still decided by the
                                // complete residual check.
                                let rc = &rcs[triple.1];
                                let selected_var = rc.head.iter().find_map(|atom| match *atom {
                                    RAtom::C { cid, v } if cid == triple.2 => Some(v),
                                    _ => None,
                                });
                                let same_var_partition = directly_traced_clauses
                                    .contains(&triple.1)
                                    && selected_var.is_some_and(|v| {
                                        rc.head.iter().all(
                                        |atom| matches!(*atom, RAtom::C { v: av, .. } if av == v),
                                        )
                                    });
                                if same_var_partition {
                                    // `u32::MAX` is a checkpoint-only sentinel:
                                    // this instance was already included in an
                                    // earlier bounded mixed window. It is never
                                    // a concept id, so it cannot affect choice
                                    // lookup or model checking.
                                    if banned.contains(&(triple.0, triple.1, u32::MAX)) {
                                        continue;
                                    }
                                    let fully_tried = rc.head.iter().all(|atom| {
                                        let RAtom::C { cid, .. } = *atom else {
                                            unreachable!()
                                        };
                                        banned.contains(&(triple.0, triple.1, cid))
                                    });
                                    let mixed = mixed_per_clause.entry(triple.1).or_default();
                                    if fully_tried || *mixed >= causal_mix_batch {
                                        continue;
                                    }
                                    *mixed += 1;
                                    for atom in &rc.head {
                                        let RAtom::C { cid, .. } = *atom else {
                                            unreachable!()
                                        };
                                        let alternative = (triple.0, triple.1, cid);
                                        if !banned.contains(&alternative)
                                            && causal_seen.insert(alternative)
                                        {
                                            causal.push(alternative);
                                        }
                                    }
                                } else if !banned.contains(&triple)
                                    && causal_seen.insert(triple)
                                {
                                    causal.push(triple);
                                }
                            }
                        }
                        if bulk_causal_node_conflicts && !causal.is_empty() {
                            // A protected-root explanation can identify one
                            // fresh node whose current universal-partition
                            // assignment kills the same existential witness.
                            // Trying the other selected covers at that node
                            // one closure at a time repeats an otherwise
                            // identical large model. Advance the whole local
                            // assignment together. These are still soft bans:
                            // exhausted alternatives fall through to the
                            // ordinary mixed chooser, and publication still
                            // requires the complete residual and root-survival
                            // checks below.
                            let causal_nodes: HashSet<u32> = causal
                                .iter()
                                .map(|&(node, _, _)| uf_find(&mut repr, node))
                                .collect();
                            let mut added_per_node: HashMap<u32, usize> = HashMap::default();
                            for &triple in chrono.iter().rev() {
                                let node = uf_find(&mut repr, triple.0);
                                let rc = &rcs[triple.1];
                                let first_var = rc.head.first().and_then(|atom| match *atom {
                                    RAtom::C { v, .. } => Some(v),
                                    _ => None,
                                });
                                let same_var_universal_cover = rc.head.len() > 1
                                    && (rc.body.is_empty()
                                        || rc.body.iter().all(|atom| {
                                            matches!(atom, RAtom::C { cid, .. } if *cid == TOP)
                                        }))
                                    && first_var.is_some_and(|v| {
                                        rc.head.iter().all(
                                            |atom| matches!(*atom, RAtom::C { v: av, .. } if av == v),
                                        )
                                    });
                                if !causal_nodes.contains(&node)
                                    || !repair_choice_untried(banned, triple)
                                    || !same_var_universal_cover
                                {
                                    continue;
                                }
                                let added = added_per_node.entry(node).or_default();
                                if *added >= causal_mix_batch {
                                    continue;
                                }
                                if causal_seen.insert(triple) {
                                    causal.push(triple);
                                    *added += 1;
                                }
                            }
                        }
                        if !causal.is_empty() {
                            // Prefer all reconstructed causal source paths over
                            // merely recent choices at the same root.
                            blame.clear();
                            blame.extend(causal);
                            explained.clear();
                            for &(node, _, _) in &blame {
                                explained.insert(uf_find(&mut repr, node));
                            }
                        }
                    }
                    for &triple in chrono.iter().rev() {
                        if !repair_choice_untried(banned, triple) {
                            continue;
                        }
                        let nd = uf_find(&mut repr, triple.0);
                        if dead_reps.contains(&nd) && explained.insert(nd) && seen.insert(triple) {
                            blame.push(triple);
                        }
                    }
                    if blame.is_empty() {
                        let cr = uf_find(&mut repr, c);
                        if let Some(triple) = chrono
                            .iter()
                            .rev()
                            .find(|&&t| {
                                uf_find(&mut repr, t.0) == cr
                                    && repair_choice_untried(banned, t)
                            })
                            .copied()
                            .or_else(|| {
                                chrono
                                    .iter()
                                    .rev()
                                    .find(|&&t| repair_choice_untried(banned, t))
                                    .copied()
                            })
                        {
                            blame.push(triple);
                        } else {
                            // Every local side can already be soft-banned in
                            // a resumed frontier. Reusing and reopening that
                            // same exhausted partition merely cycles through
                            // its finite alternatives. Backjump to the most
                            // recent different choice instance instead; if no
                            // such instance exists, retain the local fallback.
                            let exhausted_local = chrono
                                .iter()
                                .rev()
                                .find(|&&t| uf_find(&mut repr, t.0) == cr)
                                .copied();
                            let backjump = exhausted_local
                                .and_then(|local| {
                                    chrono.iter().rev().find(|&&triple| {
                                        (triple.0, triple.1) != (local.0, local.1)
                                    })
                                })
                                .copied()
                                .or(exhausted_local)
                                .or_else(|| chrono.last().copied());
                            if let Some(triple) = backjump {
                                blame.push(triple);
                            }
                        }
                    }
                    if rooted_domain {
                        // Count clauses observed in direct clashes as well as
                        // clauses retained by proof-neighbour blame. Fresh
                        // witness redirection can change the node identifier
                        // on every attempt; in that case proof tracing may
                        // backjump to an older upstream choice and otherwise
                        // miss a partition whose every side closes the same
                        // witness. Clause-level recurrence is independent of
                        // that unstable node identity and lets the existing
                        // fallback move above the exhausted partition.
                        let mut blamed_clauses: HashSet<usize> =
                            blame.iter().map(|triple| triple.1).collect();
                        blamed_clauses.extend(direct_dead_clauses.iter().copied());
                        recurrence_counted_clauses.extend(blamed_clauses.iter().copied());
                        for clause in blamed_clauses {
                            let count = rooted_clause_conflict_counts.entry(clause).or_default();
                            if *count == 0
                                && banned.iter().any(|&(_, prior_clause, concept)| {
                                    prior_clause == clause && concept != u32::MAX
                                })
                            {
                                *count = 1;
                            }
                            *count += 1;
                            if *count >= 2
                                && rooted_exhausted_backjump_clauses.insert(clause)
                                && debug
                            {
                                eprintln!(
                                    "KM_ELC_CERT repair pass {pass_label}: causal clause {clause} recurred; backjumping past it"
                                );
                            }
                        }
                    }
                    if rooted_domain && !rooted_exhausted_backjump_clauses.is_empty() {
                        let before = blame.len();
                        blame.retain(|&(_, clause, _)| {
                            !rooted_exhausted_backjump_clauses.contains(&clause)
                        });
                        if debug && blame.len() != before {
                            eprintln!(
                                "KM_ELC_CERT repair pass {pass_label}: omitted {} choice(s) \
                                 from exhausted proof clause(s)",
                                before - blame.len(),
                            );
                        }
                        if blame.is_empty() {
                            let predecessor = chrono
                                .iter()
                                .rev()
                                .find(|&&choice| {
                                    !rooted_exhausted_backjump_clauses.contains(&choice.1)
                                        && repair_choice_untried(banned, choice)
                                })
                                .or_else(|| {
                                    chrono.iter().rev().find(|&&choice| {
                                        !rooted_exhausted_backjump_clauses.contains(&choice.1)
                                    })
                                })
                                .copied();
                            let from_checkpoint = predecessor.is_none();
                            let checkpoint_predecessor = predecessor.or_else(|| {
                                let mut sentinels: Vec<(u32, usize)> = banned
                                    .iter()
                                    .filter_map(|&(node, clause, cid)| {
                                        (cid == u32::MAX
                                            && (node as usize) < st.sub_super.len()
                                            && !rooted_exhausted_backjump_clauses
                                                .contains(&clause))
                                        .then_some((node, clause))
                                    })
                                    .collect();
                                sentinels.sort_unstable();
                                let sentinel_choice = sentinels.into_iter().find_map(|(node, clause)| {
                                    let alternatives: Vec<u32> = rcs
                                        .get(clause)?
                                        .head
                                        .iter()
                                        .filter_map(|atom| match *atom {
                                            RAtom::C { cid, .. } => Some(cid),
                                            _ => None,
                                        })
                                        .collect();
                                    if alternatives.is_empty() {
                                        return None;
                                    }
                                    let pick = repair_choice_mix(node, clause, pass_label)
                                        % alternatives.len();
                                    Some((node, clause, alternatives[pick]))
                                });
                                sentinel_choice.or_else(|| {
                                    // Older compact checkpoints may retain
                                    // failed sides without a sentinel for the
                                    // same causal clause. Use one such valid
                                    // instance only after the sentinel cursor
                                    // is empty, preferring an untried sibling.
                                    let mut regular: Vec<(u32, usize)> = banned
                                        .iter()
                                        .filter_map(|&(node, clause, cid)| {
                                            (cid != u32::MAX
                                                && (node as usize) < st.sub_super.len()
                                                && !rooted_exhausted_backjump_clauses
                                                    .contains(&clause))
                                            .then_some((node, clause))
                                        })
                                        .collect();
                                    regular.sort_unstable();
                                    regular.dedup();
                                    regular.into_iter().find_map(|(node, clause)| {
                                        let alternatives: Vec<u32> = rcs
                                            .get(clause)?
                                            .head
                                            .iter()
                                            .filter_map(|atom| match *atom {
                                                RAtom::C { cid, .. } => Some(cid),
                                                _ => None,
                                            })
                                            .collect();
                                        let chosen = alternatives
                                            .iter()
                                            .copied()
                                            .find(|&cid| !banned.contains(&(node, clause, cid)))
                                            .or_else(|| {
                                                (!alternatives.is_empty()).then(|| {
                                                    let pick = repair_choice_mix(
                                                        node,
                                                        clause,
                                                        pass_label,
                                                    ) % alternatives.len();
                                                    alternatives[pick]
                                                })
                                            })?;
                                        Some((node, clause, chosen))
                                    })
                                })
                            });
                            if let Some(predecessor) = checkpoint_predecessor {
                                if from_checkpoint {
                                    // A sentinel records that every side of
                                    // this local cover was already tried. One
                                    // explicit recheck is enough to reconnect
                                    // the resumed proof path; do not then scan
                                    // the same exhausted clause at every other
                                    // ontology node.
                                    rooted_exhausted_backjump_clauses.insert(predecessor.1);
                                }
                                if debug && from_checkpoint {
                                    eprintln!(
                                        "KM_ELC_CERT repair pass {pass_label}: checkpoint \
                                         proof-neighbor backjump {:?}",
                                        predecessor,
                                    );
                                }
                                blame.push(predecessor);
                            }
                        }
                    }
                    let mut exhausted = if direct_dead_conflict || proof_path_reopen {
                        HashSet::default()
                    } else {
                        repair_exhausted_choice_instances(banned, &blame, rcs)
                    };
                    if debug && !blame.is_empty() {
                        let instances: Vec<String> = blame
                            .iter()
                            .map(|&(node, clause, cid)| {
                                format!(
                                    "({node},{clause},{cid};banned={})",
                                    banned.contains(&(node, clause, cid))
                                )
                            })
                            .collect();
                        eprintln!(
                            "KM_ELC_CERT repair pass {pass_label}: exhaustion probe [{}] -> {:?}",
                            instances.join(","),
                            exhausted,
                        );
                    }
                    if rooted_domain && !exhausted.is_empty() {
                        // The final side of a directly clashing partition can
                        // make that local instance fully tried. Reopening it
                        // toggles; treating it as a generic exhausted frontier
                        // enters the ontology-wide cursor. Remove that local
                        // provenance from the reconstructed proof and ask for
                        // the nearest upstream decision instead. This changes
                        // only chronological search order; the replacement
                        // assignment still undergoes complete closure,
                        // residual checking, and protected-root checking.
                        let exhausted_reps: HashSet<(u32, usize)> = exhausted
                            .iter()
                            .map(|&(node, clause)| (uf_find(&mut repr, node), clause))
                            .collect();
                        let mut upstream_prov = prov.clone();
                        upstream_prov.retain(|&(node, _), clause| {
                            let node = uf_find(&mut repr, node);
                            !exhausted_reps.contains(&(node, *clause))
                        });
                        let mut trace_seen = HashSet::default();
                        if let Some(upstream) = trace_repair_choice(
                            c,
                            BOTTOM,
                            &st,
                            nfs,
                            &repair_trace,
                            it,
                            &mut repr,
                            &upstream_prov,
                            &HashSet::default(),
                            &mut trace_seen,
                            96,
                        ) {
                            if debug {
                                eprintln!(
                                    "KM_ELC_CERT repair pass {pass_label}: proof backjump \
                                     {:?} after exhausting {:?}",
                                    upstream, exhausted_reps,
                                );
                            }
                            blame.clear();
                            blame.push(upstream);
                            exhausted.clear();
                        }
                    }
                    if !exhausted.is_empty() {
                        let local_exhausted = exhausted.clone();
                        if rooted_domain {
                            rooted_exhausted_backjump_clauses
                                .extend(local_exhausted.iter().map(|&(_, clause)| clause));
                        }
                        let mut persist_exhausted = exhausted.clone();
                        let mut previous = None;
                        let mut global_reopen = Vec::new();
                        for &candidate in chrono.iter().rev() {
                            if exhausted.contains(&(candidate.0, candidate.1)) {
                                continue;
                            }
                            if rooted_domain
                                && rooted_exhausted_backjump_clauses.contains(&candidate.1)
                            {
                                continue;
                            }
                            let newly_exhausted = repair_exhausted_choice_instances(
                                banned,
                                std::slice::from_ref(&candidate),
                                rcs,
                            );
                            if newly_exhausted.is_empty() {
                                previous = Some(candidate);
                                break;
                            }
                            persist_exhausted.extend(
                                newly_exhausted.iter().copied().filter(|&(node, clause)| {
                                    !banned.contains(&(node, clause, u32::MAX))
                                }),
                            );
                            if rooted_domain {
                                rooted_exhausted_backjump_clauses
                                    .extend(newly_exhausted.iter().map(|&(_, clause)| clause));
                            }
                            exhausted.extend(newly_exhausted);
                        }
                        if previous.is_none() && rooted_domain {
                            // If proof reconstruction cannot cross a fully
                            // tried local partition, reopen the nearest
                            // different chronological choice as one exact
                            // backjump. The former global fallback selected a
                            // window of nodes and every cover at each node
                            // (216 choices at Uberon's zero-residual boundary),
                            // losing causal locality. An exhausted soft choice
                            // is safe to revisit: `apply_conflicts` reopens its
                            // siblings, and the resulting model still passes
                            // every acceptance check.
                            previous = chrono
                                .iter()
                                .rev()
                                .find(|&&(node, clause, _)| {
                                    !local_exhausted.contains(&(node, clause))
                                        && !rooted_exhausted_backjump_clauses.contains(&clause)
                                })
                                .copied();
                            if let Some(previous) = previous {
                                persist_exhausted.clear();
                                if debug {
                                    eprintln!(
                                        "KM_ELC_CERT repair pass {pass_label}: chronological \
                                         proof-neighbor backjump {:?}",
                                        previous,
                                    );
                                }
                            }
                        }
                        if previous.is_none() {
                            // A compact resumed frontier can consist entirely
                            // of sentinels, so this pass has no open
                            // chronological predecessor. Reopen a different
                            // exhausted instances globally. Reopen all concept
                            // covers for a bounded window of nodes and keep one
                            // side of each failed; their siblings become the
                            // next assignment. This remains a search
                            // preference, never a model-acceptance shortcut.
                            let mut global: Vec<(u32, usize, Vec<u32>)> = banned
                                .iter()
                                .filter(|&&(node, clause, cid)| {
                                    cid == u32::MAX
                                        && !persist_exhausted.contains(&(node, clause))
                                })
                                .filter_map(|&(node, clause, _)| {
                                    let rc = rcs.get(clause)?;
                                    let alternatives: Vec<u32> = rc
                                        .head
                                        .iter()
                                        .filter_map(|atom| match *atom {
                                            RAtom::C { cid, .. } => Some(cid),
                                            _ => None,
                                        })
                                        .collect();
                                    (!alternatives.is_empty())
                                        .then_some((node, clause, alternatives))
                                })
                                .collect();
                            global.sort_unstable_by_key(|(node, clause, _)| (*node, *clause));
                            let pivot = persist_exhausted.iter().copied().max();
                            let selected = pivot
                                .and_then(|pivot| {
                                    global.iter().position(|(node, clause, _)| {
                                        (*node, *clause) > pivot
                                    })
                                })
                                .unwrap_or(0);
                            // This is the least informed fallback: neither
                            // proof reconstruction nor live chronology found
                            // a predecessor. Reopen one deterministic cover,
                            // not every cover at its node. The latter injected
                            // 146--216 unrelated choices into Uberon's
                            // chronology and obscured the causal path again.
                            // Repeated restarts still enumerate the finite
                            // cursor, while each accepted candidate receives
                            // the unchanged complete validation below.
                            global_reopen = global.get(selected).map_or_else(Vec::new, |entry| {
                                let (node, clause, alternatives) = entry;
                                let pick = repair_choice_mix(*node, *clause, pass_label)
                                    % alternatives.len();
                                vec![(*node, *clause, alternatives[pick])]
                            });
                            previous = global_reopen.first().copied();
                        }
                        if let Some(previous) = previous {
                            blame.clear();
                            if global_reopen.is_empty() {
                                blame.push(previous);
                            } else {
                                blame.extend(global_reopen);
                            }
                            // Persist every skipped finite instance as a
                            // complete frontier.  The explicit sentinel keeps
                            // the sliding clause window from deleting these
                            // alternatives when a later node of the same
                            // partition is explored.
                            for &(node, clause) in &persist_exhausted {
                                if let Some(rc) = rcs.get(clause) {
                                    for atom in &rc.head {
                                        if let RAtom::C { cid, .. } = *atom {
                                            blame.push((node, clause, cid));
                                        }
                                    }
                                }
                                blame.push((node, clause, u32::MAX));
                            }
                        }
                    }
                    if blame.is_empty() {
                        if debug {
                            eprintln!(
                                "KM_ELC_CERT repair pass {pass_label}: witness {c} died \
                                 with no choices made (genuinely unsatisfiable?)"
                            );
                        }
                        return PassOut::Fail;
                    }
                    if rooted_domain {
                        // Exhaustion/backjump processing above can replace the
                        // proof-derived blame with the concrete choice that is
                        // finally going to be banned. Count that final clause
                        // too. In particular, an indirect four-way cover can
                        // repeatedly kill freshly renamed witnesses while the
                        // proof trace keeps pointing at an older predecessor.
                        // Counting only the pre-backjump blame then misses the
                        // actual cycle. Do not double-count clauses already
                        // charged earlier in this same failed closure.
                        let final_clauses: HashSet<usize> =
                            blame.iter().map(|triple| triple.1).collect();
                        for clause in final_clauses
                            .difference(&recurrence_counted_clauses)
                            .copied()
                        {
                            let count = rooted_clause_conflict_counts.entry(clause).or_default();
                            // A resumed exact-side ban is evidence that this
                            // causal partition already failed in an earlier
                            // process. Recover that one bit of recurrence from
                            // the existing checkpoint so process boundaries do
                            // not force another pair of full Uberon closures.
                            // We only consult it after the clause has again
                            // become the final cause in the current closure.
                            if *count == 0
                                && banned.iter().any(|&(_, prior_clause, concept)| {
                                    prior_clause == clause && concept != u32::MAX
                                })
                            {
                                *count = 1;
                            }
                            *count += 1;
                            if *count >= 2
                                && rooted_exhausted_backjump_clauses.insert(clause)
                                && debug
                            {
                                eprintln!(
                                    "KM_ELC_CERT repair pass {pass_label}: final causal clause \
                                     {clause} recurred; backjumping past it"
                                );
                            }
                        }
                        if final_clauses
                            .iter()
                            .any(|clause| rooted_exhausted_backjump_clauses.contains(clause))
                        {
                            blame.retain(|&(_, clause, _)| {
                                !rooted_exhausted_backjump_clauses.contains(&clause)
                            });
                            if blame.is_empty() {
                                if let Some(previous) = chrono.iter().rev().find(|&&choice| {
                                    repair_choice_untried(banned, choice)
                                        && !rooted_exhausted_backjump_clauses
                                            .contains(&choice.1)
                                }) {
                                    blame.push(*previous);
                                }
                            }
                        }
                    }
                    if blame.is_empty() {
                        if debug {
                            eprintln!(
                                "KM_ELC_CERT repair pass {pass_label}: recurrent final clause \
                                 had no earlier choice to backjump to"
                            );
                        }
                        return PassOut::Fail;
                    }
                    if debug {
                        let first = blame[0];
                        eprintln!(
                            "KM_ELC_CERT repair pass {pass_label}: witness {c} died, \
                             batching {} choice ban(s); first={:?} (node={}, concept={}); \
                             choice_clause={}",
                            blame.len(),
                            first,
                            it.debug_name(first.0),
                            it.name(first.2),
                            describe_residual_clause(&rcs[first.1], it),
                        );
                        if rooted_domain {
                            for &(node0, rci, chosen) in &blame {
                                if chosen == u32::MAX {
                                    continue;
                                }
                                let node = uf_find(&mut repr, node0);
                                let partners = disj
                                    .get(&chosen)
                                    .into_iter()
                                    .flatten()
                                    .filter(|&&partner| {
                                        st.sub_super[node as usize].contains(&partner)
                                    })
                                    .map(|&partner| {
                                        format!(
                                            "{}(choice={:?})",
                                            it.name(partner),
                                            prov.get(&(node, partner)),
                                        )
                                    })
                                    .collect::<Vec<_>>();
                                eprintln!(
                                    "KM_ELC_CERT rooted conflict detail: node={} choice={} \
                                     clause={} disjoint_present=[{}]",
                                    it.debug_name(node),
                                    it.name(chosen),
                                    rci,
                                    partners.join(","),
                                );
                            }
                            let root = uf_find(&mut repr, c);
                            if let Some(nf) = nfs.nf2.iter().find(|nf| {
                                nf.sup == BOTTOM
                                    && st.sub_super[root as usize].contains(&nf.sub1)
                                    && st.sub_super[root as usize].contains(&nf.sub2)
                            }) {
                                eprintln!(
                                    "KM_ELC_CERT rooted bottom detail: NF2 {} & {} -> bottom; \
                                     choices={:?},{:?}",
                                    it.name(nf.sub1),
                                    it.name(nf.sub2),
                                    prov.get(&(root, nf.sub1)),
                                    prov.get(&(root, nf.sub2)),
                                );
                            }
                            for &sub in nfs
                                .nf5
                                .iter()
                                .filter(|&&sub| st.sub_super[root as usize].contains(&sub))
                                .take(4)
                            {
                                eprintln!(
                                    "KM_ELC_CERT rooted bottom detail: NF5 {} -> bottom; choice={:?}",
                                    it.name(sub),
                                    prov.get(&(root, sub)),
                                );
                            }
                            if std::env::var_os("KM_ELC_DEBUG_DERIVATION").is_some() {
                                let mut root_derivation_seen = HashSet::default();
                                let mut root_derivation_lines = 0usize;
                                debug_el_membership_producers(
                                    root,
                                    BOTTOM,
                                    &st,
                                    nfs,
                                    it,
                                    &prov,
                                    &mut root_derivation_seen,
                                    8,
                                    &mut root_derivation_lines,
                                );
                                if let Some(q36024) = it.id("Q_36024") {
                                    if st.sub_super[root as usize].contains(&q36024) {
                                        eprintln!(
                                            "KM_ELC_CERT rooted diagnostic: tracing Q_36024 \
                                             complement-side taxon witness"
                                        );
                                        let mut branch_seen = HashSet::default();
                                        let mut branch_lines = 0usize;
                                        debug_el_membership_producers(
                                            root,
                                            q36024,
                                            &st,
                                            nfs,
                                            it,
                                            &prov,
                                            &mut branch_seen,
                                            8,
                                            &mut branch_lines,
                                        );
                                    }
                                }
                            }
                            if let Some(&(role, target)) =
                                st.edges[root as usize].iter().find(|(_, target)| {
                                    st.sub_super[*target as usize].contains(&BOTTOM)
                                })
                            {
                                eprintln!(
                                    "KM_ELC_CERT rooted bottom detail: dead successor -{}->{}",
                                    it.name(role),
                                    it.debug_name(target),
                                );
                                if let Some(&(source, generated_role, filler)) =
                                    fresh_inverse.origins.get(&target)
                                {
                                    if std::env::var_os("KM_ELC_DEBUG_DERIVATION").is_some() {
                                        let mut extra: Vec<u32> = st.sub_super[target as usize]
                                            .iter()
                                            .copied()
                                            .filter(|concept| {
                                                !base.sub_super[filler as usize].contains(concept)
                                            })
                                            .collect();
                                        extra.sort_unstable();
                                        eprintln!(
                                            "KM_ELC_CERT rooted fresh origin: {} -{}-> {} as {}; \
                                             canonical_bottom={} fresh_only_labels={} [{}]",
                                            it.debug_name(source),
                                            it.name(generated_role),
                                            it.debug_name(target),
                                            it.name(filler),
                                            base.sub_super[filler as usize].contains(&BOTTOM),
                                            extra.len(),
                                            extra
                                                .iter()
                                                .take(24)
                                                .map(|&concept| it.name(concept))
                                                .collect::<Vec<_>>()
                                                .join(","),
                                        );
                                    } else {
                                        eprintln!(
                                            "KM_ELC_CERT rooted fresh origin: {} -{}-> {} as {}",
                                            it.debug_name(source),
                                            it.name(generated_role),
                                            it.debug_name(target),
                                            it.name(filler),
                                        );
                                    }
                                }
                                for nf in nfs.nf3.iter().filter(|nf| {
                                    st.sub_super[root as usize].contains(&nf.sub)
                                        && st.sub_super[target as usize].contains(&nf.filler)
                                        && (nf.role == role
                                            || idx.role_supers(nf.role).contains(&role))
                                }) {
                                    eprintln!(
                                        "KM_ELC_CERT rooted bottom producer: {} -> exists {}.{} \
                                         (observed as {})",
                                        it.name(nf.sub),
                                        it.name(nf.role),
                                        it.name(nf.filler),
                                        it.name(role),
                                    );
                                }
                                if let Some(nf) = nfs.nf2.iter().find(|nf| {
                                    nf.sup == BOTTOM
                                        && st.sub_super[target as usize].contains(&nf.sub1)
                                        && st.sub_super[target as usize].contains(&nf.sub2)
                                }) {
                                    eprintln!(
                                        "KM_ELC_CERT rooted bottom detail: target NF2 {} & {} -> \
                                         bottom; choices={:?},{:?}",
                                        it.name(nf.sub1),
                                        it.name(nf.sub2),
                                        prov.get(&(target, nf.sub1)),
                                        prov.get(&(target, nf.sub2)),
                                    );
                                }
                                if std::env::var_os("KM_ELC_DEBUG_DERIVATION").is_some() {
                                    let mut derivation_seen = HashSet::default();
                                    let mut derivation_lines = 0usize;
                                    debug_el_membership_producers(
                                        target,
                                        BOTTOM,
                                        &st,
                                        nfs,
                                        it,
                                        &prov,
                                        &mut derivation_seen,
                                        5,
                                        &mut derivation_lines,
                                    );
                                    let mut target_trace_seen = HashSet::default();
                                    let target_choice = trace_repair_choice(
                                        target,
                                        BOTTOM,
                                        &st,
                                        nfs,
                                        &repair_trace,
                                        it,
                                        &mut repr,
                                        &prov,
                                        banned,
                                        &mut target_trace_seen,
                                        128,
                                    );
                                    eprintln!(
                                        "KM_ELC_CERT target causal choice: {:?}",
                                        target_choice.map(|(node, clause, chosen)| (
                                            it.debug_name(node),
                                            clause,
                                            it.name(chosen),
                                        )),
                                    );
                                }
                            }
                        }
                    }
                    return PassOut::Conflict(blame, Some(viols.len()));
                }
            }
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
        }
        if debug {
            eprintln!(
                "KM_ELC_CERT repair pass {pass_label}: no convergence in {max_rounds} rounds"
            );
        }
        PassOut::Fail
    };

    // Check the unchanged EL structure before cloning it for a repair pass.
    // A clean full round is exactly the `Pristine` result that the first pass
    // would return after `State::fork`. If it is not clean, hand the complete
    // enumeration index to the first fork; refreshing it with that fork's
    // empty journal produces the same index as rebuilding it from scratch.
    let mut base_idx = CertIdx::default();
    if lazy_complements.is_empty() {
        let mut budget: u64 = std::env::var("KM_ELC_REPAIR_BUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(PASS_BUDGET);
        let clean = cert_round(
            rcs,
            &repair_concept_names,
            &base.sub_super,
            &base.edges,
            None,
            &mut budget,
            None,
            false,
            Some(CertReuse {
                idx: &mut base_idx,
                delta: None,
                edge_epoch: base.edge_epoch,
            }),
            None,
            None,
        );
        if clean {
            if debug {
                eprintln!("KM_ELC_CERT repair: base model already complete");
            }
            return if rooted_domain {
                if rooted_publish {
                    rooted_unverified()
                } else {
                    CertOutcome::Fail
                }
            } else {
                CertOutcome::Pass
            };
        }
    }
    let mut base_idx = Some(base_idx);

    const RESTART_CAP: usize = REPAIR_RESTART_CAP;
    let mut pass_states: Vec<(State, HashMap<(u32, u32), usize>)> = Vec::new();
    let polv0 = vec![false; rcs.len()];
    let mut banned0: HashSet<(u32, usize, u32)> = HashSet::default();
    let model_passes: usize = std::env::var("KM_ELC_MODEL_PASSES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(2)
        // One complete countermodel is sufficient for a single rooted row
        // when its named label equals the EL lower bound. Whole-taxonomy
        // repair retains the two-polarity minimum.
        .clamp(if rooted_domain { 1 } else { 2 }, 8);
    // Resumed rooted searches must be able to sample assignments beyond the
    // original eight-pass portfolio. The offset changes only deterministic
    // choice order; every candidate still undergoes the unchanged closure and
    // complete residual-model checks. Ordinary and non-rooted routes retain
    // offset zero.
    let model_seed_offset: usize = if rooted_domain {
        std::env::var("KM_ELC_MODEL_SEED_OFFSET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(0)
    } else {
        0
    };
    let strict_restart_limit = if bulk_causal_clause_conflicts {
        4_096
    } else {
        RESTART_CAP
    };
    let strict_restart_cap: usize = std::env::var("KM_ELC_STRICT_RESTARTS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(strict_restart_limit)
        .min(strict_restart_limit);
    let tolerant_restart_cap: usize = std::env::var("KM_ELC_TOLERANT_RESTARTS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(RESTART_CAP)
        .min(RESTART_CAP);
    // The non-eager rooted bulk-causal route deliberately exhausts whole clause
    // partitions before trying node-mixed assignments. Rebuilding that same
    // frontier for every polarity seed is duplicate search, so that route
    // carries its checkpoint between seeds. The eager portfolio instead takes
    // a common checkpoint snapshot below and keeps later conflicts seed-local.
    // Bans only influence choice order; closure and complete model checking are
    // unchanged in both schedules.
    let rooted_ban_checkpoint = if bulk_causal_clause_conflicts {
        std::env::var_os("KM_ELC_REPAIR_BAN_CHECKPOINT").map(std::path::PathBuf::from)
    } else {
        None
    };
    let checkpoint_header = format!("v1\t{n}\t{}", rcs.len());
    let mut rooted_shared_bans: HashSet<(u32, usize, u32)> = rooted_ban_checkpoint
        .as_ref()
        .and_then(|path| std::fs::read_to_string(path).ok())
        .and_then(|text| {
            let mut lines = text.lines();
            (lines.next() == Some(checkpoint_header.as_str())).then(|| {
                lines
                    .filter_map(|line| {
                        let mut fields = line.split('\t');
                        let node = fields.next()?.parse().ok()?;
                        let clause = fields.next()?.parse().ok()?;
                        let concept = fields.next()?.parse().ok()?;
                        fields.next().is_none().then_some((node, clause, concept))
                    })
                    .collect()
            })
        })
        .unwrap_or_default();
    if debug && !rooted_shared_bans.is_empty() {
        eprintln!(
            "KM_ELC_CERT repair: resumed {} rooted causal choice ban(s)",
            rooted_shared_bans.len()
        );
    }
    let write_bans = |path: &std::path::Path,
                      bans: &HashSet<(u32, usize, u32)>|
     -> std::io::Result<()> {
        let mut triples: Vec<_> = bans.iter().copied().collect();
        triples.sort_unstable();
        let mut text = String::with_capacity(32 + triples.len() * 24);
        text.push_str(&checkpoint_header);
        text.push('\n');
        for (node, clause, concept) in triples {
            use std::fmt::Write as _;
            let _ = writeln!(text, "{node}\t{clause}\t{concept}");
        }
        let tmp = path.with_extension("tmp");
        std::fs::write(&tmp, text).and_then(|()| std::fs::rename(&tmp, path))
    };
    let save_rooted_bans = |bans: &HashSet<(u32, usize, u32)>| {
        let Some(path) = &rooted_ban_checkpoint else {
            return;
        };
        let result = write_bans(path, bans);
        if debug {
            if let Err(error) = result {
                eprintln!(
                    "KM_ELC_CERT repair: could not update ban checkpoint {}: {error}",
                    path.display()
                );
            }
        }
    };
    // Eager model passes are a portfolio, not a continuation of one unary-ban
    // walk.  Every pass starts from the same previously established frontier
    // and keeps conflicts local to that pass, allowing the pass hash to vary
    // all still-uncommitted choices together.  The non-eager route continues
    // to persist and share its monotone exploration frontier between passes.
    let mut rooted_seed_base_bans = rooted_shared_bans.clone();
    if eager_causal_mix && !eager_continuation {
        // A checkpoint can end between the two alternatives of one covering
        // clause instance. Carrying that one-sided preference into every seed
        // fixes the same choice before the seeded mixer can act. Keep only
        // completed per-node covering frontiers (plus sentinels and clauses
        // that are not same-variable concept covers); seed-local repair may
        // still add a temporary one-sided preference during its own retry.
        let checkpoint = rooted_seed_base_bans.clone();
        rooted_seed_base_bans.retain(|&(node, rci, cid)| {
            if cid == u32::MAX {
                return true;
            }
            let Some(rc) = rcs.get(rci) else {
                return true;
            };
            let Some(first_var) = rc.head.first().and_then(|atom| match *atom {
                RAtom::C { v, .. } => Some(v),
                _ => None,
            }) else {
                return true;
            };
            let same_var_cover = rc.head.len() > 1
                && rc
                    .head
                    .iter()
                    .all(|atom| matches!(*atom, RAtom::C { v, .. } if v == first_var));
            !same_var_cover
                || rc.head.iter().all(|atom| {
                    let RAtom::C { cid: alternative, .. } = *atom else {
                        unreachable!()
                    };
                    checkpoint.contains(&(node, rci, alternative))
                })
        });
        if debug && rooted_seed_base_bans.len() != rooted_shared_bans.len() {
            eprintln!(
                "KM_ELC_CERT repair: eager seed base dropped {} incomplete checkpoint ban(s)",
                rooted_shared_bans.len() - rooted_seed_base_bans.len()
            );
        }
    }
    let apply_conflicts =
        |banned: &mut HashSet<(u32, usize, u32)>, triples: Vec<(u32, usize, u32)>| {
            // A large same-variable covering clause is explored through a
            // sliding mixed window. Sentinels remember nodes visited by older
            // windows, while their actual alternative bans are removed before
            // the next window. This bounds the number of simultaneous mixed
            // assignments without revisiting nodes after a restart.
            let homogeneous_causal = triples.first().is_some_and(|first| {
                triples
                    .iter()
                    .all(|triple| (triple.1, triple.2) == (first.1, first.2))
            });
            let mut window_nodes: HashMap<usize, HashSet<u32>> = HashMap::default();
            // A homogeneous set is one precise local conflict repeated at
            // several nodes, not a sliding mixed window. Preserve it when the
            // same clause later fails elsewhere; deleting older bans made two
            // Uberon witnesses alternate forever. Batches spanning alternatives
            // retain the bounded-window compaction that controls checkpoint size.
            if bulk_causal_clause_conflicts && !homogeneous_causal {
                for &(node, clause, _) in &triples {
                    let Some(rc) = rcs.get(clause) else {
                        continue;
                    };
                    let Some(first_var) = rc.head.first().and_then(|atom| match *atom {
                        RAtom::C { v, .. } => Some(v),
                        _ => None,
                    }) else {
                        continue;
                    };
                    if rc
                        .head
                        .iter()
                        .all(|atom| matches!(*atom, RAtom::C { v, .. } if v == first_var))
                    {
                        window_nodes.entry(clause).or_default().insert(node);
                    }
                }
                window_nodes.retain(|&clause, nodes| {
                    nodes.len() >= causal_mix_batch
                        || banned
                            .iter()
                            .any(|&(_, rci, cid)| rci == clause && cid == u32::MAX)
                });
                for (&clause, nodes) in &window_nodes {
                    banned.retain(|&(node, rci, cid)| {
                        rci != clause || cid == u32::MAX || nodes.contains(&node)
                    });
                }
            }
            let mut inserted = 0usize;
            for triple in triples {
                if triple.2 == u32::MAX {
                    inserted += usize::from(banned.insert(triple));
                    continue;
                }
                // Bans are search preferences, not learned logical clauses.
                // Once every side of one covering instance has been tried,
                // the ordinary tier-3 chooser may deliberately reuse a
                // banned side.  If that reused side causes the next conflict,
                // keeping all sides banned would make the conflict appear
                // non-actionable and repeat the same assignment forever.
                // Reopen the sibling sides and retain only the side that just
                // failed.  This is chronological backtracking for an
                // exhausted finite choice; the complete residual-model check
                // remains the sole acceptance criterion.
                let exhausted = rcs.get(triple.1).is_some_and(|rc| {
                    !rc.head.is_empty()
                        && rc.head.iter().all(|atom| match *atom {
                            RAtom::C { cid, .. } => {
                                banned.contains(&(triple.0, triple.1, cid))
                            }
                            _ => false,
                        })
                });
                if exhausted
                    || banned.contains(&(triple.0, triple.1, u32::MAX))
                {
                    let before = banned.len();
                    banned.retain(|&(node, clause, cid)| {
                        node != triple.0
                            || clause != triple.1
                            || (cid != u32::MAX && cid == triple.2)
                    });
                    inserted += usize::from(banned.len() != before);
                }
                inserted += usize::from(banned.insert(triple));
            }
            for (&clause, nodes) in &window_nodes {
                let rc = &rcs[clause];
                for &node in nodes {
                    let fully_tried = rc.head.iter().all(|atom| {
                        let RAtom::C { cid, .. } = *atom else {
                            unreachable!()
                        };
                        banned.contains(&(node, clause, cid))
                    });
                    if fully_tried {
                        banned.insert((node, clause, u32::MAX));
                    }
                }
            }
            inserted
        };
    let mut best_conflict_score = usize::MAX;
    for model_index in 0..model_passes {
        let seed = model_seed_offset.saturating_add(model_index);
        let polv: Vec<bool> = match seed {
            0 => vec![false; rcs.len()],
            1 => vec![true; rcs.len()],
            // Deterministic mixed polarities. Each pass remains an ordinary
            // complete residual model; diversity only strengthens the model
            // intersection by keeping more satisfiable subjects alive in at
            // least one checked model.
            _ => (0..rcs.len())
                .map(|rci| {
                    let x = (rci as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
                        ^ (seed as u64).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                    (x ^ (x >> 29) ^ (x >> 47)) & 1 != 0
                })
                .collect(),
        };
        let mut banned: HashSet<(u32, usize, u32)> = if bulk_causal_clause_conflicts {
            if eager_causal_mix && !eager_continuation {
                rooted_seed_base_bans.clone()
            } else {
                rooted_shared_bans.clone()
            }
        } else {
            HashSet::default()
        };
        let mut restarts = 0usize;
        let mut bulk_conflicts = 0usize;
        let mut got_model = false;
        loop {
            match run_pass(&polv, seed, &banned, false, base_idx.take()) {
                PassOut::Pristine => {
                    if debug {
                        eprintln!("KM_ELC_CERT repair: base model already complete");
                    }
                    return if rooted_domain {
                        if rooted_publish {
                            rooted_unverified()
                        } else {
                            CertOutcome::Fail
                        }
                    } else {
                        CertOutcome::Pass
                    };
                }
                PassOut::Model(st, prov) => {
                    if model_index == 0 {
                        banned0 = banned.clone();
                    }
                    pass_states.push((st, prov));
                    got_model = true;
                    break;
                }
                PassOut::Conflict(triples, score) => {
                    if let (Some(score), Some(path)) = (score, rooted_ban_checkpoint.as_ref()) {
                        // A zero-length violation vector can accompany a dead
                        // canonical witness or protected root. It is not a
                        // better search frontier than a low nonzero residual
                        // batch, so do not let it overwrite that checkpoint.
                        if score != 0 && score < best_conflict_score {
                            best_conflict_score = score;
                            let best_path = path.with_extension("best.tsv");
                            if let Err(error) = write_bans(&best_path, &banned) {
                                if debug {
                                    eprintln!(
                                        "KM_ELC_CERT repair: could not update best checkpoint {}: {error}",
                                        best_path.display(),
                                    );
                                }
                            } else if debug {
                                eprintln!(
                                    "KM_ELC_CERT repair pass {seed}: retained best score {score} at {}",
                                    best_path.display(),
                                );
                            }
                        }
                    }
                    let inserted = apply_conflicts(&mut banned, triples);
                    if bulk_causal_clause_conflicts
                        && (!eager_causal_mix || eager_continuation)
                        && inserted != 0
                    {
                        rooted_shared_bans = banned.clone();
                        save_rooted_bans(&rooted_shared_bans);
                    }
                    // Two ontology-wide conflict waves establish that this
                    // polarity cannot preserve every base-alive witness. The
                    // death-tolerant pass computes a complete model and leaves
                    // only the affected subjects for exact discharge.
                    if inserted >= 1_024 {
                        bulk_conflicts += 1;
                    }
                    // The historical death-tolerant fallback is useful when
                    // broad witness deaths show that a strict polarity is a
                    // poor global model.  A rooted causal-clause schedule is
                    // different: each bulk wave can discharge one independent
                    // universal partition on the path to the protected root.
                    // Preserve those accumulated bans and continue through
                    // later causal clauses instead of discarding the strict
                    // search after the second large batch.
                    if bulk_conflicts >= 2 && !bulk_causal_clause_conflicts {
                        if debug {
                            eprintln!(
                                "KM_ELC_CERT repair pass {seed}: two bulk conflict waves; \
                                 switching to the exact partial-certificate pass"
                            );
                        }
                        break;
                    }
                    if restarts >= strict_restart_cap || inserted == 0 {
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
        if bulk_causal_clause_conflicts && (!eager_causal_mix || eager_continuation) {
            rooted_shared_bans = banned.clone();
            if debug {
                eprintln!(
                    "KM_ELC_CERT repair pass {seed}: retained {} rooted causal choice ban(s)",
                    rooted_shared_bans.len()
                );
            }
        }
        if !got_model {
            // strict passes kept dying: accept a model that lets witnesses
            // die — their subjects become unresolved residue for the engine.
            // Canonical Skolem witnesses remain mandatory, so retry batched
            // conflicts that report one of those dying.
            let mut tolerant_banned = banned.clone();
            for _ in 0..=tolerant_restart_cap {
                match run_pass(&polv, seed + 10, &tolerant_banned, true, None) {
                    PassOut::Pristine => {
                        return if rooted_domain {
                            if rooted_publish {
                                rooted_unverified()
                            } else {
                                CertOutcome::Fail
                            }
                        } else {
                            CertOutcome::Pass
                        };
                    }
                    PassOut::Model(st, prov) => {
                        if debug {
                            eprintln!(
                                "KM_ELC_CERT repair pass {seed}: death-tolerant model accepted"
                            );
                        }
                        if model_index == 0 {
                            banned0 = tolerant_banned.clone();
                        }
                        pass_states.push((st, prov));
                        break;
                    }
                    PassOut::Conflict(triples, _score) => {
                        let inserted = apply_conflicts(&mut tolerant_banned, triples);
                        if bulk_causal_clause_conflicts
                            && (!eager_causal_mix || eager_continuation)
                            && inserted != 0
                        {
                            rooted_shared_bans = tolerant_banned.clone();
                            save_rooted_bans(&rooted_shared_bans);
                        }
                        if inserted == 0 {
                            break;
                        }
                    }
                    PassOut::Fail => break,
                }
            }
            if bulk_causal_clause_conflicts && (!eager_causal_mix || eager_continuation) {
                rooted_shared_bans = tolerant_banned.clone();
            }
        }
    }
    if pass_states.is_empty() {
        return CertOutcome::Fail;
    }
    if rooted_domain && !rooted_publish {
        if debug {
            eprintln!(
                "KM_ELC_CERT rooted-domain diagnostic: complete model found; refusing publication"
            );
        }
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
        let subjects: Vec<u32> = if rooted_domain {
            preserve_named.clone()
        } else {
            (0..n as u32).collect()
        };
        for c in subjects {
            let c = c as usize;
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
            let unsat_subject_count = unsat_subjects.len();
            if debug && !unsat_subjects.is_empty() {
                for &(ref st, ref prov) in pass_states.iter().take(1) {
                    for &start in unsat_subjects.iter().take(5) {
                        let mut node = start;
                        let mut path = vec![it.debug_name(node)];
                        let mut cause = "no local bottom cause found".to_string();
                        for _ in 0..64 {
                            if let Some(&sub) = nfs
                                .nf5
                                .iter()
                                .find(|&&sub| st.sub_super[node as usize].contains(&sub))
                            {
                                let derivation = if let Some(rci) = prov.get(&(node, sub)) {
                                    format!("direct residual choice {rci}")
                                } else if let Some(nf) = nfs.nf1.iter().find(|nf| {
                                    nf.sup == sub && st.sub_super[node as usize].contains(&nf.sub)
                                }) {
                                    format!(
                                        "NF1 {} (choice={:?})",
                                        it.name(nf.sub),
                                        prov.get(&(node, nf.sub))
                                    )
                                } else if let Some(nf) = nfs.nf2.iter().find(|nf| {
                                    nf.sup == sub
                                        && st.sub_super[node as usize].contains(&nf.sub1)
                                        && st.sub_super[node as usize].contains(&nf.sub2)
                                }) {
                                    format!(
                                        "NF2 {} & {} (choices={:?},{:?})",
                                        it.name(nf.sub1),
                                        it.name(nf.sub2),
                                        prov.get(&(node, nf.sub1)),
                                        prov.get(&(node, nf.sub2))
                                    )
                                } else if let Some((nf, target)) = nfs.nf4.iter().find_map(|nf| {
                                    (nf.sup == sub).then(|| {
                                        st.edges[node as usize]
                                            .iter()
                                            .find(|(role, target)| {
                                                *role == nf.role
                                                    && st.sub_super[*target as usize]
                                                        .contains(&nf.filler)
                                            })
                                            .map(|(_, target)| (nf, *target))
                                    })?
                                }) {
                                    format!(
                                        "NF4 edge -{}->{} with filler {}",
                                        it.name(nf.role),
                                        it.debug_name(target),
                                        it.name(nf.filler)
                                    )
                                } else {
                                    "derivation not reconstructed".to_string()
                                };
                                cause =
                                    format!("NF5 {} <= bottom via {}", it.name(sub), derivation);
                                break;
                            }
                            if let Some(nf) = nfs.nf2.iter().find(|nf| {
                                nf.sup == BOTTOM
                                    && st.sub_super[node as usize].contains(&nf.sub1)
                                    && st.sub_super[node as usize].contains(&nf.sub2)
                            }) {
                                cause = format!(
                                    "NF2 {} & {} <= bottom (choices={:?},{:?})",
                                    it.name(nf.sub1),
                                    it.name(nf.sub2),
                                    prov.get(&(node, nf.sub1)),
                                    prov.get(&(node, nf.sub2)),
                                );
                                break;
                            }
                            if let Some((role, target)) = st.edges[node as usize]
                                .iter()
                                .find(|(_, target)| {
                                    st.sub_super[*target as usize].contains(&BOTTOM)
                                })
                                .copied()
                            {
                                node = target;
                                path.push(format!("-{}->{}", it.name(role), it.debug_name(node)));
                                continue;
                            }
                            break;
                        }
                        eprintln!(
                            "KM_ELC_CERT dead trace {}: {} ; {}",
                            it.name(start),
                            path.join(" "),
                            cause
                        );
                    }
                }
            }
            let mut unresolved: Vec<u32> = unsat_subjects;
            unresolved.extend(undet.iter().map(|p| p.0));
            if rooted_domain {
                let protected: HashSet<u32> = preserve_named.iter().copied().collect();
                unresolved.extend(
                    base_alive_named
                        .iter()
                        .copied()
                        .filter(|c| !protected.contains(c)),
                );
            }
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
            if rooted_domain || unresolved.len() <= cap {
                if debug {
                    eprintln!(
                        "KM_ELC_CERT partial: {} unresolved subject(s) left for the \
                         context engine (unsat_in_all_models={}, undetermined_pairs={}, \
                         models={}, refine={})",
                        unresolved.len(),
                        unsat_subject_count,
                        undet.len(),
                        pass_states.len(),
                        refine,
                    );
                }
                return CertOutcome::Partial(unresolved);
            }
            if debug {
                eprintln!(
                    "KM_ELC_CERT repair fail: {} unresolved subjects exceed the residue cap \
                     (unsat_in_all_models={}, undetermined_pairs={}, models={}, refine={})",
                    unresolved.len(),
                    unsat_subject_count,
                    undet.len(),
                    pass_states.len(),
                    refine,
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
            match run_pass(&polv0, 20 + refine, &banned0, true, None) {
                PassOut::Pristine => {
                    return if rooted_domain {
                        if rooted_publish {
                            rooted_unverified()
                        } else {
                            CertOutcome::Fail
                        }
                    } else {
                        CertOutcome::Pass
                    };
                }
                PassOut::Model(st, prov) => {
                    pass_states.push((st, prov));
                    break;
                }
                PassOut::Conflict(triples, _score) => {
                    let mut inserted = 0usize;
                    for triple in triples {
                        inserted += usize::from(banned0.insert(triple));
                    }
                    if restarts >= RESTART_CAP || inserted == 0 {
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
    /// Worker-only dictionary-coded taxonomy. Public [`classify`] never sets
    /// this field; the isolated ELC worker may use it to avoid materialising
    /// and then re-interning millions of repeated superclass strings.
    #[serde(skip)]
    pub(crate) compact: Option<crate::json_io::CompactElcOutput>,
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

/// Exact typed-ABox translation consumed by both batch and incremental EL
/// materialization. `Inconsistent` records an identity contradiction that is
/// complete before completion starts.
pub enum PositiveAboxPreparation {
    Clauses {
        clauses: Vec<JClause>,
        roots: std::collections::HashSet<String>,
    },
    Inconsistent,
}

/// Materialise a positive ground ABox and retain the exact EL taxonomy produced
/// by that same completion. Every injected rule is rooted at a fresh ABox-node
/// concept, and generated role edges connect only those fresh roots and their
/// fresh witnesses. No injected rule can therefore add a subsumption whose
/// subject is an original named class. Consequently the returned named-class
/// taxonomy is the ordinary TBox taxonomy as well as the consistency
/// certificate.
pub fn prepare_positive_abox(
    clauses: Vec<JClause>,
    meta: &crate::json_io::NominalAboxMeta,
) -> Option<PositiveAboxPreparation> {
    prepare_positive_abox_mode(clauses, meta, false)
}

fn prepare_positive_abox_mode(
    mut clauses: Vec<JClause>,
    meta: &crate::json_io::NominalAboxMeta,
    merge_all: bool,
) -> Option<PositiveAboxPreparation> {
    let debug = std::env::var_os("KM_ELC_DEBUG").is_some();
    // This helper rewrites the retained ABox into fresh completion concepts.
    // The source-bound ELC publication theorem currently covers the resulting
    // clause stream, not the preceding identity/ABox rewrite.  A caller asking
    // for the Lean-certified publication boundary must therefore decline here
    // and use a separately source-certified ABox route.
    if std::env::var_os("KM_ELC_LEAN_REQUIRED").is_some() {
        if debug {
            eprintln!("KM_EL_ABOX defer: source ABox rewrite is outside the ELC Lean boundary");
        }
        return None;
    }
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
            return Some(PositiveAboxPreparation::Inconsistent);
        }
    }

    let node = |root: usize| {
        if merge_all {
            "__km_abox_merged".to_string()
        } else {
            format!("__km_abox_node_{root}")
        }
    };
    let var = || JTerm::Var {
        name: "x".to_string(),
    };
    let concept = |name: String, term: JTerm| JAtom::Concept {
        concept: name,
        term,
    };

    let mut merged_markers = std::collections::HashSet::new();
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
            if merge_all && !merged_markers.insert(marker.as_str()) {
                continue;
            }
            clauses.push(JClause {
                body: vec![concept(node(root), var())],
                head: vec![concept(marker.clone(), var())],
            });
        }
    }
    let mut merged_roles = std::collections::HashSet::new();
    for (edge_index, edge) in meta.role_assertions.iter().enumerate() {
        if merge_all && !merged_roles.insert(edge.role.as_str()) {
            continue;
        }
        let source = find(&mut parent, ids[edge.source.as_str()]);
        let target = find(&mut parent, ids[edge.target.as_str()]);
        let fun = JTerm::Fun {
            function: if merge_all {
                format!("__km_abox_role_{}", edge.role)
            } else {
                format!("__km_abox_edge_{edge_index}")
            },
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
    let identity_roots: Box<dyn Iterator<Item = usize>> = if merge_all {
        Box::new(std::iter::once(0))
    } else {
        Box::new(0..parent.len())
    };
    for index in identity_roots {
        let root = if merge_all {
            0
        } else {
            find(&mut parent, index)
        };
        clauses.push(JClause {
            body: vec![concept(node(root), var())],
            head: vec![concept(node(root), var())],
        });
    }

    let roots: std::collections::HashSet<String> = if merge_all {
        std::iter::once(node(0)).collect()
    } else {
        (0..parent.len())
            .map(|i| node(find(&mut parent, i)))
            .collect()
    };
    Some(PositiveAboxPreparation::Clauses { clauses, roots })
}

pub fn positive_abox_classify(
    clauses: Vec<JClause>,
    meta: &crate::json_io::NominalAboxMeta,
) -> Option<PositiveAboxResult> {
    positive_abox_classify_mode(clauses, meta, false, false)
}

/// Orchestrator-specialized positive-ABox completion. It computes the same
/// fixpoint and consistency verdict as [`positive_abox_classify`] while
/// retaining dictionary-coded taxonomy rows for the public-output mapper.
pub(crate) fn positive_abox_classify_compact(
    clauses: Vec<JClause>,
    meta: &crate::json_io::NominalAboxMeta,
) -> Option<PositiveAboxResult> {
    positive_abox_classify_mode(clauses, meta, true, false)
}

/// Fast consistency certificate obtained by homomorphically merging every
/// named ABox individual into one completion root. Any derivation in the real
/// ABox maps to this over-approximation, so absence of bottom proves the real
/// ABox consistent. A merged-root clash declines and lets the caller reload
/// the unchanged input for exact per-individual materialization.
pub(crate) fn positive_abox_classify_compact_merged(
    clauses: Vec<JClause>,
    meta: &crate::json_io::NominalAboxMeta,
) -> Option<PositiveAboxResult> {
    positive_abox_classify_mode(clauses, meta, true, true)
}

fn positive_abox_classify_mode(
    clauses: Vec<JClause>,
    meta: &crate::json_io::NominalAboxMeta,
    compact: bool,
    merged_overapprox: bool,
) -> Option<PositiveAboxResult> {
    let prepared = prepare_positive_abox_mode(clauses, meta, merged_overapprox)?;
    let PositiveAboxPreparation::Clauses { clauses, roots } = prepared else {
        return Some(PositiveAboxResult {
            consistent: false,
            classification: None,
        });
    };
    let debug = std::env::var_os("KM_ELC_DEBUG").is_some();
    let result = match if compact {
        classify_compact(clauses)
    } else {
        classify(clauses)
    } {
        Some(result) => result,
        None => {
            if debug {
                eprintln!("KM_EL_ABOX defer: augmented clause set is not pure EL++");
            }
            return None;
        }
    };
    let node_unsat = if let Some(encoded) = &result.compact {
        let bottom = encoded
            .names
            .iter()
            .position(|name| matches!(name.as_ref(), "owl:Nothing" | "⊥"));
        bottom.is_some_and(|bottom| {
            encoded.rows.iter().any(|(subject, supers)| {
                roots.contains(encoded.names[*subject as usize].as_ref())
                    && supers.iter().any(|&sup| sup as usize == bottom)
            })
        })
    } else {
        roots.iter().any(|root| {
            result
                .subsumptions
                .get(root)
                .is_some_and(|supers| supers.iter().any(|sup| sup == "owl:Nothing"))
        })
    };
    if merged_overapprox && node_unsat && !result.inconsistent {
        return None;
    }
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

/// Statistics for one accepted EL transaction.
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

/// Incremental EL++ classification.
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
/// changing the clauses, revision, or completed state. Removals and
/// replacements use a conservative symbol-dependency
/// graph: unaffected completion components are copied at fixpoint, while the
/// changed component is initialized and saturated against the candidate rule
/// indexes. Global top-premise changes complete afresh.
pub struct IncrementalElClassifier {
    clauses: Vec<JClause>,
    interner: Interner,
    concept_ids: HashSet<u32>,
    normal_forms: HashSet<NormalFormKey>,
    state: State,
    revision: u64,
}

fn el_term_symbols(term: &JTerm, symbols: &mut Vec<String>) {
    match term {
        JTerm::Var { .. } => {}
        JTerm::Ind { name } => symbols.push(format!("I:{name}")),
        JTerm::Aux { root, label } => {
            symbols.push(format!("I:{root}"));
            symbols.extend(label.iter().map(|(name, _)| format!("C:{name}")));
        }
        JTerm::Fun { function, arg } => {
            symbols.push(format!("F:{function}"));
            el_term_symbols(arg, symbols);
        }
    }
}

fn el_clause_symbols(clause: &JClause) -> Vec<String> {
    let mut symbols = Vec::new();
    for atom in clause.body.iter().chain(&clause.head) {
        match atom {
            JAtom::Concept { concept, term } => {
                symbols.push(format!("C:{concept}"));
                el_term_symbols(term, &mut symbols);
            }
            JAtom::Role {
                role,
                source,
                target,
            } => {
                symbols.push(format!("R:{role}"));
                el_term_symbols(source, &mut symbols);
                el_term_symbols(target, &mut symbols);
            }
            JAtom::Eq { left, right } => {
                el_term_symbols(left, &mut symbols);
                el_term_symbols(right, &mut symbols);
            }
        }
    }
    symbols.sort_unstable();
    symbols.dedup();
    symbols
}

fn is_top_name(name: &str) -> bool {
    name == "owl:Thing" || name == "http://www.w3.org/2002/07/owl#Thing" || name == "\u{22a4}"
}

fn changed_clause_is_global(clause: &JClause) -> bool {
    clause.body.is_empty()
        || clause
            .body
            .iter()
            .any(|atom| matches!(atom, JAtom::Concept { concept, .. } if is_top_name(concept)))
}

/// Symbols in the dependency component touched by a replacement. `None`
/// means the change has a global premise and therefore admits no component
/// reuse. Edges from both snapshots make removal and replacement conservative.
fn affected_el_symbols(
    old: &[JClause],
    new: &[JClause],
    changed: &[JClause],
) -> Option<HashSet<String>> {
    if changed.iter().any(changed_clause_is_global) {
        return None;
    }
    let mut graph: HashMap<String, HashSet<String>> = HashMap::default();
    for clause in old.iter().chain(new) {
        let symbols = el_clause_symbols(clause);
        for symbol in &symbols {
            let neighbours = graph.entry(symbol.clone()).or_default();
            neighbours.extend(symbols.iter().filter(|other| *other != symbol).cloned());
        }
    }
    let mut affected = HashSet::default();
    let mut queue = VecDeque::new();
    for clause in changed {
        for symbol in el_clause_symbols(clause) {
            if affected.insert(symbol.clone()) {
                queue.push_back(symbol);
            }
        }
    }
    while let Some(symbol) = queue.pop_front() {
        if let Some(neighbours) = graph.get(&symbol) {
            for neighbour in neighbours {
                if affected.insert(neighbour.clone()) {
                    queue.push_back(neighbour.clone());
                }
            }
        }
    }
    // Every concept row implicitly contains top, even when its source clauses
    // share no symbols with a global rule. If the affected component reaches
    // such a rule, its consequences can occur in every row: the explicit-symbol
    // graph no longer proves that the other rows are independent. Include both
    // snapshots so deletions cannot retain consequences of an old global rule.
    if old.iter().chain(new).any(|clause| {
        changed_clause_is_global(clause)
            && el_clause_symbols(clause)
                .iter()
                .any(|symbol| affected.contains(symbol))
    }) {
        return None;
    }
    Some(affected)
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
        // The retained worklist is empty at a fixpoint; widen it to the new
        // symbol space and queue the replay through its own discipline.
        debug_assert!(self.state.worklist.is_empty());
        self.state.worklist.grow(next_len);
        for (c, supers) in self.state.sub_super.iter().enumerate() {
            for &d in supers {
                self.state.worklist.push(Item::Sub(c as u32, d));
            }
        }
        for (c, edges) in self.state.edges.iter().enumerate() {
            for &(r, d) in edges {
                self.state.worklist.push(Item::Edge(c as u32, r, d));
            }
        }

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

    /// Replace the complete clause snapshot while retaining every completion
    /// component disconnected from the changed clauses. This is the deletion
    /// counterpart of [`Self::add_clauses`]. A changed global/top premise, or
    /// one dependency component spanning the whole ontology, takes the exact
    /// fresh path and reports no reuse.
    pub fn replace_clauses(
        &self,
        candidate: Vec<JClause>,
        changed_clauses: &[JClause],
    ) -> Result<(Self, IncrementalUpdate), IncrementalError> {
        let mut next_interner = self.interner.clone();
        let (next_nfs, residual, _) =
            to_nf(&candidate, &mut next_interner).ok_or(IncrementalError::UnsupportedNormalForm)?;
        if !residual.is_empty() {
            return Err(IncrementalError::NonElResidual {
                clauses: residual.len(),
            });
        }

        let old_subsumptions = fact_count(&self.state.sub_super);
        let old_edges = fact_count(&self.state.edges);
        let affected = affected_el_symbols(&self.clauses, &candidate, changed_clauses);
        let all_affected = affected.is_none();
        let affected = affected.unwrap_or_default();
        let next_concept_ids = next_nfs.concept_names.clone();
        let next_role_ids = next_nfs.role_names.clone();

        if all_affected {
            let total_clauses = candidate.len();
            let mut next = Self::new(candidate)?;
            next.revision = self.revision + 1;
            let new_subsumptions = fact_count(&next.state.sub_super);
            let new_edges = fact_count(&next.state.edges);
            return Ok((
                next,
                IncrementalUpdate {
                    revision: self.revision + 1,
                    added_clauses: 0,
                    total_clauses,
                    reused_fixpoint: false,
                    reused_subsumptions: 0,
                    reused_edges: 0,
                    new_subsumptions,
                    new_edges,
                },
            ));
        }

        let next_len = next_interner.len();
        let name_affected =
            |tag: char, id: u32| affected.contains(&format!("{tag}:{}", next_interner.name(id)));
        let mut state = State {
            sub_super: vec![HashSet::default(); next_len],
            edges: vec![HashSet::default(); next_len],
            in_by_role: HashMap::default(),
            in_roles: vec![Vec::new(); next_len],
            prop: HashMap::default(),
            worklist: Worklist::from_env(next_len),
            sub_journal: None,
            edge_epoch: 0,
        };

        // Copy only closed components whose rules and symbols are unchanged.
        // Builtin top remains in every retained label; bottom is copied only
        // as a consequence of an unaffected component.
        for &concept in &next_concept_ids {
            if name_affected('C', concept) || concept as usize >= self.state.sub_super.len() {
                continue;
            }
            for &sup in &self.state.sub_super[concept as usize] {
                if sup == TOP
                    || sup == BOTTOM
                    || (next_concept_ids.contains(&sup) && !name_affected('C', sup))
                {
                    state.sub_super[concept as usize].insert(sup);
                }
            }
            for &(role, target) in &self.state.edges[concept as usize] {
                if next_role_ids.contains(&role)
                    && next_concept_ids.contains(&target)
                    && !name_affected('R', role)
                    && !name_affected('C', target)
                {
                    state.edges[concept as usize].insert((role, target));
                    state
                        .in_by_role
                        .entry((target, role))
                        .or_default()
                        .push(concept);
                    if !state.in_roles[target as usize].contains(&role) {
                        state.in_roles[target as usize].push(role);
                    }
                }
            }
        }
        let reused_subsumptions = fact_count(&state.sub_super);
        let reused_edges = fact_count(&state.edges);

        // Initialize only affected/new concept rows. Unaffected rows are
        // already at their old fixpoint and have no path to a changed rule.
        for &concept in &next_concept_ids {
            if name_affected('C', concept) || state.sub_super[concept as usize].is_empty() {
                if concept != BOTTOM {
                    state.add_sub(concept, concept);
                    state.add_sub(concept, TOP);
                }
            }
        }
        let idx = build_idx(&next_nfs, next_len);
        seed_reflexive_edges(&next_nfs, &idx, &mut state);
        run(&idx, &mut state, &mut Prof::default());

        let final_subsumptions = fact_count(&state.sub_super);
        let final_edges = fact_count(&state.edges);
        let next = IncrementalElClassifier {
            clauses: candidate,
            interner: next_interner,
            concept_ids: next_concept_ids,
            normal_forms: normal_form_keys(&next_nfs),
            state,
            revision: self.revision + 1,
        };
        let total_clauses = next.clauses.len();
        Ok((
            next,
            IncrementalUpdate {
                revision: self.revision + 1,
                added_clauses: 0,
                total_clauses,
                reused_fixpoint: reused_subsumptions != 0 || reused_edges != 0,
                reused_subsumptions: reused_subsumptions.min(old_subsumptions),
                reused_edges: reused_edges.min(old_edges),
                new_subsumptions: final_subsumptions.saturating_sub(reused_subsumptions),
                new_edges: final_edges.saturating_sub(reused_edges),
            },
        ))
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
            compact: None,
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

fn configured_cert_mode() -> CertMode {
    // Default OFF: on the ORE 2015 corpus every non-EL residual is a live
    // covering disjunction / non-inert inverse bridge / multi-successor
    // functionality, none of which the canonical EL model satisfies, so the
    // PLAIN certificate never passes there -- and attempting it would saturate
    // the (large) EL subset before failing, stealing time from the CB
    // fallback. `KM_ELC_CERT=1` enables the plain check (near-EL ontologies
    // whose non-EL part IS model-satisfiable); `KM_ELC_CERT=2` additionally
    // repairs violated residuals by disjunct choice and certifies via the
    // intersection of the choice-pass models.
    match std::env::var("KM_ELC_CERT").as_deref() {
        Ok("1") | Ok("on") => CertMode::Check,
        Ok("2") | Ok("repair") => CertMode::Repair,
        _ => CertMode::Off,
    }
}

pub fn classify(clauses: Vec<JClause>) -> Option<ElResult> {
    let cert = configured_cert_mode();
    let debug = std::env::var("KM_ELC_DEBUG").is_ok();
    classify_inner(clauses, cert, debug)
}

/// Worker-specialized entry point. Dense acyclic NF1 taxonomies may retain
/// their interned relation IDs through the existing compact binary handoff;
/// library callers continue to receive the established string map.
pub(crate) fn classify_worker(clauses: Vec<JClause>) -> Option<ElResult> {
    let cert = configured_cert_mode();
    let debug = std::env::var("KM_ELC_DEBUG").is_ok();
    let compact_nf1_output = std::env::var_os("KM_ELC_OUTPUT_BINARY").is_some()
        && std::env::var_os("KM_NO_ELC_OUTPUT_BINARY").is_none();
    classify_inner_mode(clauses, cert, debug, compact_nf1_output, false)
}

/// Orchestrator entry point for the exact in-process EL leaf: the complete
/// fixpoint is returned dictionary-coded (`ElResult::compact`) instead of as
/// one owned superclass string per pair. Residue answers keep the string map.
pub(crate) fn classify_compact(clauses: Vec<JClause>) -> Option<ElResult> {
    let cert = configured_cert_mode();
    let debug = std::env::var("KM_ELC_DEBUG").is_ok();
    // Both output-producing branches must retain dictionary coding: acyclic
    // NF1 returns before the general fixpoint-output branch is reached.
    classify_inner_mode(clauses, cert, debug, true, true)
}

/// `KM_ELC_TIMING` phase laps inside the completion itself (the worker's
/// `classify=` line only brackets the whole call). Off by default.
fn elc_timing_lap(on: bool, last: &mut std::time::Instant, label: &str) {
    if on {
        let now = std::time::Instant::now();
        eprintln!("KM_ELC_TIMING {label}={:.3}s", (now - *last).as_secs_f64());
        *last = now;
    }
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
///
/// Exact fast path for a pure, satisfiable atomic taxonomy whose directed
/// subclass graph is acyclic.  General EL completion inserts every reachable
/// pair through a hash-set worklist.  On million-class taxonomies that means
/// hashing the complete published relation even though NF1 closure is just
/// graph reachability.  Reverse-topological vector unions derive exactly the
/// same least transitive closure while storing each published pair once.
///
/// The deliberately narrow screen excludes bottom, TOP premises, every other
/// normal form, residuals, and Lean publication requests.  A cycle declines
/// to the general completion path rather than adding SCC logic here.
fn acyclic_nf1_taxonomy(
    nfs: &Nfs,
    residual_is_empty: bool,
    it: &Interner,
    lean_cert_requested: bool,
    compact_output: bool,
    force_compact_output: bool,
) -> Option<ElResult> {
    if std::env::var_os("KM_ELC_DEBUG_DERIVATION").is_some() {
        let trace_concept = std::env::var("KM_ELC_DEBUG_CONCEPT")
            .unwrap_or_else(|_| "Q_36024".to_string());
        let trace_node = std::env::var("KM_ELC_DEBUG_NODE")
            .unwrap_or_else(|_| "CL_0000540".to_string());
        DEBUG_ADD_SUB_CONCEPT.store(
            it.id(&trace_concept).map_or(usize::MAX, |id| id as usize),
            Ordering::Relaxed,
        );
        DEBUG_ADD_SUB_NODE.store(
            it.id(&trace_node).map_or(usize::MAX, |id| id as usize),
            Ordering::Relaxed,
        );
        DEBUG_ADD_SUB_COUNT.store(0, Ordering::Relaxed);
        if let Some(target) = it.id(&trace_concept) {
            for nf in nfs.nf1.iter().filter(|nf| nf.sup == target) {
                eprintln!(
                    "KM_ELC_CERT target NF1 predecessor: {}({}) -> {}({})",
                    it.name(nf.sub),
                    nf.sub,
                    it.name(nf.sup),
                    nf.sup,
                );
            }
            for nf in nfs.nf2.iter().filter(|nf| nf.sup == target) {
                eprintln!(
                    "KM_ELC_CERT target NF2 predecessor: {}({}) & {}({}) -> {}({})",
                    it.name(nf.sub1),
                    nf.sub1,
                    it.name(nf.sub2),
                    nf.sub2,
                    it.name(nf.sup),
                    nf.sup,
                );
            }
            for nf in nfs.nf4.iter().filter(|nf| nf.sup == target) {
                eprintln!(
                    "KM_ELC_CERT target NF4 predecessor: exists {}({}).{}({}) -> {}({})",
                    it.name(nf.role),
                    nf.role,
                    it.name(nf.filler),
                    nf.filler,
                    it.name(nf.sup),
                    nf.sup,
                );
            }
        }
    }
    if !residual_is_empty
        || lean_cert_requested
        || std::env::var_os("KM_ELC_NO_ACYCLIC_NF1").is_some()
        || !nfs.nf2.is_empty()
        || !nfs.nf3.is_empty()
        || !nfs.nf4.is_empty()
        || !nfs.nf5.is_empty()
        || !nfs.nf6.is_empty()
        || !nfs.nf7.is_empty()
        || !nfs.reflexive_roles.is_empty()
        || !nfs.role_names.is_empty()
        || nfs.nf1.iter().any(|a| a.sub == TOP || a.sup == BOTTOM)
    {
        return None;
    }

    let n = it.len();
    let mut outgoing = vec![Vec::<u32>::new(); n];
    for ax in &nfs.nf1 {
        if ax.sub == ax.sup || ax.sup == TOP {
            continue;
        }
        outgoing[ax.sub as usize].push(ax.sup);
    }
    let mut indegree = vec![0u32; n];
    for successors in &mut outgoing {
        successors.sort_unstable();
        successors.dedup();
        for &sup in successors.iter() {
            indegree[sup as usize] = indegree[sup as usize].saturating_add(1);
        }
    }

    let mut queue = VecDeque::new();
    for &concept in &nfs.concept_names {
        if concept != TOP && concept != BOTTOM && indegree[concept as usize] == 0 {
            queue.push_back(concept);
        }
    }
    let expected = nfs
        .concept_names
        .iter()
        .filter(|&&c| c != TOP && c != BOTTOM)
        .count();
    let mut order = Vec::with_capacity(expected);
    while let Some(concept) = queue.pop_front() {
        order.push(concept);
        for &sup in &outgoing[concept as usize] {
            let degree = &mut indegree[sup as usize];
            *degree -= 1;
            if *degree == 0 {
                queue.push_back(sup);
            }
        }
    }
    if order.len() != expected {
        return None;
    }

    let mut closure = vec![Vec::<u32>::new(); n];
    for &concept in order.iter().rev() {
        let successors = &outgoing[concept as usize];
        if successors.len() == 1 {
            let sup = successors[0];
            let mut reached = closure[sup as usize].clone();
            match reached.binary_search(&sup) {
                Ok(_) => {}
                Err(at) => reached.insert(at, sup),
            }
            closure[concept as usize] = reached;
        } else if !successors.is_empty() {
            let mut reached: HashSet<u32> = HashSet::default();
            for &sup in successors {
                reached.insert(sup);
                reached.extend(closure[sup as usize].iter().copied());
            }
            let mut reached: Vec<u32> = reached.into_iter().collect();
            reached.sort_unstable();
            closure[concept as usize] = reached;
        }
    }
    drop(outgoing);
    drop(indegree);

    if compact_output && (force_compact_output || expected >= 1_000) {
        let mut rows = Vec::new();
        for &concept in &nfs.concept_names {
            if concept == TOP || concept == BOTTOM {
                continue;
            }
            let reached = std::mem::take(&mut closure[concept as usize]);
            if !reached.is_empty() {
                rows.push((concept, reached));
            }
        }
        return Some(ElResult {
            unresolved: Vec::new(),
            subsumptions: std::collections::BTreeMap::new(),
            inconsistent: false,
            compact: Some(crate::json_io::CompactElcOutput {
                names: it.cloned_shared_names(),
                rows,
                inconsistent: false,
                dropped: 0,
            }),
        });
    }

    let mut subsumptions = std::collections::BTreeMap::new();
    for &concept in &nfs.concept_names {
        if concept == TOP || concept == BOTTOM {
            continue;
        }
        let reached = std::mem::take(&mut closure[concept as usize]);
        if !reached.is_empty() {
            subsumptions.insert(
                it.name(concept).to_string(),
                reached
                    .into_iter()
                    .map(|sup| it.name(sup).to_string())
                    .collect(),
            );
        }
    }
    Some(ElResult {
        unresolved: Vec::new(),
        subsumptions,
        inconsistent: false,
        compact: None,
    })
}

fn classify_inner(clauses: Vec<JClause>, cert: CertMode, debug: bool) -> Option<ElResult> {
    classify_inner_mode(clauses, cert, debug, false, false)
}

fn classify_inner_mode(
    clauses: Vec<JClause>,
    cert: CertMode,
    debug: bool,
    compact_nf1_output: bool,
    compact_fixpoint_output: bool,
) -> Option<ElResult> {
    let elc_timing = std::env::var_os("KM_ELC_TIMING").is_some();
    let mut elc_lap = std::time::Instant::now();
    let lean_cert_path = std::env::var_os("KM_ELC_LEAN_CERT_OUT").map(std::path::PathBuf::from);
    let lean_cert_checker =
        std::env::var_os("KM_ELC_LEAN_CERT_CHECKER").map(std::path::PathBuf::from);
    let lean_cert_required = std::env::var_os("KM_ELC_LEAN_REQUIRED").is_some();
    if lean_cert_required && lean_cert_checker.is_none() {
        eprintln!("KM_ELC_LEAN_CERT fail closed: missing required publication checker");
        return None;
    }
    let lean_cert_requested =
        lean_cert_required || lean_cert_path.is_some() || lean_cert_checker.is_some();
    let mut unresolved: Vec<String> = Vec::new();
    // Residual-shrinking inverse-bridge rewrites are not yet part of the Lean
    // source theorem. A checker-backed run must retain the exact input stream;
    // otherwise an accepted certificate would start after an uncertified
    // preprocessing boundary. Non-Lean certificate modes keep the established
    // optimization. Cert-off classify declines on the first residual clause.
    let mut clauses = clauses;
    if cert != CertMode::Off
        && !lean_cert_requested
        && std::env::var_os("KM_ELC_NO_BRIDGE_PREP").is_none()
    {
        prepare_inverse_bridges(&mut clauses, debug);
    }
    let clauses = clauses;
    let mut it = Interner::new();
    let (mut nfs, residual, skolem_target) = to_nf(&clauses, &mut it)?;
    let rooted_batch_names: Option<Vec<String>> = match std::env::var_os("KM_ELC_PRESERVE_FILE") {
        Some(path) => {
            let text = match std::fs::read_to_string(&path) {
                Ok(text) => text,
                Err(error) => {
                    eprintln!(
                        "KM_ELC_CERT fail closed: cannot read preserve file {}: {error}",
                        std::path::Path::new(&path).display()
                    );
                    return None;
                }
            };
            let names: Vec<String> = text
                .lines()
                .map(str::trim)
                .filter(|name| !name.is_empty())
                .map(str::to_owned)
                .collect();
            let unique: HashSet<&str> = names.iter().map(String::as_str).collect();
            if names.is_empty() || unique.len() != names.len() {
                eprintln!("KM_ELC_CERT fail closed: preserve file is empty or has duplicates");
                return None;
            }
            Some(names)
        }
        None => None,
    };
    elc_timing_lap(elc_timing, &mut elc_lap, "to_nf");
    // TOP is always a semantic concept context, even when no normalized axiom
    // mentions it explicitly. The inconsistency readout queries TOP ⊑ BOTTOM,
    // so omitting this initialization could miss an ontology-level clash.
    nfs.concept_names.insert(TOP);
    if let Some(result) = acyclic_nf1_taxonomy(
        &nfs,
        residual.is_empty(),
        &it,
        lean_cert_requested,
        compact_nf1_output,
        compact_fixpoint_output,
    ) {
        return Some(result);
    }
    // ELK discards the OWL parse tree once axioms are indexed. `to_nf` has
    // interned the EL part into `nfs` (u32-keyed) and cloned the non-EL part into
    // `residual`; the original `clauses` (millions of `JClause`, each owning
    // `String` IRIs -- a multi-GB block on the giants) is dead from here on.
    // Drop it BEFORE saturation so the parse tree never coexists with the peak
    // saturation state. On a pure-EL ont (`residual` empty) this is the whole
    // input freed; the saturation then peaks on the interned state alone.
    let background_release = std::env::var_os("KM_ELC_BG_DROP").is_some();
    // Finer laps inside `index+init` (that lap itself is unchanged): the drop
    // of the parsed clause set, the rule index, and the seeded state.
    let mut elc_sub = std::time::Instant::now();
    let certificate_clauses = if lean_cert_requested {
        Some(clauses)
    } else {
        release(clauses, background_release);
        None
    };
    elc_timing_lap(elc_timing, &mut elc_sub, "index+init/drop_clauses");
    let (rcs, residual_skolem_witnesses) = if residual.is_empty() {
        (Vec::new(), HashMap::default())
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
            Some(compiled) => (compiled.clauses, compiled.skolem_witnesses),
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
    if std::env::var_os("KM_ELC_DEBUG_DERIVATION").is_some() {
        let trace_concept = std::env::var("KM_ELC_DEBUG_CONCEPT")
            .unwrap_or_else(|_| "Q_36024".to_string());
        let trace_node = std::env::var("KM_ELC_DEBUG_NODE")
            .unwrap_or_else(|_| "CL_0000540".to_string());
        DEBUG_ADD_SUB_CONCEPT.store(
            it.id(&trace_concept).map_or(usize::MAX, |id| id as usize),
            Ordering::Relaxed,
        );
        DEBUG_ADD_SUB_NODE.store(
            it.id(&trace_node).map_or(usize::MAX, |id| id as usize),
            Ordering::Relaxed,
        );
        DEBUG_ADD_SUB_COUNT.store(0, Ordering::Relaxed);
    }
    let n = it.len();
    elc_sub = std::time::Instant::now();
    let idx = build_idx(&nfs, n);
    elc_timing_lap(elc_timing, &mut elc_sub, "index+init/build_idx");
    // Context-parallel saturation when it is asked for and nothing depends on
    // the serial construction order (see `context_parallel_plan`); it seeds its
    // own shards, so the serial state is not built at all on that path.
    let parallel_workers = context_parallel_workers(cert, lean_cert_requested, n);
    let mut seeded = match parallel_workers {
        Some(_) => None,
        None => {
            let mut st = init_state(&nfs, n);
            // EL++ reflexive roles: seed a self-edge (C,R,C) at every satisfiable
            // concept node for each reflexive role (closed up the role hierarchy).
            // The existing NF4 (∃R.D⊑E), NF7 (R∘S⊑T, both chain positions),
            // ⊥-edge, and role-lift rules then fire over these edges through the
            // normal fixpoint -- no new rule logic. This mirrors ELK's
            // `⊤⊑∃R.Self` + ObjectHasSelf decomposition, and because a self-edge
            // feeds NF7 in both directions it also closes the
            // reflexive-role-plus-chain corner ELK marks only partially supported.
            seed_reflexive_edges(&nfs, &idx, &mut st);
            Some(st)
        }
    };
    elc_timing_lap(elc_timing, &mut elc_sub, "index+init/init_state");
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
    elc_timing_lap(elc_timing, &mut elc_lap, "index+init");
    let mut prof = Prof::default();
    let st = match (seeded.take(), parallel_workers) {
        (None, Some(workers)) => match run_context_parallel(&nfs, &idx, n, workers, &mut prof) {
            Some(st) => st,
            // The worker threads could not be started: fall back to the serial
            // engine, seeds and all.
            None => {
                let mut st = init_state(&nfs, n);
                seed_reflexive_edges(&nfs, &idx, &mut st);
                run(&idx, &mut st, &mut prof);
                st
            }
        },
        (Some(mut st), _) => {
            run(&idx, &mut st, &mut prof);
            st
        }
        (None, None) => unreachable!("the serial path seeds its state"),
    };
    elc_timing_lap(elc_timing, &mut elc_lap, "saturate");
    if std::env::var_os("KM_ELC_DEBUG_DERIVATION").is_some() {
        if let (Ok(trace_name), Ok(node_name)) = (
            std::env::var("KM_ELC_DEBUG_CONCEPT"),
            std::env::var("KM_ELC_DEBUG_NODE"),
        ) {
            if let (Some(concept), Some(node)) = (it.id(&trace_name), it.id(&node_name)) {
                if st.sub_super[node as usize].contains(&concept) {
                    eprintln!(
                        "KM_ELC_CERT base target present: {}@{}",
                        trace_name, node_name
                    );
                    let mut seen = HashSet::default();
                    let mut lines = 0;
                    debug_el_membership_producers(
                        node,
                        concept,
                        &st,
                        &nfs,
                        &it,
                        &HashMap::default(),
                        &mut seen,
                        5,
                        &mut lines,
                    );
                }
            }
        }
    }
    if lean_cert_requested {
        let source_clauses = certificate_clauses
            .as_deref()
            .expect("requested certificate retains source clauses");
        let residual_compilations = match build_lean_residual_compilations(&residual, &rcs, &it) {
            Ok(compilations) => compilations,
            Err(error) => {
                eprintln!("KM_ELC_LEAN_CERT fail closed: {error}");
                return None;
            }
        };
        let (direct_clauses, witness_records) = match build_lean_source_partition(
            source_clauses,
            &residual,
            &skolem_target,
            &residual_skolem_witnesses,
            &it,
        ) {
            Ok(partition) => partition,
            Err(error) => {
                eprintln!("KM_ELC_LEAN_CERT fail closed: {error}");
                return None;
            }
        };
        let certificate = match build_lean_el_certificate(
            &nfs,
            &st,
            &it,
            &direct_clauses,
            witness_records,
            residual_compilations,
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
            temporary_path =
                std::env::temp_dir().join(format!("km-elc-cert-{}.json", std::process::id()));
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
            "KM_ELC_PROFILE sub_items={} edge_items={} | nf1_scan={} nf2_scan={} \
             nf2_label_side={} nf3_scan={} nf4_sub_scan={} nf4_edge_scan={} nf7_scan={} \
             botback={} | nf4_batch_calls={} nf4_batch_edges={} nf4_batch_groups={} \
             nf4_batch_missing={} | ctx_activations={} link_items={} par_workers={} \
             par_batches={} par_messages={}",
            prof.sub_items,
            prof.edge_items,
            prof.nf1_scan,
            prof.nf2_scan,
            prof.nf2_label_side,
            prof.nf3_scan,
            prof.nf4_sub_scan,
            prof.nf4_edge_scan,
            prof.nf7_scan,
            prof.botback,
            prof.nf4_batch_calls,
            prof.nf4_batch_edges,
            prof.nf4_batch_groups,
            prof.nf4_batch_missing,
            prof.ctx_activations,
            prof.link_items,
            prof.par_workers,
            prof.par_batches,
            prof.par_messages
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
            CertMode::Repair => {
                if let Some(batch) = rooted_batch_names.as_deref() {
                    if std::env::var_os("KM_ELC_REPAIR_ROOT_DOMAIN").is_none()
                        || std::env::var_os("KM_ELC_REPAIR_ROOT_PUBLISH").is_none()
                        || std::env::var_os("KM_ELC_PRESERVE").is_some()
                    {
                        eprintln!(
                            "KM_ELC_CERT fail closed: preserve-file batching requires rooted publication and no KM_ELC_PRESERVE"
                        );
                        return None;
                    }
                    let mut intersection: Option<HashSet<u32>> = None;
                    for root in batch {
                        let Some(root_id) = it.id(root) else {
                            eprintln!("KM_ELC_CERT fail closed: unknown batch root {root}");
                            return None;
                        };
                        if !nfs.concept_names.contains(&root_id)
                            || crate::calc::is_internal_concept(it.name(root_id))
                            || res.sub_super[root_id as usize].contains(&BOTTOM)
                        {
                            eprintln!("KM_ELC_CERT fail closed: invalid batch root {root}");
                            return None;
                        }
                        match repair_certify(
                            &rcs,
                            &nfs,
                            &idx,
                            &res,
                            &it,
                            debug,
                            Some(std::slice::from_ref(root)),
                        ) {
                            CertOutcome::Partial(subjects)
                                if !subjects.iter().any(|&subject| subject == root_id) =>
                            {
                                let subjects: HashSet<u32> = subjects.into_iter().collect();
                                match &mut intersection {
                                    Some(current) => {
                                        current.retain(|subject| subjects.contains(subject))
                                    }
                                    None => intersection = Some(subjects),
                                }
                            }
                            _ => {
                                eprintln!(
                                    "KM_ELC_CERT fail closed: batch root {root} was not independently certified"
                                );
                                return None;
                            }
                        }
                    }
                    let mut unresolved: Vec<u32> =
                        intersection.unwrap_or_default().into_iter().collect();
                    unresolved.sort_unstable();
                    CertOutcome::Partial(unresolved)
                } else {
                    repair_certify(&rcs, &nfs, &idx, &res, &it, debug, None)
                }
            }
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
    elc_timing_lap(elc_timing, &mut elc_lap, "certificate");

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
    let rooted_output_names: Option<HashSet<String>> =
        std::env::var_os("KM_ELC_REPAIR_ROOT_PUBLISH").and_then(|_| {
            rooted_batch_names
                .clone()
                .or_else(|| std::env::var("KM_ELC_PRESERVE").ok().map(|name| vec![name]))
                .map(|names| {
                    names
                        .into_iter()
                        .flat_map(|name| name.split(',').map(str::to_owned).collect::<Vec<_>>())
                        .filter(|name| !name.is_empty())
                        .collect()
                })
        });
    // Everything below reads only the completed relation (`sub_super`) and the
    // interner names. The rule indexes, the normal forms, the residual, the
    // compiled residual clauses, and the role graph (`edges` / `in_by_role` /
    // `in_roles` / `prop`) are dead here — free them BEFORE materialising the output
    // strings, so the string map reuses their memory instead of stacking on
    // top of the full saturation state (process peak RSS on the ORE giants
    // sits exactly at this point, the fixpoint). Destructuring `res` drops the
    // unbound `State` fields in place.
    let State {
        mut sub_super,
        edges,
        in_by_role,
        in_roles,
        prop,
        worklist,
        sub_journal,
        edge_epoch: _,
    } = res;
    release(
        (
            idx,
            nfs,
            rcs,
            residual,
            skolem_target,
            edges,
            in_by_role,
            in_roles,
            prop,
            worklist,
            sub_journal,
        ),
        background_release,
    );
    elc_timing_lap(elc_timing, &mut elc_lap, "release");

    // Dictionary-coded rows for the in-process orchestrator. The interned ids
    // and the single name table replace one owned superclass string per pair
    // and the string-keyed map. Rows follow the name order of that map, so a
    // consumer that keys on row order (the first-alias unsat representative)
    // sees the same subject sequence. Only a complete answer is coded: a
    // residue keeps the string map because its subjects are merged by name.
    if compact_fixpoint_output && unresolved.is_empty() {
        let names = it.into_names();
        let mut order: Vec<u32> = (0..sub_super.len() as u32)
            .filter(|&cid| cid != TOP && cid != BOTTOM && !sub_super[cid as usize].is_empty())
            .collect();
        order.sort_unstable_by(|&a, &b| names[a as usize].cmp(&names[b as usize]));
        let mut rows = Vec::with_capacity(order.len());
        for cid in order {
            let sups = std::mem::take(&mut sub_super[cid as usize]);
            let out: Vec<u32> = sups
                .iter()
                .copied()
                .filter(|&d| d != cid && d != TOP)
                .collect();
            if !out.is_empty() {
                rows.push((cid, out));
            }
        }
        elc_timing_lap(elc_timing, &mut elc_lap, "output(compact)");
        return Some(ElResult {
            unresolved: Vec::new(),
            subsumptions: std::collections::BTreeMap::new(),
            inconsistent: el_inconsistent,
            compact: Some(crate::json_io::CompactElcOutput {
                names,
                rows,
                inconsistent: el_inconsistent,
                dropped: 0,
            }),
        });
    }

    let mut subsumptions = std::collections::BTreeMap::new();
    for c in 0..sub_super.len() {
        let cid = c as u32;
        // ⊤/⊥ as a *subject* give trivially-true ⊤⊑X / ⊥⊑X, which no reasoner
        // reports as a class subsumption — skip them.
        if cid == TOP || cid == BOTTOM {
            continue;
        }
        // A rooted worker publishes only the subjects whose carriers and
        // countermodels it checked. Base-derived rows outside that set remain
        // exact, but repeating them in every array task would turn a compact
        // per-row proof into terabytes of redundant output.
        if rooted_output_names
            .as_ref()
            .is_some_and(|names| !names.contains(it.name(cid)))
        {
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
        if !out.is_empty() || rooted_output_names.is_some() {
            subsumptions.insert(it.name(cid).to_string(), out);
        }
    }
    elc_timing_lap(elc_timing, &mut elc_lap, "output(strings)");

    Some(ElResult {
        subsumptions,
        inconsistent: el_inconsistent,
        unresolved,
        compact: None,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    static ROOTED_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    struct EnvRestore(&'static str, Option<std::ffi::OsString>);

    impl EnvRestore {
        fn set(name: &'static str, value: &str) -> Self {
            let old = std::env::var_os(name);
            std::env::set_var(name, value);
            Self(name, old)
        }

        fn remove(name: &'static str) -> Self {
            let old = std::env::var_os(name);
            std::env::remove_var(name);
            Self(name, old)
        }
    }

    impl Drop for EnvRestore {
        fn drop(&mut self) {
            match self.1.take() {
                Some(value) => std::env::set_var(self.0, value),
                None => std::env::remove_var(self.0),
            }
        }
    }

    #[test]
    fn repair_violation_cap_override_is_bounded_and_fail_safe() {
        assert_eq!(repair_viol_cap_from(None), REPAIR_VIOL_CAP);
        assert_eq!(repair_viol_cap_from(Some("invalid")), REPAIR_VIOL_CAP);
        assert_eq!(repair_viol_cap_from(Some("0")), 1);
        assert_eq!(repair_viol_cap_from(Some("750000")), 750_000);
        assert_eq!(repair_viol_cap_from(Some("999999999")), 5_000_000);
    }

    #[test]
    fn repair_choice_mixer_gives_binary_heads_distinct_seed_assignments() {
        let assignments: HashSet<Vec<usize>> = (0..8)
            .map(|pass| {
                (100_000..100_064)
                    .map(|node| repair_choice_mix(node, 119, pass) % 2)
                    .collect()
            })
            .collect();
        assert_eq!(assignments.len(), 8);
    }

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
            nf2: vec![Nf2 {
                sub1: 2,
                sub2: 3,
                sup: TOP,
            }],
            nf3: vec![Nf3 {
                sub: 3,
                role: 4,
                filler: 2,
            }],
            nf4: vec![Nf4 {
                role: 4,
                filler: 3,
                sup: 2,
            }],
            nf5: vec![],
            nf6: vec![Nf6 { sub: 4, sup: 5 }],
            nf7: vec![Nf7 {
                r1: 5,
                r2: 4,
                sup: 6,
            }],
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
        let cert = build_lean_el_certificate(&nfs, &state, &interner, &[], Vec::new(), Vec::new())
            .expect("exact certificate");
        assert_eq!(cert.version, 5);
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
            fact.sub != TOP && fact.sub != BOTTOM && fact.sup != fact.sub && fact.sup != TOP
        }));

        state.sub_super[2].insert(6);
        assert!(
            build_lean_el_certificate(&nfs, &state, &interner, &[], Vec::new(), Vec::new())
                .unwrap_err()
                .contains("Rust-only subsumption")
        );
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

    #[test]
    fn compact_fixpoint_output_matches_the_string_map() {
        use std::collections::{BTreeMap, BTreeSet};
        // NF1, NF2, NF3 (existential pair), NF4, and a bottom conjunction, so
        // the general fixpoint runs (the acyclic NF1 shortcut declines).
        let cs = clauses(&format!(
            "[{},{},{},{},{},{},{},{}]",
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[c("B", "x"), c("C", "x")], &[c("D", "x")]),
            cl(&[c("A", "x")], &[c("C", "x")]),
            cl(&[c("B", "x")], &[cf("F", "f", "x")]),
            cl(&[c("B", "x")], &[rf("r", "x", "f")]),
            cl(&[r("r", "x", "y"), c("F", "y")], &[c("E", "x")]),
            cl(&[c("G", "x"), c("B", "x")], &[]),
            cl(&[c("A", "x")], &[c("G", "x")]),
        ));
        let expected = classify_inner_mode(cs.clone(), CertMode::Off, false, false, false)
            .expect("pure EL input");
        let compact =
            classify_inner_mode(cs, CertMode::Off, false, false, true).expect("pure EL input");
        assert!(compact.subsumptions.is_empty());
        assert!(compact.unresolved.is_empty());
        let compact = compact.compact.expect("dictionary-coded fixpoint");
        assert_eq!(compact.inconsistent, expected.inconsistent);
        let mut rebuilt: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut previous: Option<&str> = None;
        for (subject, supers) in &compact.rows {
            let name = compact.names[*subject as usize].as_ref();
            assert!(
                previous.map_or(true, |p| p < name),
                "rows follow the string map's name order"
            );
            previous = Some(name);
            let sups: BTreeSet<String> = supers
                .iter()
                .map(|&d| {
                    if d == BOTTOM {
                        "owl:Nothing".to_string()
                    } else {
                        compact.names[d as usize].to_string()
                    }
                })
                .collect();
            assert!(rebuilt.insert(name.to_string(), sups).is_none());
        }
        let expected: BTreeMap<String, BTreeSet<String>> = expected
            .subsumptions
            .into_iter()
            .map(|(subject, supers)| (subject, supers.into_iter().collect()))
            .collect();
        assert_eq!(rebuilt, expected);
        // The fixture exercises every path the coding must preserve: NF2
        // (D), the existential join (E), and the bottom translation.
        assert!(expected["A"].contains("D"));
        assert!(expected["A"].contains("E"));
        assert!(expected["A"].contains("owl:Nothing"));
        assert!(expected["B"].contains("E"));
    }

    fn positive_abox_consistency(ofn: &str) -> Option<bool> {
        let _environment_lock = crate::frontend::lock_test_environment();
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
            SubClassOf(ObjectIntersectionOf(<urn:A> <urn:B>) owl:Nothing)
            ClassAssertion(<urn:A> <urn:a>)
            ClassAssertion(<urn:B> <urn:b>)
            DifferentIndividuals(<urn:a> <urn:b>)
        )"#;
        assert_eq!(positive_abox_consistency(consistent), Some(true));

        let inconsistent = r#"Ontology(
            SubClassOf(ObjectIntersectionOf(<urn:A> <urn:B>) owl:Nothing)
            ClassAssertion(<urn:A> <urn:a>)
            ClassAssertion(<urn:B> <urn:b>)
            SameIndividual(<urn:a> <urn:b>)
        )"#;
        assert_eq!(positive_abox_consistency(inconsistent), Some(false));
    }

    #[test]
    fn positive_abox_completion_materializes_ground_role_edges() {
        let inconsistent = r#"Ontology(
            SubClassOf(ObjectSomeValuesFrom(<urn:r> <urn:B>) owl:Nothing)
            ObjectPropertyAssertion(<urn:r> <urn:a> <urn:b>)
            ClassAssertion(<urn:B> <urn:b>)
        )"#;
        assert_eq!(positive_abox_consistency(inconsistent), Some(false));
    }

    #[test]
    fn positive_abox_completion_retains_the_exact_named_taxonomy() {
        let ofn = r#"Ontology(
            Declaration(Class(<urn:A>))
            Declaration(Class(<urn:B>))
            Declaration(Class(<urn:C>))
            SubClassOf(<urn:A> <urn:B>)
            SubClassOf(<urn:B> <urn:C>)
            ClassAssertion(<urn:A> <urn:a>)
        )"#;
        let _environment_lock = crate::frontend::lock_test_environment();
        crate::frontend::with_ofn_to_clauses_requested_route(
            ofn,
            crate::routing::Route::ProductionAll,
            |frontend| {
                let named: std::collections::HashSet<&str> =
                    frontend.named.iter().map(String::as_str).collect();
                let tbox = classify(frontend.clauses.clone()).expect("pure EL TBox");
                let abox = positive_abox_classify(frontend.clauses, &frontend.nominal_abox)
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

    #[test]
    fn compact_positive_abox_completion_matches_string_result() {
        let ofn = r#"Ontology(
            Declaration(Class(<urn:A>))
            Declaration(Class(<urn:B>))
            Declaration(Class(<urn:C>))
            SubClassOf(<urn:A> <urn:B>)
            SubClassOf(<urn:B> <urn:C>)
            ClassAssertion(<urn:A> <urn:a>)
            SameIndividual(<urn:a> <urn:b>)
            DifferentIndividuals(<urn:a> <urn:c>)
        )"#;
        let _environment_lock = crate::frontend::lock_test_environment();
        crate::frontend::with_ofn_to_clauses_requested_route(
            ofn,
            crate::routing::Route::ProductionAll,
            |frontend| {
                let string =
                    positive_abox_classify(frontend.clauses.clone(), &frontend.nominal_abox)
                        .expect("string completion");
                let compact =
                    positive_abox_classify_compact(frontend.clauses, &frontend.nominal_abox)
                        .expect("compact completion");
                assert_eq!(compact.consistent, string.consistent);
                let string = string.classification.expect("string taxonomy");
                let compact = compact.classification.expect("compact taxonomy");
                let encoded = compact.compact.expect("dictionary-coded taxonomy");
                for subject in &frontend.named {
                    let row = encoded
                        .rows
                        .iter()
                        .find(|(id, _)| encoded.names[*id as usize].as_ref() == subject)
                        .map(|(_, supers)| {
                            let mut names: Vec<_> = supers
                                .iter()
                                .map(|id| encoded.names[*id as usize].to_string())
                                .collect();
                            names.sort();
                            names
                        });
                    let mut expected = string.subsumptions.get(subject).cloned();
                    if let Some(expected) = &mut expected {
                        expected.sort();
                    }
                    assert_eq!(row, expected, "named taxonomy changed for {subject}");
                }
            },
        )
        .expect("ontology parses");
    }

    #[test]
    fn merged_positive_abox_proves_safe_separated_individuals() {
        let ofn = r#"Ontology(
            SubClassOf(ObjectIntersectionOf(<urn:A> <urn:B>) owl:Nothing)
            ClassAssertion(<urn:A> <urn:a>)
            ClassAssertion(<urn:A> <urn:b>)
            DifferentIndividuals(<urn:a> <urn:b>)
        )"#;
        let _environment_lock = crate::frontend::lock_test_environment();
        crate::frontend::with_ofn_to_clauses_requested_route(
            ofn,
            crate::routing::Route::ProductionAll,
            |frontend| {
                let merged = positive_abox_classify_compact_merged(
                    frontend.clauses.clone(),
                    &frontend.nominal_abox,
                )
                .expect("merged abstraction proves consistency");
                let exact =
                    positive_abox_classify_compact(frontend.clauses, &frontend.nominal_abox)
                        .expect("exact completion");
                assert!(merged.consistent);
                assert_eq!(merged.consistent, exact.consistent);
            },
        )
        .expect("ontology parses");
    }

    #[test]
    fn merged_positive_abox_declines_a_spurious_cross_individual_clash() {
        let ofn = r#"Ontology(
            SubClassOf(ObjectIntersectionOf(<urn:A> <urn:B>) owl:Nothing)
            ClassAssertion(<urn:A> <urn:a>)
            ClassAssertion(<urn:B> <urn:b>)
            DifferentIndividuals(<urn:a> <urn:b>)
        )"#;
        let _environment_lock = crate::frontend::lock_test_environment();
        crate::frontend::with_ofn_to_clauses_requested_route(
            ofn,
            crate::routing::Route::ProductionAll,
            |frontend| {
                let merged = positive_abox_classify_compact_merged(
                    frontend.clauses.clone(),
                    &frontend.nominal_abox,
                );
                assert!(merged.is_none(), "merged abstraction must decline");
                let exact =
                    positive_abox_classify_compact(frontend.clauses, &frontend.nominal_abox)
                        .expect("exact fallback");
                assert!(exact.consistent);
            },
        )
        .expect("ontology parses");
    }

    #[test]
    fn compact_positive_abox_detects_node_local_bottom() {
        let ofn = r#"Ontology(
            SubClassOf(ObjectIntersectionOf(<urn:A> <urn:B>) owl:Nothing)
            ClassAssertion(<urn:A> <urn:a>)
            ClassAssertion(<urn:B> <urn:a>)
        )"#;
        let _environment_lock = crate::frontend::lock_test_environment();
        crate::frontend::with_ofn_to_clauses_requested_route(
            ofn,
            crate::routing::Route::ProductionAll,
            |frontend| {
                let result =
                    positive_abox_classify_compact(frontend.clauses, &frontend.nominal_abox)
                        .expect("compact exact completion");
                assert!(!result.consistent);
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

    #[test]
    fn lean_v5_certificate_checks_source_partition_and_rejects_tampering() {
        let Some(checker) = std::env::var_os("KM_ELC_TEST_LEAN_CHECKER") else {
            return;
        };
        let source = clauses(&format!("[{}]", cl(&[c("A", "x")], &[c("B", "x")])));
        let mut interner = Interner::new();
        let (mut nfs, residual, _) = to_nf(&source, &mut interner).expect("direct EL source");
        assert!(residual.is_empty());
        nfs.concept_names.insert(TOP);
        let idx = build_idx(&nfs, interner.len());
        let mut state = init_state(&nfs, interner.len());
        run(&idx, &mut state, &mut Prof::default());
        let certificate =
            build_lean_el_certificate(&nfs, &state, &interner, &source, Vec::new(), Vec::new())
                .expect("v5 certificate");
        let path = std::env::temp_dir().join(format!(
            "km-elc-v5-cert-{}-{}.json",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let run_checker = |payload: &LeanElCertificate| {
            std::fs::write(&path, serde_json::to_vec(payload).unwrap()).unwrap();
            std::process::Command::new(&checker)
                .arg(&path)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .expect("run Lean v5 checker")
                .success()
        };
        assert!(
            run_checker(&certificate),
            "exact source partition must pass"
        );

        let a = interner.id("A").expect("A is interned");
        let source_var = LeanRawTerm::Var { name: 0 };
        let tautology_raw = LeanResidualClause {
            body: vec![LeanResidualAtom::Concept {
                concept: a,
                term: source_var.clone(),
            }],
            head: vec![LeanResidualAtom::Concept {
                concept: a,
                term: source_var,
            }],
        };
        let tautology = LeanResidualCompilation {
            variable_count: 1,
            origins: vec![LeanResidualOrigin::Source { name: 0 }],
            raw: tautology_raw.clone(),
            body: vec![LeanCompiledResidualAtom::Concept {
                concept: a,
                slot: 0,
            }],
            head: vec![LeanCompiledResidualAtom::Concept {
                concept: a,
                slot: 0,
            }],
            pins: Vec::new(),
        };
        let mut residual_certificate = certificate.clone();
        residual_certificate.source_ontology.push(tautology_raw);
        residual_certificate.residual_compilations.push(tautology);
        assert!(
            run_checker(&residual_certificate),
            "a structurally exact residual tautology must pass the finite model check"
        );

        let mut false_residual = residual_certificate.clone();
        let compilation = false_residual
            .residual_compilations
            .last_mut()
            .expect("residual compilation");
        compilation.raw.head = vec![LeanResidualAtom::Concept {
            concept: BOTTOM,
            term: LeanRawTerm::Var { name: 0 },
        }];
        compilation.head = vec![LeanCompiledResidualAtom::Concept {
            concept: BOTTOM,
            slot: 0,
        }];
        *false_residual
            .source_ontology
            .last_mut()
            .expect("residual source clause") = compilation.raw.clone();
        assert!(
            !run_checker(&false_residual),
            "a structurally exact but canonically false residual must fail closed"
        );

        let mut omitted_source = certificate.clone();
        omitted_source.source_ontology.clear();
        assert!(
            !run_checker(&omitted_source),
            "source omission must fail closed"
        );

        let mut duplicate_symbol = certificate.clone();
        let b = interner.id("B").expect("B is interned");
        duplicate_symbol.symbols[b as usize] = duplicate_symbol.symbols[a as usize].clone();
        assert!(
            !run_checker(&duplicate_symbol),
            "duplicate public symbol names must fail closed"
        );

        let mut old_version = certificate.clone();
        old_version.version = 4;
        assert!(
            !run_checker(&old_version),
            "wire downgrade must fail closed"
        );
        let _ = std::fs::remove_file(path);
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
    fn acyclic_nf1_fast_path_is_exact_on_chain_and_diamond() {
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[c("A", "x")], &[c("B", "x")]),
            cl(&[c("A", "x")], &[c("C", "x")]),
            cl(&[c("B", "x")], &[c("D", "x")]),
            cl(&[c("C", "x")], &[c("D", "x")]),
        ));
        let mut interner = Interner::new();
        let (mut nfs, residual, _) = to_nf(&cs, &mut interner).expect("normal forms");
        nfs.concept_names.insert(TOP);
        let result =
            acyclic_nf1_taxonomy(&nfs, residual.is_empty(), &interner, false, false, false)
                .expect("acyclic NF1 path");
        assert_eq!(subs_of(&result, "A"), vec!["B", "C", "D"]);
        assert_eq!(subs_of(&result, "B"), vec!["D"]);
        assert_eq!(subs_of(&result, "C"), vec!["D"]);
        assert!(subs_of(&result, "D").is_empty());
        assert!(!result.inconsistent);
    }

    #[test]
    fn acyclic_nf1_fast_path_declines_cycles_and_bottom() {
        for cs in [
            clauses(&format!(
                "[{},{}]",
                cl(&[c("A", "x")], &[c("B", "x")]),
                cl(&[c("B", "x")], &[c("A", "x")]),
            )),
            clauses(&format!("[{}]", cl(&[c("A", "x")], &[]))),
        ] {
            let mut interner = Interner::new();
            let (mut nfs, residual, _) = to_nf(&cs, &mut interner).expect("normal forms");
            nfs.concept_names.insert(TOP);
            assert!(acyclic_nf1_taxonomy(
                &nfs,
                residual.is_empty(),
                &interner,
                false,
                false,
                false
            )
            .is_none());
        }
    }

    #[test]
    fn acyclic_nf1_worker_keeps_dictionary_coded_rows() {
        let mut interner = Interner::new();
        let mut concepts = HashSet::default();
        concepts.insert(TOP);
        let ids: Vec<u32> = (0..1_000)
            .map(|index| {
                let id = interner.intern(&format!("C{index}"));
                concepts.insert(id);
                id
            })
            .collect();
        let nfs = Nfs {
            nf1: vec![Nf1 {
                sub: ids[0],
                sup: ids[1],
            }],
            nf2: vec![],
            nf3: vec![],
            nf4: vec![],
            nf5: vec![],
            nf6: vec![],
            nf7: vec![],
            reflexive_roles: HashSet::default(),
            concept_names: concepts,
            role_names: HashSet::default(),
            conjunction_origins: HashMap::default(),
        };
        let result = acyclic_nf1_taxonomy(&nfs, true, &interner, false, true, false)
            .expect("compact NF1 result");
        assert!(result.subsumptions.is_empty());
        let compact = result.compact.expect("dictionary-coded worker result");
        assert_eq!(compact.names[ids[0] as usize].as_ref(), "C0");
        assert!(compact.rows.contains(&(ids[0], vec![ids[1]])));
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
            cl(
                &[c("A", "x"), c("A", "u")],
                &[cf("C", "x", "u")],
            ),
        ));
        let mut interner = Interner::new();
        let (mut nfs, residual, skolem_target) =
            to_nf(&cs, &mut interner).expect("normalizable EL prefix");
        assert_eq!(residual.len(), 1);
        let compiled = compile_residual(&residual, &mut interner, &mut nfs, &skolem_target)
            .expect("supported residual");
        assert_eq!(compiled.clauses[0].nvars, 3);
        assert_eq!(compiled.clauses[0].pins.len(), 1);
        assert_ne!(
            compiled.clauses[0].pins[0].0, 0,
            "source slot must remain unpinned"
        );
        assert!(matches!(compiled.clauses[0].body[0], RAtom::C { v: 0, .. }));
    }

    #[test]
    fn lean_residual_compilation_payload_accepts_and_tampering_fails() {
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[c("A", "u")], &[rf("R", "u", "x")]),
            cl(&[c("A", "u")], &[cf("B", "x", "u")]),
            cl(
                &[c("A", "x"), c("A", "u")],
                &[cf("C", "x", "u")],
            ),
            cl(&[c("B", "z")], &[c("C", "z")]),
        ));
        let mut interner = Interner::new();
        let (mut nfs, residual, skolem_target) =
            to_nf(&cs, &mut interner).expect("normalizable EL prefix");
        let compiled = compile_residual(&residual, &mut interner, &mut nfs, &skolem_target)
            .expect("supported residual");
        let payloads = build_lean_residual_compilations(&residual, &compiled.clauses, &interner)
            .expect("exact residual payload");
        assert_eq!(payloads.len(), 1);
        assert_eq!(payloads[0].origins.len(), payloads[0].variable_count);
        let json = serde_json::to_string(&payloads[0]).expect("payload JSON");
        assert!(json.contains("\"source\""));
        assert!(json.contains("\"function\""));

        let (direct, witnesses) = build_lean_source_partition(
            &cs,
            &residual,
            &skolem_target,
            &compiled.skolem_witnesses,
            &interner,
        )
        .expect("exact direct/witness/residual partition");
        assert_eq!(direct.len(), 1);
        assert_eq!(witnesses.len(), 1);
        nfs.concept_names.insert(TOP);
        let idx = build_idx(&nfs, interner.len());
        let mut state = init_state(&nfs, interner.len());
        run(&idx, &mut state, &mut Prof::default());
        let certificate = build_lean_el_certificate(
            &nfs,
            &state,
            &interner,
            &direct,
            witnesses,
            payloads.clone(),
        )
        .expect("whole residual certificate");
        assert_eq!(certificate.variable_count, 2,
            "the source variable used only by the residual clause must be in range");

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

        std::fs::write(&path, serde_json::to_vec(&certificate).unwrap()).unwrap();
        assert!(
            std::process::Command::new(&checker)
                .arg(&path)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .expect("run whole Lean checker")
                .success(),
            "native source partition must pass the whole Lean checker"
        );

        let previous_checker = std::env::var_os("KM_ELC_LEAN_CERT_CHECKER");
        std::env::set_var("KM_ELC_LEAN_CERT_CHECKER", &checker);
        let production = classify_inner(cs.clone(), CertMode::Check, false);
        match previous_checker {
            Some(value) => std::env::set_var("KM_ELC_LEAN_CERT_CHECKER", value),
            None => std::env::remove_var("KM_ELC_LEAN_CERT_CHECKER"),
        }
        assert!(
            production.is_some(),
            "checker-backed production residual publication must succeed"
        );

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
        let res = classify_inner(cs.clone(), CertMode::Repair, false).expect("repair certifies");
        assert!(subs_of(&res, "C").contains(&"D".to_string()));
        // The choices must not leak into the answer.
        assert!(!subs_of(&res, "C").contains(&"A".to_string()));
        assert!(!subs_of(&res, "C").contains(&"B".to_string()));
        assert!(!res.inconsistent);

        // The search-based repair algorithm has no Lean theorem yet. Even
        // when ordinary repair accepts this ontology, checker-backed repair
        // must stop at the rejected base-model certificate and publish
        // nothing from the uncertified search.
        if let Some(checker) = std::env::var_os("KM_ELC_TEST_LEAN_CHECKER") {
            let previous = std::env::var_os("KM_ELC_LEAN_CERT_CHECKER");
            std::env::set_var("KM_ELC_LEAN_CERT_CHECKER", checker);
            let certified = classify_inner(cs, CertMode::Repair, false);
            match previous {
                Some(value) => std::env::set_var("KM_ELC_LEAN_CERT_CHECKER", value),
                None => std::env::remove_var("KM_ELC_LEAN_CERT_CHECKER"),
            }
            assert!(
                certified.is_none(),
                "checker-backed execution must not publish repair output"
            );
        }
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

    #[test]
    fn repair_after_failed_base_check_uses_handed_off_index() {
        // The base check rejects the live cover. Its prebuilt enumeration
        // index is then reused by the first repair pass, which must still
        // produce the same exact range consequence without leaking a choice.
        let cs = clauses(&format!(
            "[{},{},{},{},{}]",
            cl(&[c("P", "x")], &[rf("R", "x", "f")]),
            cl(&[c("P", "x")], &[cf("Q", "f", "x")]),
            cl(&[c("Q", "x")], &[c("S", "x")]),
            cl(&[r("R", "x", "y")], &[c("S", "y")]),
            cl(&[], &[c("A", "x"), c("B", "x")]),
        ));
        assert!(classify_inner(cs.clone(), CertMode::Check, false).is_none());
        let res = classify_inner(cs, CertMode::Repair, false).expect("repair certifies");
        assert!(!res.inconsistent);
        assert!(res.unresolved.is_empty());
        assert!(subs_of(&res, "Q").contains(&"S".to_string()));
        for subject in ["P", "Q", "S"] {
            let sups = subs_of(&res, subject);
            assert!(!sups.contains(&"A".to_string()));
            assert!(!sups.contains(&"B".to_string()));
        }
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
            pin_guards: Vec::new(),
        }
    }

    #[test]
    fn residual_pin_must_name_an_alive_canonical_domain_element() {
        let clause = rc(
            1,
            vec![RAtom::C { cid: 2, v: 0 }],
            vec![RAtom::C { cid: 2, v: 0 }],
            vec![(0, 3)],
        );
        assert!(residual_pins_are_alive(
            &[clause],
            &[true, false, true, true]
        ));
        let clause = rc(
            1,
            vec![RAtom::C { cid: 2, v: 0 }],
            vec![RAtom::C { cid: 2, v: 0 }],
            vec![(0, 3)],
        );
        assert!(!residual_pins_are_alive(
            &[clause],
            &[true, false, true, false]
        ));
    }

    #[test]
    fn residual_pin_is_vacuous_when_its_exact_source_guard_is_empty() {
        let mut clause = rc(
            2,
            vec![RAtom::C { cid: 2, v: 0 }],
            vec![RAtom::C { cid: 4, v: 1 }],
            vec![(1, 3)],
        );
        clause.pin_guards.push((1, 2, 0));
        assert!(residual_pins_are_alive(
            &[clause],
            // guard 2 is empty and pin 3 is empty: the guarded clause has no
            // instances, so the dead dedicated witness is irrelevant.
            &[true, false, false, false, true]
        ));
    }

    #[test]
    fn rooted_pin_guard_activation_uses_domain_members_not_canonical_node() {
        let mut clause = rc(
            2,
            vec![RAtom::C { cid: 2, v: 0 }],
            vec![RAtom::C { cid: 4, v: 1 }],
            vec![(1, 3)],
        );
        clause.pin_guards.push((1, 2, 0));

        // In a rooted carrier the canonical node numbered like the guard is
        // irrelevant.  A different carrier node labelled with the guard makes
        // the source class nonempty and activates its dedicated witness.
        let mut members: HashMap<u32, Vec<u32>> = HashMap::default();
        members.insert(2, vec![7]);
        assert!(residual_clause_active_in(
            &clause,
            &[true, false, false, true],
            Some(&members),
        ));
        assert!(residual_pins_are_alive_in(
            std::slice::from_ref(&clause),
            &[true, false, false, true],
            Some(&members),
        ));

        // Conversely, merely retaining canonical node 2 does not activate the
        // guard when no carrier element is labelled with concept 2.
        members.remove(&2);
        assert!(!residual_clause_active_in(
            &clause,
            &[true, false, true, false],
            Some(&members),
        ));
        assert!(residual_pins_are_alive_in(
            &[clause],
            &[true, false, true, false],
            Some(&members),
        ));
    }

    #[test]
    fn rooted_domain_expands_edges_and_only_active_guarded_witnesses() {
        let mut guarded = rc(
            2,
            vec![RAtom::C { cid: 7, v: 0 }],
            vec![RAtom::C { cid: 8, v: 1 }],
            vec![(1, 4)],
        );
        guarded.pin_guards.push((1, 7, 0));
        let mut inactive = rc(
            2,
            vec![RAtom::C { cid: 9, v: 0 }],
            vec![RAtom::C { cid: 8, v: 1 }],
            vec![(1, 5)],
        );
        inactive.pin_guards.push((1, 9, 0));

        let st = state_of(12, &[(1, &[7])], &[(1, 3, 2), (2, 3, 3), (4, 3, 6)]);
        let mut domain: HashSet<u32> = HashSet::default();
        domain.insert(1);
        let mut repr: Vec<u32> = (0..12).collect();
        assert_eq!(
            expand_rooted_domain(&mut domain, &st, &[guarded, inactive], &mut repr),
            4,
        );
        assert_eq!(domain, HashSet::from_iter([1, 2, 3, 4, 6]));
        assert!(!domain.contains(&5));
    }

    #[test]
    fn inverse_functional_existentials_get_source_specific_fresh_targets() {
        let ifun = rc(
            3,
            vec![
                RAtom::R { rid: 8, s: 0, t: 2 },
                RAtom::R { rid: 8, s: 1, t: 2 },
            ],
            vec![RAtom::Eq { s: 0, t: 1 }],
            vec![],
        );
        assert_eq!(inverse_functional_role(&ifun), Some(8));

        let mut st = state_of(16, &[], &[]);
        let mut fresh = FreshInverseWitnesses {
            roles: HashSet::from_iter([8]),
            unrestricted_roles: HashSet::from_iter([8]),
            selected_pairs: HashSet::default(),
            deep_unrestricted_roles: HashSet::default(),
            deep_selected_pairs: HashSet::default(),
            selective_deep: false,
            active_sources: HashSet::from_iter([1, 2]),
            depth: HashMap::default(),
            max_depth: None,
            existential_pairs: HashSet::from_iter([(8, 9)]),
            nodes: HashMap::default(),
            origins: HashMap::default(),
            limit: 8,
            exhausted: false,
        };
        let a = fresh.target(&mut st, 1, 8, 9);
        let b = fresh.target(&mut st, 2, 8, 9);
        assert_ne!(a, b);
        assert_eq!(fresh.target(&mut st, 1, 8, 9), a);
        assert!(st.sub_super[a as usize].contains(&TOP));
        assert!(st.sub_super[a as usize].contains(&9));
        assert_eq!(fresh.target(&mut st, 1, 7, 9), 9);
        assert!(!fresh.exhausted);
    }

    #[test]
    fn rooted_existing_inverse_existential_edge_is_redirected() {
        let mut st = state_of(16, &[], &[(1, 8, 9)]);
        let mut fresh = FreshInverseWitnesses {
            roles: HashSet::from_iter([8]),
            unrestricted_roles: HashSet::from_iter([8]),
            selected_pairs: HashSet::default(),
            deep_unrestricted_roles: HashSet::default(),
            deep_selected_pairs: HashSet::default(),
            selective_deep: false,
            active_sources: HashSet::from_iter([1]),
            depth: HashMap::default(),
            max_depth: None,
            existential_pairs: HashSet::from_iter([(8, 9)]),
            nodes: HashMap::default(),
            origins: HashMap::default(),
            limit: 8,
            exhausted: false,
        };
        let domain = HashSet::from_iter([1]);
        assert_eq!(
            freshen_rooted_inverse_edges(
                &domain,
                &mut st,
                &mut fresh,
                &vec![HashSet::default(); 9],
            ),
            1,
        );
        assert!(!st.edges[1].contains(&(8, 9)));
        let target = st.edges[1]
            .iter()
            .find_map(|&(role, target)| (role == 8).then_some(target))
            .expect("redirected edge");
        assert!(target >= 16);
        assert_eq!(st.in_by_role.get(&(target, 8)), Some(&vec![1]));
        assert!(!st.in_by_role.contains_key(&(9, 8)));
        // A cached, already-freshened scaffold must be reusable: replaying the
        // redirect phase sees no canonical generating edge and changes
        // nothing.
        assert_eq!(
            freshen_rooted_inverse_edges(
                &domain,
                &mut st,
                &mut fresh,
                &vec![HashSet::default(); 9],
            ),
            0,
        );
        assert!(st.edges[1].contains(&(8, target)));
    }

    #[test]
    fn rooted_fresh_pair_is_limited_to_active_sources_and_exact_fillers() {
        let mut st = state_of(16, &[], &[]);
        let mut fresh = FreshInverseWitnesses {
            roles: HashSet::from_iter([8]),
            unrestricted_roles: HashSet::default(),
            selected_pairs: HashSet::from_iter([(8, 9)]),
            deep_unrestricted_roles: HashSet::default(),
            deep_selected_pairs: HashSet::default(),
            selective_deep: false,
            active_sources: HashSet::from_iter([1]),
            depth: HashMap::default(),
            max_depth: None,
            existential_pairs: HashSet::from_iter([(8, 9), (8, 10)]),
            nodes: HashMap::default(),
            origins: HashMap::default(),
            limit: 8,
            exhausted: false,
        };
        assert!(fresh.target(&mut st, 1, 8, 9) >= 16);
        assert_eq!(fresh.target(&mut st, 1, 8, 10), 10);
        assert_eq!(fresh.target(&mut st, 2, 8, 9), 9);
    }

    #[test]
    fn rooted_fresh_depth_reuses_canonical_filler_at_cutoff() {
        let mut st = state_of(16, &[], &[]);
        let mut fresh = FreshInverseWitnesses {
            roles: HashSet::from_iter([8]),
            unrestricted_roles: HashSet::from_iter([8]),
            selected_pairs: HashSet::default(),
            deep_unrestricted_roles: HashSet::default(),
            deep_selected_pairs: HashSet::default(),
            selective_deep: false,
            active_sources: HashSet::from_iter([1]),
            depth: HashMap::default(),
            max_depth: Some(2),
            existential_pairs: HashSet::from_iter([(8, 9)]),
            nodes: HashMap::default(),
            origins: HashMap::default(),
            limit: 8,
            exhausted: false,
        };
        let child = fresh.target(&mut st, 1, 8, 9);
        assert!(child >= 16);
        let grandchild = fresh.target(&mut st, child, 8, 9);
        assert!(grandchild > child);
        assert_eq!(fresh.target(&mut st, grandchild, 8, 9), 9);
    }

    #[test]
    fn rooted_fresh_deep_frontier_can_differ_from_first_layer() {
        let mut st = state_of(16, &[], &[]);
        let mut fresh = FreshInverseWitnesses {
            roles: HashSet::from_iter([8, 11]),
            unrestricted_roles: HashSet::from_iter([8, 11]),
            selected_pairs: HashSet::default(),
            deep_unrestricted_roles: HashSet::from_iter([11]),
            deep_selected_pairs: HashSet::default(),
            selective_deep: true,
            active_sources: HashSet::from_iter([1]),
            depth: HashMap::default(),
            max_depth: Some(2),
            existential_pairs: HashSet::from_iter([(8, 9), (11, 12)]),
            nodes: HashMap::default(),
            origins: HashMap::default(),
            limit: 8,
            exhausted: false,
        };
        let child = fresh.target(&mut st, 1, 8, 9);
        assert!(child >= 16);
        assert_eq!(fresh.target(&mut st, child, 8, 9), 9);
        assert!(fresh.target(&mut st, child, 11, 12) > child);
    }

    #[test]
    fn rooted_fresh_bottom_sources_do_not_consume_live_witness_budget() {
        // A doomed source has two existential obligations, with room for only
        // one fresh witness. Its obligations must not prevent the unrelated
        // live source from getting that witness and deriving its NF4 result.
        let nfs = Nfs {
            nf1: Vec::new(), nf2: Vec::new(),
            nf3: vec![
                Nf3 { sub: 3, role: 8, filler: 10 },
                Nf3 { sub: 3, role: 8, filler: 11 },
                Nf3 { sub: 5, role: 8, filler: 9 },
            ],
            nf4: vec![Nf4 { role: 8, filler: 9, sup: 12 }],
            nf5: vec![3], nf6: Vec::new(), nf7: Vec::new(),
            reflexive_roles: HashSet::default(),
            concept_names: HashSet::default(), role_names: HashSet::default(),
            conjunction_origins: HashMap::default(),
        };
        let idx = build_idx(&nfs, 16);
        let mut st = state_of(16, &[], &[]);
        st.add_sub(2, 3);
        st.add_sub(4, 5);
        st.add_edge(6, 8, 2);
        let mut fresh = FreshInverseWitnesses {
            roles: HashSet::from_iter([8]),
            unrestricted_roles: HashSet::from_iter([8]),
            selected_pairs: HashSet::default(),
            deep_unrestricted_roles: HashSet::default(),
            deep_selected_pairs: HashSet::default(),
            selective_deep: false,
            active_sources: HashSet::from_iter([2, 4]),
            depth: HashMap::default(), max_depth: Some(1),
            existential_pairs: HashSet::from_iter([(8, 9), (8, 10), (8, 11)]),
            nodes: HashMap::default(), origins: HashMap::default(),
            limit: 1, exhausted: false,
        };
        run_with_fresh_inverse(&idx, &mut st, &mut Prof::default(), &mut fresh);
        assert!(st.sub_super[2].contains(&BOTTOM));
        assert!(st.sub_super[6].contains(&BOTTOM), "bottom must still propagate");
        assert!(!st.sub_super[4].contains(&BOTTOM));
        assert!(st.sub_super[4].contains(&12), "live NF4 consequence must remain");
        assert!(!fresh.exhausted);
        assert_eq!(fresh.nodes.len(), 1);
        let witness = fresh.nodes[&(4, 8, 9)];
        assert!(st.edges[4].contains(&(8, witness)));
        assert!(st.sub_super[witness as usize].contains(&9));
        // A subsequent carrier scan must not repeatedly "redirect" the dead
        // source's canonical edges back to themselves (the Uberon-154 loop).
        for _ in 0..2 {
            assert_eq!(
                freshen_rooted_inverse_edges(
                    &HashSet::from_iter([2, 4, 6]),
                    &mut st,
                    &mut fresh,
                    &vec![HashSet::default(); 9],
                ),
                0,
            );
        }
        // Learning bottom later must not replace a previously issued identity.
        st.add_sub(4, BOTTOM);
        assert_eq!(fresh.target(&mut st, 4, 8, 9), witness);
    }

    #[test]
    fn rooted_trace_blames_existential_source_before_successor_choice() {
        // Root 1 reaches bottom because its R-successor 2 is dead. Both nodes
        // carry direct repair choices, but banning the target-local choice can
        // repeat once per generated successor. The source choice that enabled
        // the existential is the causal and reusable conflict.
        let qbottom = 25;
        let source_guard = 9;
        let distracting_local_choice = 10;
        let role = 8;
        let mut it = Interner::new();
        for id in 2..32u32 {
            let name = match id {
                2 => "__cert_witness__f_Q_GEN_0".to_owned(),
                9 => "Q_GEN".to_owned(),
                _ => format!("X_{id}"),
            };
            assert_eq!(it.intern(&name), id);
        }
        let st = state_of(
            32,
            &[
                (
                    1,
                    &[source_guard, distracting_local_choice, qbottom, BOTTOM],
                ),
                (2, &[BOTTOM]),
            ],
            &[(1, role, 2)],
        );
        let nfs = Nfs {
            nf1: vec![Nf1 {
                sub: distracting_local_choice,
                sup: qbottom,
            }],
            nf2: Vec::new(),
            nf3: vec![Nf3 {
                sub: source_guard,
                role,
                filler: BOTTOM,
            }],
            nf4: vec![Nf4 {
                role,
                filler: BOTTOM,
                sup: qbottom,
            }],
            nf5: vec![qbottom],
            nf6: Vec::new(),
            nf7: Vec::new(),
            reflexive_roles: HashSet::default(),
            concept_names: HashSet::default(),
            role_names: HashSet::default(),
            conjunction_origins: HashMap::default(),
        };
        let prov = HashMap::from_iter([
            ((1, source_guard), 3),
            ((2, BOTTOM), 4),
            ((1, distracting_local_choice), 5),
        ]);
        let mut repr: Vec<u32> = (0..32).collect();
        let mut seen = HashSet::default();
        let trace = RepairTraceIdx::new(&nfs);
        let exhausted = HashSet::from_iter([
            (1, 3, u32::MAX),
            (2, 4, u32::MAX),
            (1, 5, u32::MAX),
        ]);
        assert_eq!(
            trace_repair_choice(
                1,
                BOTTOM,
                &st,
                &nfs,
                &trace,
                &it,
                &mut repr,
                &prov,
                &exhausted,
                &mut seen,
                16,
            ),
            None,
            "the ordinary trace must respect exhausted search frontiers",
        );
        seen.clear();
        assert_eq!(
            trace_repair_choice(
                1,
                BOTTOM,
                &st,
                &nfs,
                &trace,
                &it,
                &mut repr,
                &prov,
                &HashSet::default(),
                &mut seen,
                16,
            ),
            Some((1, 3, source_guard)),
        );
    }

    #[test]
    fn rooted_publication_emits_only_the_checked_subject() {
        let _lock = ROOTED_ENV_LOCK.lock().expect("rooted environment lock");
        let _cert = EnvRestore::set("KM_ELC_CERT", "2");
        let _domain = EnvRestore::set("KM_ELC_REPAIR_ROOT_DOMAIN", "1");
        let _publish = EnvRestore::set("KM_ELC_REPAIR_ROOT_PUBLISH", "1");
        let _preserve = EnvRestore::set("KM_ELC_PRESERVE", "C");

        // The residual cover is satisfied at C by its already-derived A label.
        // The rooted certificate checks C only; A, B, and D are deliberately
        // outside its claim even though the EL lower bound contains their rows.
        let cs = clauses(&format!(
            "[{},{},{},{}]",
            cl(&[c("C", "x")], &[c("A", "x")]),
            cl(&[c("A", "x")], &[c("D", "x")]),
            cl(&[], &[c("A", "x"), c("B", "x")]),
            cl(&[c("A", "x"), c("B", "x")], &[]),
        ));
        let result = classify(cs).expect("rooted certificate should publish C");

        assert_eq!(
            result
                .subsumptions
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            vec!["C"]
        );
        assert_eq!(
            result.subsumptions["C"]
                .iter()
                .cloned()
                .collect::<std::collections::BTreeSet<_>>(),
            std::collections::BTreeSet::from(["A".to_string(), "D".to_string()])
        );
        assert!(!result.unresolved.iter().any(|name| name == "C"));
        for name in ["A", "B", "D"] {
            assert!(
                result
                    .unresolved
                    .iter()
                    .any(|unresolved| unresolved == name),
                "unchecked subject {name} must remain unresolved"
            );
            assert!(!result.subsumptions.contains_key(name));
        }
        assert!(!result.inconsistent);
    }

    #[test]
    fn rooted_batch_reuses_one_fixpoint_but_certifies_each_subject() {
        let _lock = ROOTED_ENV_LOCK.lock().expect("rooted environment lock");
        let preserve_file = std::env::temp_dir().join(format!(
            "km-root-batch-{}-{}.txt",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        std::fs::write(&preserve_file, "C\nE\n").expect("write preserve fixture");
        let _cert = EnvRestore::set("KM_ELC_CERT", "2");
        let _domain = EnvRestore::set("KM_ELC_REPAIR_ROOT_DOMAIN", "1");
        let _publish = EnvRestore::set("KM_ELC_REPAIR_ROOT_PUBLISH", "1");
        let _single = EnvRestore::remove("KM_ELC_PRESERVE");
        let _batch = EnvRestore::set(
            "KM_ELC_PRESERVE_FILE",
            preserve_file.to_str().expect("UTF-8 temporary path"),
        );

        let cs = clauses(&format!(
            "[{},{},{},{},{}]",
            cl(&[c("C", "x")], &[c("A", "x")]),
            cl(&[c("A", "x")], &[c("D", "x")]),
            cl(&[c("E", "x")], &[c("B", "x")]),
            cl(&[], &[c("A", "x"), c("B", "x")]),
            cl(&[c("A", "x"), c("B", "x")], &[]),
        ));
        let result = classify(cs).expect("both roots should certify independently");
        std::fs::remove_file(&preserve_file).expect("remove preserve fixture");

        assert_eq!(
            result
                .subsumptions
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            vec!["C", "E"]
        );
        assert!(result.subsumptions["C"].contains(&"A".to_string()));
        assert!(result.subsumptions["C"].contains(&"D".to_string()));
        assert_eq!(result.subsumptions["E"], vec!["B".to_string()]);
        assert!(!result
            .unresolved
            .iter()
            .any(|name| name == "C" || name == "E"));
        for name in ["A", "B", "D"] {
            assert!(result
                .unresolved
                .iter()
                .any(|unresolved| unresolved == name));
        }
        assert!(!result.inconsistent);
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
            worklist: Worklist::contextual(n),
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
    fn rooted_card_guide_enforces_only_nonempty_guarded_pins() {
        let mut clause = pin_apart(7, 11, 12);
        clause.pin_guards.push((0, 7, 0));
        let guide = CardGuide::new(&[clause]);
        let mut repr: Vec<u32> = (0..16).collect();
        let mut domain: HashSet<u32> = HashSet::default();
        domain.insert(5);
        let mut round = CardRound::default();

        let empty_guard = state_of(16, &[], &[]);
        round.resync_active(&guide, &mut repr, &empty_guard, &domain);
        assert!(guide.merge_legal(&round, &mut repr, 11, 12));

        let inhabited_guard = state_of(16, &[(5, &[7])], &[]);
        round.resync_active(&guide, &mut repr, &inhabited_guard, &domain);
        assert!(!guide.merge_legal(&round, &mut repr, 11, 12));
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
        let mut nfs = empty_nfs();
        for &(role, filler, sup) in nf4 {
            nfs.nf4.push(Nf4 { role, filler, sup });
        }
        nfs.role_names = (0..nroles).collect();
        let width = nf4
            .iter()
            .map(|&(role, filler, sup)| role.max(filler).max(sup) + 1)
            .max()
            .unwrap_or(0)
            .max(nroles);
        build_idx(&nfs, width as usize)
    }

    fn blank_state(n: usize) -> State {
        State {
            sub_super: vec![HashSet::default(); n],
            edges: vec![HashSet::default(); n],
            in_by_role: HashMap::default(),
            in_roles: vec![Vec::new(); n],
            prop: HashMap::default(),
            worklist: Worklist::contextual(n),
            sub_journal: None,
            edge_epoch: 0,
        }
    }

    /// A normal-form set with no axioms and an empty signature.
    fn empty_nfs() -> Nfs {
        Nfs {
            nf1: Vec::new(),
            nf2: Vec::new(),
            nf3: Vec::new(),
            nf4: Vec::new(),
            nf5: Vec::new(),
            nf6: Vec::new(),
            nf7: Vec::new(),
            reflexive_roles: HashSet::default(),
            concept_names: HashSet::default(),
            role_names: HashSet::default(),
            conjunction_origins: HashMap::default(),
        }
    }

    fn lazy_complement_fixture() -> (Vec<RClause>, Nfs, HashSet<u32>, Interner, u32, u32, u32) {
        let mut it = Interner::new();
        let positive = it.intern("A");
        let negative = it.intern("Q_1");
        let source = it.intern("Source");
        let role = it.intern("R");
        let consequence = it.intern("Consequence");
        let cover = RClause {
            nvars: 1,
            origins: Vec::new(),
            body: Vec::new(),
            head: vec![
                RAtom::C {
                    cid: positive,
                    v: 0,
                },
                RAtom::C {
                    cid: negative,
                    v: 0,
                },
            ],
            pins: Vec::new(),
            pin_guards: Vec::new(),
        };
        let mut nfs = empty_nfs();
        nfs.nf2.push(Nf2 {
            sub1: positive,
            sub2: negative,
            sup: BOTTOM,
        });
        // The explicit existential witness is allowed to carry Q_1.
        nfs.nf3.push(Nf3 {
            sub: source,
            role,
            filler: negative,
        });
        // Q_1 is otherwise observed only as the target test in ∃R.Q_1 ⊑ C.
        nfs.nf4.push(Nf4 {
            role,
            filler: negative,
            sup: consequence,
        });
        let known_bottom = [BOTTOM].into_iter().collect();
        (vec![cover], nfs, known_bottom, it, positive, negative, role)
    }

    #[test]
    fn lazy_complement_recognizer_accepts_only_the_regular_fragment() {
        let (rcs, mut nfs, known_bottom, it, positive, negative, role) = lazy_complement_fixture();
        // An unrelated conjunction must not reject the candidate. This pins
        // the boolean grouping in the NF2 occurrence check.
        nfs.nf2.push(Nf2 {
            sub1: positive,
            sub2: TOP,
            sup: positive,
        });
        let found = regular_lazy_complements(&rcs, &nfs, &known_bottom, &it);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].cover_clause, 0);
        assert_eq!((found[0].positive, found[0].negative), (positive, negative));
        assert_eq!(
            found[0].consumers.get(&role),
            Some(&vec![it.id("Consequence").unwrap()])
        );

        // Uberon keeps the exact disjointness as an empty-head residual rather
        // than an NF2-to-bottom rule. That single occurrence is equivalent and
        // is the only additional residual occurrence this fragment accepts.
        let (mut residual_rcs, mut residual_nfs, _, residual_it, _, _, _) =
            lazy_complement_fixture();
        residual_nfs.nf2.clear();
        residual_rcs.push(RClause {
            nvars: 1,
            origins: Vec::new(),
            body: vec![
                RAtom::C {
                    cid: positive,
                    v: 0,
                },
                RAtom::C {
                    cid: negative,
                    v: 0,
                },
            ],
            head: Vec::new(),
            pins: Vec::new(),
            pin_guards: Vec::new(),
        });
        assert_eq!(
            regular_lazy_complements(&residual_rcs, &residual_nfs, &known_bottom, &residual_it)
                .len(),
            1
        );

        // Explicit producers remain ordinary EL rules. A local NF2 consumer
        // is recorded for sparse rooted firing; this is Uberon's Q_3 shape.
        let (producer_rcs, mut producer_nfs, _, producer_it, _, _, _) = lazy_complement_fixture();
        let producer = producer_it.id("Source").unwrap();
        let guard = producer_it.id("Consequence").unwrap();
        producer_nfs.nf1.push(Nf1 {
            sub: producer,
            sup: negative,
        });
        producer_nfs.nf2.push(Nf2 {
            sub1: guard,
            sub2: negative,
            sup: producer,
        });
        let producer_found =
            regular_lazy_complements(&producer_rcs, &producer_nfs, &known_bottom, &producer_it);
        assert_eq!(producer_found.len(), 1);
        assert_eq!(producer_found[0].local_consumers, vec![(guard, producer)]);

        let rejects = |mut bad: Nfs| {
            assert!(
                regular_lazy_complements(&rcs, &bad, &known_bottom, &it).is_empty(),
                "an unsupported occurrence of the negative definer was accepted"
            );
            // Keep the closure's argument observably mutable so each caller
            // supplies an independent fixture rather than sharing state.
            bad.nf1.clear();
        };

        let (_, mut bad, _, _, _, _, _) = lazy_complement_fixture();
        bad.nf1.push(Nf1 {
            sub: negative,
            sup: positive,
        });
        rejects(bad);
        let (_, mut bad, _, _, _, _, _) = lazy_complement_fixture();
        bad.nf3.push(Nf3 {
            sub: negative,
            role,
            filler: positive,
        });
        rejects(bad);
        let (_, mut bad, _, _, _, _, _) = lazy_complement_fixture();
        bad.nf5.push(negative);
        rejects(bad);

        let (mut bad_rcs, good, _, _, _, _, _) = lazy_complement_fixture();
        bad_rcs.push(RClause {
            nvars: 1,
            origins: Vec::new(),
            body: vec![RAtom::C {
                cid: negative,
                v: 0,
            }],
            head: vec![RAtom::C {
                cid: positive,
                v: 0,
            }],
            pins: Vec::new(),
            pin_guards: Vec::new(),
        });
        assert!(regular_lazy_complements(&bad_rcs, &good, &known_bottom, &it).is_empty());
    }

    #[test]
    fn lazy_complement_fires_only_observable_rooted_consumers() {
        let (rcs, mut nfs, known_bottom, mut it, positive, negative, role) =
            lazy_complement_fixture();
        // Isolate implicit-target firing here. The recognizer test separately
        // proves that an explicit NF3 negative witness is allowed.
        nfs.nf3.clear();
        let source = it.id("Source").unwrap();
        let consequence = it.id("Consequence").unwrap();
        let local = it.intern("LocalConsequence");
        nfs.nf2.push(Nf2 {
            sub1: source,
            sub2: negative,
            sup: local,
        });
        nfs.concept_names = [TOP, BOTTOM, positive, negative, source, consequence, local]
            .into_iter()
            .collect();
        nfs.role_names.insert(role);
        let lazy = regular_lazy_complements(&rcs, &nfs, &known_bottom, &it);
        let idx = build_idx(&nfs, it.len());
        let mut st = init_state(&nfs, it.len());
        run(&idx, &mut st, &mut Prof::default());

        // `consequence` is an ordinary target with no A label. The implicit
        // complement must fire ∃R.Q_1 ⊑ Consequence at the source without
        // storing Q_1 on this globally shared target.
        st.add_edge(source, role, consequence);
        run(&idx, &mut st, &mut Prof::default());
        assert!(!st.sub_super[consequence as usize].contains(&negative));
        assert!(!st.sub_super[source as usize].contains(&consequence));
        let domain = [source, negative, consequence].into_iter().collect();
        let mut repr: Vec<u32> = (0..it.len() as u32).collect();
        let banned = HashSet::default();
        let mut prov = HashMap::default();
        let mut chrono = Vec::new();
        assert_eq!(
            fire_lazy_complement_consumers(
                &lazy,
                &domain,
                &mut st,
                &mut repr,
                &nfs,
                &known_bottom,
                &banned,
                &mut prov,
                &mut chrono,
                true,
                &it,
            ),
            2
        );
        run(&idx, &mut st, &mut Prof::default());
        assert!(!st.sub_super[consequence as usize].contains(&negative));
        assert!(st.sub_super[source as usize].contains(&consequence));
        assert!(st.sub_super[source as usize].contains(&local));
        assert_eq!(
            fire_lazy_complement_consumers(
                &lazy,
                &domain,
                &mut st,
                &mut repr,
                &nfs,
                &known_bottom,
                &banned,
                &mut prov,
                &mut chrono,
                true,
                &it,
            ),
            0,
            "the sparse closure reaches a fixpoint"
        );

        // A positive target is outside Q's complement and is never labelled Q.
        st.add_sub(positive, positive);
        st.add_edge(source, role, positive);
        run(&idx, &mut st, &mut Prof::default());
        assert_eq!(
            fire_lazy_complement_consumers(
                &lazy,
                &domain,
                &mut st,
                &mut repr,
                &nfs,
                &known_bottom,
                &banned,
                &mut prov,
                &mut chrono,
                true,
                &it,
            ),
            0
        );
        assert!(!st.sub_super[positive as usize].contains(&negative));
    }

    #[test]
    fn lazy_complement_prefers_exact_positive_cover_before_known_bottom() {
        let (rcs, mut nfs, known_bottom, mut it, positive, _negative, role) =
            lazy_complement_fixture();
        let source = it.id("Source").unwrap();
        let consequence = it.id("Consequence").unwrap();
        let target = it.intern("Target");
        let guard = it.intern("Guard");
        nfs.nf2.push(Nf2 {
            sub1: consequence,
            sub2: guard,
            sup: BOTTOM,
        });
        nfs.concept_names.extend([target, guard]);
        let lazy = regular_lazy_complements(&rcs, &nfs, &known_bottom, &it);
        assert_eq!(lazy.len(), 1);
        let mut st = init_state(&nfs, it.len());
        st.add_edge(source, role, target);
        let domain = [source, target].into_iter().collect();
        let mut repr: Vec<u32> = (0..it.len() as u32).collect();
        let banned = HashSet::default();
        let mut prov = HashMap::default();
        let mut chrono = Vec::new();

        assert_eq!(
            fire_lazy_complement_consumers(
                &lazy,
                &domain,
                &mut st,
                &mut repr,
                &nfs,
                &known_bottom,
                &banned,
                &mut prov,
                &mut chrono,
                true,
                &it,
            ),
            1
        );
        assert!(st.sub_super[target as usize].contains(&positive));
        assert!(!st.sub_super[source as usize].contains(&consequence));
        assert_eq!(prov.get(&(target, positive)), Some(&0));
        assert_eq!(chrono, vec![(target, 0, positive)]);
    }

    #[test]
    fn lazy_local_complement_consumer_is_deferred_before_known_bottom() {
        let (rcs, mut nfs, known_bottom, mut it, positive, negative, _role) =
            lazy_complement_fixture();
        let source = it.id("Source").unwrap();
        let consequence = it.id("Consequence").unwrap();
        let sibling = it.intern("LaterSibling");
        nfs.nf2.push(Nf2 {
            sub1: source,
            sub2: negative,
            sup: consequence,
        });
        nfs.nf2.push(Nf2 {
            sub1: consequence,
            sub2: sibling,
            sup: BOTTOM,
        });
        nfs.concept_names.extend([source, sibling]);
        let lazy = regular_lazy_complements(&rcs, &nfs, &known_bottom, &it);
        assert_eq!(lazy.len(), 1);
        assert!(lazy[0].local_consumers.contains(&(source, consequence)));
        let mut st = init_state(&nfs, it.len());
        let domain = [source].into_iter().collect();
        let mut repr: Vec<u32> = (0..it.len() as u32).collect();
        let banned = HashSet::default();
        let mut prov = HashMap::default();
        let mut chrono = Vec::new();

        assert_eq!(
            fire_lazy_complement_consumers(
                &lazy,
                &domain,
                &mut st,
                &mut repr,
                &nfs,
                &known_bottom,
                &banned,
                &mut prov,
                &mut chrono,
                false,
                &it,
            ),
            0,
            "the choice-free scaffold must not commit the cyclic negative side"
        );
        assert!(!st.sub_super[source as usize].contains(&consequence));

        assert_eq!(
            fire_lazy_complement_consumers(
                &lazy,
                &domain,
                &mut st,
                &mut repr,
                &nfs,
                &known_bottom,
                &banned,
                &mut prov,
                &mut chrono,
                true,
                &it,
            ),
            1
        );
        assert!(st.sub_super[source as usize].contains(&positive));
        assert!(!st.sub_super[source as usize].contains(&consequence));
    }

    #[test]
    fn shared_nf1_nf2_bucket_preserves_the_serial_horn_closure() {
        const ROOT: u32 = 2;
        const A: u32 = 3;
        const B: u32 = 4;
        const D: u32 = 5;
        const E: u32 = 6;
        const F: u32 = 7;
        let nfs = Nfs {
            // A ⊑ B and B ⊑ D. Each NF1 conclusion is inserted before
            // the NF2 candidates in that same trigger bucket are inspected.
            nf1: vec![Nf1 { sub: A, sup: B }, Nf1 { sub: B, sup: D }],
            // A ⊓ B ⊑ E and B ⊓ D ⊑ F exercise both symmetric
            // NF2 entries, including candidates made true by the preceding NF1.
            nf2: vec![
                Nf2 {
                    sub1: A,
                    sub2: B,
                    sup: E,
                },
                Nf2 {
                    sub1: B,
                    sub2: D,
                    sup: F,
                },
            ],
            nf3: Vec::new(),
            nf4: Vec::new(),
            nf5: Vec::new(),
            nf6: Vec::new(),
            nf7: Vec::new(),
            reflexive_roles: HashSet::default(),
            concept_names: HashSet::default(),
            role_names: HashSet::default(),
            conjunction_origins: HashMap::default(),
        };
        let idx = build_idx(&nfs, 8);
        assert_eq!(idx.rule_count(), 3);
        let a_rules = idx.rules_of(A).expect("A triggers NF1 and NF2");
        assert_eq!(a_rules.nf1_sups, &[B]);
        assert_eq!(a_rules.nf2_cand, &[[B, E]]);
        assert!(idx.rules_of(ROOT).is_none());
        assert!(!idx.has_nf4);

        let mut st = blank_state(8);
        st.add_sub(ROOT, A);
        let mut prof = Prof::default();
        run(&idx, &mut st, &mut prof);

        for sup in [A, B, D, E, F] {
            assert!(
                st.sub_super[ROOT as usize].contains(&sup),
                "ROOT ⊑ {sup} missing"
            );
        }
        assert_eq!(prof.nf1_scan, 2);
        assert_eq!(prof.nf2_scan, 4);
    }

    #[test]
    fn nf2_join_fires_in_both_arrival_orders_from_either_side() {
        // One ordinary conjunction A ⊓ B ⊑ E, plus a hub H that is an operand
        // of 64 conjunctions H ⊓ X_i ⊑ E_i. The hub's candidate list is far
        // longer than any label here, so a Sub(_, H) item takes the
        // label-side join while every other item takes the direct scan. Both
        // must fire exactly the conjunctions whose partner is present,
        // whichever operand arrives second.
        const ROOT: u32 = 2;
        const A: u32 = 3;
        const B: u32 = 4;
        const E: u32 = 5;
        const H: u32 = 6;
        const FIRST_X: u32 = 7;
        const FIRST_E: u32 = FIRST_X + 64;
        let mut nfs = empty_nfs();
        nfs.nf2.push(Nf2 {
            sub1: A,
            sub2: B,
            sup: E,
        });
        for i in 0..64 {
            nfs.nf2.push(Nf2 {
                sub1: H,
                sub2: FIRST_X + i,
                sup: FIRST_E + i,
            });
        }
        let n = (FIRST_E + 64) as usize;
        let idx = build_idx(&nfs, n);
        assert_eq!(idx.rules_of(H).map(|r| r.nf2_cand.len()), Some(64));
        assert_eq!(
            idx.rules_of(FIRST_X + 3).map(|r| r.nf2_cand),
            Some(&[[H, FIRST_E + 3]][..])
        );

        // Direct scan, both arrival orders.
        for (first, second) in [(A, B), (B, A)] {
            let mut st = blank_state(n);
            st.add_sub(ROOT, first);
            run(&idx, &mut st, &mut Prof::default());
            assert!(!st.sub_super[ROOT as usize].contains(&E));
            st.add_sub(ROOT, second);
            let mut prof = Prof::default();
            run(&idx, &mut st, &mut prof);
            assert!(st.sub_super[ROOT as usize].contains(&E));
            assert_eq!(prof.nf2_label_side, 0);
        }
        // Partner first, hub second: the hub item joins from the label.
        let mut st = blank_state(n);
        st.add_sub(ROOT, FIRST_X + 3);
        run(&idx, &mut st, &mut Prof::default());
        assert!(!st.sub_super[ROOT as usize].contains(&(FIRST_E + 3)));
        st.add_sub(ROOT, H);
        let mut prof = Prof::default();
        run(&idx, &mut st, &mut prof);
        assert!(st.sub_super[ROOT as usize].contains(&(FIRST_E + 3)));
        assert_eq!(prof.nf2_label_side, 1);
        // Exactly the one conjunction whose partner is present fired.
        assert_eq!(st.sub_super[ROOT as usize].len(), 3);
        // Hub first, partner second: the partner's short list is scanned.
        let mut st = blank_state(n);
        st.add_sub(ROOT, H);
        let mut prof = Prof::default();
        run(&idx, &mut st, &mut prof);
        assert_eq!(prof.nf2_label_side, 1);
        assert_eq!(st.sub_super[ROOT as usize].len(), 1);
        st.add_sub(ROOT, FIRST_X + 3);
        let mut prof = Prof::default();
        run(&idx, &mut st, &mut prof);
        assert!(st.sub_super[ROOT as usize].contains(&(FIRST_E + 3)));
        assert_eq!(prof.nf2_label_side, 0);
        assert_eq!(st.sub_super[ROOT as usize].len(), 3);
    }

    /// The record a direct filter of the normal forms gives for `d`: NF1
    /// conclusions and NF3 pairs in axiom order, NF2 candidates (from both
    /// operand positions) and NF4 axioms sorted, and the NF5 flag; `None`
    /// when `d` triggers nothing.
    #[allow(clippy::type_complexity)]
    fn direct_rules(
        nfs: &Nfs,
        d: u32,
    ) -> Option<(Vec<u32>, Vec<[u32; 2]>, Vec<[u32; 2]>, Vec<[u32; 2]>, bool)> {
        let nf1: Vec<u32> = nfs
            .nf1
            .iter()
            .filter(|a| a.sub == d)
            .map(|a| a.sup)
            .collect();
        let mut nf2: Vec<[u32; 2]> = Vec::new();
        for a in &nfs.nf2 {
            if a.sub1 == d {
                nf2.push([a.sub2, a.sup]);
            }
            if a.sub2 == d {
                nf2.push([a.sub1, a.sup]);
            }
        }
        nf2.sort_unstable();
        let nf3: Vec<[u32; 2]> = nfs
            .nf3
            .iter()
            .filter(|a| a.sub == d)
            .map(|a| [a.role, a.filler])
            .collect();
        let mut nf4: Vec<[u32; 2]> = nfs
            .nf4
            .iter()
            .filter(|a| a.filler == d)
            .map(|a| [a.role, a.sup])
            .collect();
        nf4.sort_unstable();
        let bottom = nfs.nf5.contains(&d);
        if nf1.is_empty() && nf2.is_empty() && nf3.is_empty() && nf4.is_empty() && !bottom {
            None
        } else {
            Some((nf1, nf2, nf3, nf4, bottom))
        }
    }

    /// Every record of the pooled index equals the direct construction, entry
    /// for entry and in the same order; records are packed back to back in
    /// ascending trigger order and account for the whole pool.
    fn assert_pool_matches_direct(nfs: &Nfs, n: usize) {
        let idx = build_idx(nfs, n);
        let width = idx.rule_slot.len();
        assert!(width >= n);
        let mut records = 0usize;
        let mut next = 0usize;
        for d in 0..width as u32 {
            match (direct_rules(nfs, d), idx.rules_of(d)) {
                (None, None) => {}
                (Some((nf1, nf2, nf3, nf4, bottom)), Some(rules)) => {
                    assert_eq!(rules.nf1_sups, &nf1[..], "NF1 of {d}");
                    assert_eq!(rules.nf2_cand, &nf2[..], "NF2 of {d}");
                    assert_eq!(rules.nf3_edges, &nf3[..], "NF3 of {d}");
                    assert_eq!(rules.nf4_axioms, &nf4[..], "NF4 of {d}");
                    assert_eq!(rules.bottom, bottom, "NF5 of {d}");
                    let slot = idx.rule_slot[d as usize] as usize;
                    assert_eq!(slot, next, "record of {d} is not packed");
                    next = slot
                        + RULE_HEADER_WORDS
                        + nf1.len()
                        + 2 * (nf2.len() + nf3.len() + nf4.len());
                    records += 1;
                }
                (direct, pooled) => panic!(
                    "trigger {d}: direct record {} but pooled record {}",
                    direct.is_some(),
                    pooled.is_some()
                ),
            }
        }
        assert_eq!(records, idx.rule_count());
        assert_eq!(next, idx.pool.len());
        assert!(idx.rules_of(width as u32).is_none());
        assert!(idx.rules_of(u32::MAX).is_none());
        assert_eq!(idx.has_nf4, !nfs.nf4.is_empty());
    }

    #[test]
    fn pooled_rule_index_matches_a_direct_per_trigger_construction() {
        for seed in 0..32 {
            let (nfs, n) = random_terminology(seed);
            assert_pool_matches_direct(&nfs, n);
        }
        for seed in 0..4 {
            let (nfs, n) = stress_terminology(seed, 96);
            assert_pool_matches_direct(&nfs, n);
        }
        // An empty terminology has no records and an `n`-wide slot table.
        let idx = build_idx(&empty_nfs(), 5);
        assert_eq!(idx.rule_count(), 0);
        assert!(idx.pool.is_empty());
        assert_eq!(idx.rule_slot.len(), 5);
    }

    #[test]
    fn pooled_rule_index_keeps_flag_only_and_duplicate_records() {
        const A: u32 = 2;
        const B: u32 = 3;
        const E: u32 = 4;
        const F: u32 = 5;
        const R: u32 = 6;
        const WIDE: u32 = 12;
        let mut nfs = empty_nfs();
        nfs.role_names.insert(R);
        // A ⊑ ⊥ alone: a header-only record carrying the NF5 flag.
        nfs.nf5.push(A);
        // B ⊓ B ⊑ E registers under B from both operand positions.
        nfs.nf2.push(Nf2 {
            sub1: B,
            sub2: B,
            sup: E,
        });
        // A repeated NF3 axiom keeps both entries, in axiom order.
        for _ in 0..2 {
            nfs.nf3.push(Nf3 {
                sub: A,
                role: R,
                filler: F,
            });
        }
        // A trigger beyond `n` widens the slot table, as before.
        nfs.nf1.push(Nf1 { sub: WIDE, sup: A });
        let n = (R + 1) as usize;
        let idx = build_idx(&nfs, n);
        let a = idx.rules_of(A).expect("A triggers NF5 and NF3");
        assert!(a.bottom);
        assert!(a.nf1_sups.is_empty());
        assert!(a.nf2_cand.is_empty());
        assert_eq!(a.nf3_edges, &[[R, F], [R, F]]);
        assert!(a.nf4_axioms.is_empty());
        let b = idx.rules_of(B).expect("B triggers NF2");
        assert!(!b.bottom);
        assert_eq!(b.nf2_cand, &[[B, E], [B, E]]);
        assert_eq!(idx.rules_of(WIDE).map(|r| r.nf1_sups), Some(&[A][..]));
        assert_eq!(idx.rule_slot.len(), WIDE as usize + 1);
        assert_eq!(idx.rule_count(), 3);
        assert!(idx.rules_of(E).is_none());
        assert!(idx.rules_of(F).is_none());
        assert_pool_matches_direct(&nfs, n);
    }

    #[test]
    fn interner_distinguishes_long_names_at_every_chunk_boundary() {
        // The hasher folds 8-byte words, then a 4-byte half, then single
        // bytes. Names differing inside each of those regions, and names of
        // lengths 8k, 8k+1..3, 8k+4, 8k+5.., must stay distinct symbols while
        // the same spelling always maps back to its first id.
        let mut it = Interner::new();
        let base = "http://example.org/onto#ClassNumber0123456789";
        let mut names: Vec<String> = vec![base.to_string()];
        for cut in [0usize, 5, 8, 12, 15, 16, 20, 23] {
            let mut s = base.to_string();
            s.replace_range(cut..cut + 1, "Z");
            names.push(s);
        }
        for len in [8usize, 9, 11, 12, 13, 16, 17] {
            names.push(base[..len].to_string());
        }
        let ids: Vec<u32> = names.iter().map(|s| it.intern(s)).collect();
        for (i, name) in names.iter().enumerate() {
            assert_eq!(it.intern(name), ids[i], "re-interning {name}");
            assert_eq!(it.name(ids[i]), name.as_str());
            assert_eq!(it.id(name), Some(ids[i]));
        }
        let mut sorted = ids.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), names.len(), "distinct spellings share an id");
        assert_eq!(it.len(), 2 + names.len());
    }

    #[test]
    fn interner_shares_symbol_storage_and_preserves_external_names() {
        let mut it = Interner::new();
        let iri = "http://example.org/a/deliberately/long/concept/name";
        let id = it.intern(iri);
        let (forward_name, &forward_id) = it.map.get_key_value(iri).unwrap();
        assert_eq!(forward_id, id);
        assert!(Arc::ptr_eq(forward_name, &it.names[id as usize]));

        let names = it.into_names();
        assert_eq!(names[TOP as usize].as_ref(), "⊤");
        assert_eq!(names[BOTTOM as usize].as_ref(), "⊥");
        assert_eq!(names[id as usize].as_ref(), iri);
    }

    /// Deterministic xorshift64* stream for the random differential fixtures.
    struct Rng(u64);

    impl Rng {
        fn step(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }

        fn below(&mut self, n: u32) -> u32 {
            (self.step() % u64::from(n)) as u32
        }
    }

    /// A small random EL++ terminology over disjoint concept and role id
    /// ranges (as the interner lays them out), using every normal form the
    /// completion implements: NF1-NF7, a domain-style `∃R.⊤` filler, a
    /// reflexive role, and one conjunction hub whose candidate list exceeds
    /// eight times any label these terminologies can grow, so the label-side
    /// NF2 join is exercised alongside the direct scan.
    fn random_terminology(seed: u64) -> (Nfs, usize) {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
        let nc = 6 + rng.below(7);
        let nr = 2 + rng.below(2);
        let first_role = 2 + nc;
        let n = (first_role + nr) as usize;
        let mut nfs = empty_nfs();
        nfs.concept_names = (2..first_role).collect();
        nfs.concept_names.insert(TOP);
        nfs.role_names = (first_role..first_role + nr).collect();
        let concept = |rng: &mut Rng| 2 + rng.below(nc);
        let role = |rng: &mut Rng| first_role + rng.below(nr);
        for _ in 0..nc {
            nfs.nf1.push(Nf1 {
                sub: concept(&mut rng),
                sup: concept(&mut rng),
            });
        }
        for _ in 0..nc / 2 {
            nfs.nf2.push(Nf2 {
                sub1: concept(&mut rng),
                sub2: concept(&mut rng),
                sup: concept(&mut rng),
            });
        }
        let hub = concept(&mut rng);
        for _ in 0..64 {
            nfs.nf2.push(Nf2 {
                sub1: hub,
                sub2: concept(&mut rng),
                sup: concept(&mut rng),
            });
        }
        for _ in 0..nc / 2 {
            nfs.nf3.push(Nf3 {
                sub: concept(&mut rng),
                role: role(&mut rng),
                filler: concept(&mut rng),
            });
        }
        for _ in 0..nc / 2 {
            let filler = if rng.below(4) == 0 {
                TOP
            } else {
                concept(&mut rng)
            };
            nfs.nf4.push(Nf4 {
                role: role(&mut rng),
                filler,
                sup: concept(&mut rng),
            });
        }
        if rng.below(3) == 0 {
            let sub = concept(&mut rng);
            nfs.nf5.push(sub);
        }
        for _ in 0..rng.below(3) {
            nfs.nf6.push(Nf6 {
                sub: role(&mut rng),
                sup: role(&mut rng),
            });
        }
        if rng.below(2) == 0 {
            nfs.nf7.push(Nf7 {
                r1: role(&mut rng),
                r2: role(&mut rng),
                sup: role(&mut rng),
            });
        }
        if rng.below(3) == 0 {
            let reflexive = role(&mut rng);
            nfs.reflexive_roles.insert(reflexive);
        }
        (nfs, n)
    }

    /// Reference least fixpoint of the EL++ rule set over an `Nfs`, computed
    /// by naive rule-by-rule iteration over explicit fact sets: no indexes,
    /// no worklist, no scheduling. `n` bounds the symbol ids.
    fn naive_fixpoint(nfs: &Nfs, n: usize) -> (HashSet<(u32, u32)>, HashSet<(u32, u32, u32)>) {
        // Reflexive-transitive role closure of NF6 over the role signature.
        let mut supers: Vec<HashSet<u32>> = vec![HashSet::default(); n];
        for &r in &nfs.role_names {
            supers[r as usize].insert(r);
        }
        let mut changed = true;
        while changed {
            changed = false;
            for a in &nfs.nf6 {
                let reach: Vec<u32> = supers[a.sup as usize].iter().copied().collect();
                for s in reach {
                    changed |= supers[a.sub as usize].insert(s);
                }
            }
        }
        let reflexive: HashSet<u32> = nfs
            .reflexive_roles
            .iter()
            .flat_map(|&r| supers[r as usize].iter().copied())
            .collect();
        let nf5: HashSet<u32> = nfs.nf5.iter().copied().collect();
        let mut sub: HashSet<(u32, u32)> = HashSet::default();
        let mut edge: HashSet<(u32, u32, u32)> = HashSet::default();
        for &c in &nfs.concept_names {
            if c == BOTTOM {
                continue;
            }
            sub.insert((c, c));
            sub.insert((c, TOP));
            for &r in &reflexive {
                edge.insert((c, r, c));
            }
        }
        let mut changed = true;
        while changed {
            changed = false;
            let subs: Vec<(u32, u32)> = sub.iter().copied().collect();
            let edges: Vec<(u32, u32, u32)> = edge.iter().copied().collect();
            for &(a, d) in &subs {
                for x in &nfs.nf1 {
                    if x.sub == d {
                        changed |= sub.insert((a, x.sup));
                    }
                }
                for x in &nfs.nf2 {
                    let both = (x.sub1 == d && sub.contains(&(a, x.sub2)))
                        || (x.sub2 == d && sub.contains(&(a, x.sub1)));
                    if both {
                        changed |= sub.insert((a, x.sup));
                    }
                }
                if nf5.contains(&d) {
                    changed |= sub.insert((a, BOTTOM));
                }
                for x in &nfs.nf3 {
                    if x.sub == d {
                        changed |= edge.insert((a, x.role, x.filler));
                    }
                }
            }
            for &(a, r, t) in &edges {
                if sub.contains(&(t, BOTTOM)) {
                    changed |= sub.insert((a, BOTTOM));
                }
                for x in &nfs.nf4 {
                    if x.role == r && sub.contains(&(t, x.filler)) {
                        changed |= sub.insert((a, x.sup));
                    }
                }
                for &s in &supers[r as usize] {
                    changed |= edge.insert((a, s, t));
                }
                for &(b, r2, u) in &edges {
                    if b != t {
                        continue;
                    }
                    for x in &nfs.nf7 {
                        if x.r1 == r && x.r2 == r2 {
                            for &s in &supers[x.sup as usize] {
                                changed |= edge.insert((a, s, u));
                            }
                        }
                    }
                }
            }
        }
        (sub, edge)
    }

    #[test]
    fn saturation_matches_the_naive_fixpoint_on_random_terminologies() {
        // Differential oracle for the indexed completion (`build_idx`, the
        // dense rule records, the min-side NF2 join, the backward-link guard
        // of the sub-side NF4 join, and `run`'s scheduling): 32 random
        // terminologies, each compared fact for fact against a naive
        // fixpoint over explicit sets.
        let mut label_side_joins = 0u64;
        for seed in 1..=32u64 {
            let (nfs, n) = random_terminology(seed);
            let idx = build_idx(&nfs, n);
            let mut st = init_state(&nfs, n);
            seed_reflexive_edges(&nfs, &idx, &mut st);
            let mut prof = Prof::default();
            run(&idx, &mut st, &mut prof);
            label_side_joins += prof.nf2_label_side;
            let (want_sub, want_edge) = naive_fixpoint(&nfs, n);
            let mut got_sub: HashSet<(u32, u32)> = HashSet::default();
            for (c, sups) in st.sub_super.iter().enumerate() {
                for &d in sups {
                    got_sub.insert((c as u32, d));
                }
            }
            let mut got_edge: HashSet<(u32, u32, u32)> = HashSet::default();
            for (c, es) in st.edges.iter().enumerate() {
                for &(r, d) in es {
                    got_edge.insert((c as u32, r, d));
                }
            }
            assert_eq!(
                got_sub, want_sub,
                "seed {seed}: subsumption closure differs"
            );
            assert_eq!(got_edge, want_edge, "seed {seed}: edge closure differs");
        }
        assert!(
            label_side_joins > 0,
            "the hub never took the label-side join"
        );
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
        // The frontier batch is defined over the global FIFO.
        st.worklist = Worklist::fifo();
        for target in FIRST_TARGET..FIRST_TARGET + PAR_NF4_MIN_EDGES as u32 {
            st.prop.insert(
                (target, R),
                (0..128).map(|i| if i % 2 == 0 { E1 } else { E2 }).collect(),
            );
            st.worklist.push(Item::Edge(PARENT, R, target));
        }
        let mut prof = Prof::default();
        assert!(fire_edge_nf4_batch(&idx, &mut st, &mut prof, true));
        assert_eq!(prof.nf4_edge_scan, 128 * PAR_NF4_MIN_EDGES as u64);
        assert!(st.sub_super[PARENT as usize].contains(&E1));
        assert!(st.sub_super[PARENT as usize].contains(&E2));
        assert_eq!(st.sub_super[PARENT as usize].len(), 2);
        let pending = st.worklist.items();
        assert_eq!(
            pending
                .iter()
                .filter(|item| matches!(item, Item::EdgeAfterNf4(..)))
                .count(),
            PAR_NF4_MIN_EDGES
        );
        assert_eq!(
            pending
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
        st.worklist = Worklist::fifo();
        for target in FIRST_TARGET..FIRST_TARGET + PAR_NF4_MIN_EDGES as u32 {
            st.prop.insert((target, R), vec![SUP]);
            st.worklist.push(Item::Edge(PARENT, R, target));
        }
        let mut prof = Prof::default();
        assert!(fire_edge_nf4_batch(&idx, &mut st, &mut prof, true));
        assert_eq!(prof.nf4_batch_calls, 0);
        assert!(st
            .worklist
            .items()
            .iter()
            .all(|item| matches!(item, Item::EdgeSerial(..))));
        run(&idx, &mut st, &mut prof);
        assert!(st.sub_super[PARENT as usize].contains(&SUP));
        assert_eq!(prof.nf4_edge_scan, PAR_NF4_MIN_EDGES as u64);
        assert_eq!(prof.ctx_activations, 0);
    }

    #[test]
    fn frontier_batch_keeps_the_serial_join_on_the_contextual_worklist() {
        // The parallel frontier batch is defined over the global FIFO. On the
        // context-local worklist it declines without touching the queue, and
        // the ordinary edge-side join reaches the same closure in one
        // activation of the parent context.
        const R: u32 = 0;
        const PARENT: u32 = 2;
        const SUP: u32 = 3;
        const FIRST_TARGET: u32 = 10;
        let idx = nf4_only_idx(&[(R, FIRST_TARGET, SUP)], 1);
        let mut st = blank_state(300);
        assert!(matches!(st.worklist, Worklist::Contextual(_)));
        for target in FIRST_TARGET..FIRST_TARGET + PAR_NF4_MIN_EDGES as u32 {
            st.prop.insert((target, R), vec![SUP; 128]);
            st.worklist.push(Item::Edge(PARENT, R, target));
        }
        let mut prof = Prof::default();
        assert!(!fire_edge_nf4_batch(&idx, &mut st, &mut prof, true));
        assert_eq!(st.worklist.len(), PAR_NF4_MIN_EDGES);
        assert!(st
            .worklist
            .items()
            .iter()
            .all(|item| matches!(item, Item::Edge(..))));
        run(&idx, &mut st, &mut prof);
        assert_eq!(prof.nf4_batch_calls, 0);
        assert!(st.sub_super[PARENT as usize].contains(&SUP));
        assert_eq!(prof.nf4_edge_scan, 128 * PAR_NF4_MIN_EDGES as u64);
        assert_eq!(prof.ctx_activations, 1);
        assert!(st.worklist.is_empty());
    }

    #[test]
    fn contextual_worklist_drains_one_activated_context_at_a_time() {
        let mut wl = Worklist::contextual(8);
        assert!(wl.is_empty());
        assert_eq!(wl.pop(), None);
        wl.push(Item::Sub(3, 4));
        wl.push(Item::Sub(5, 6));
        wl.push(Item::Edge(3, 0, 7));
        assert_eq!(wl.len(), 3);
        assert_eq!(
            wl.items(),
            vec![Item::Edge(3, 0, 7), Item::Sub(3, 4), Item::Sub(5, 6)]
        );
        // Context 3 was activated first; its items come back newest first.
        assert_eq!(wl.pop(), Some(Item::Edge(3, 0, 7)));
        assert_eq!(wl.activations(), 1);
        // A conclusion the drain produces for its own context is processed
        // in the same activation, before any other context.
        wl.push(Item::Sub(3, 5));
        assert_eq!(wl.pop(), Some(Item::Sub(3, 5)));
        assert_eq!(wl.pop(), Some(Item::Sub(3, 4)));
        // The context is released only by the pop that finds it empty; that
        // pop moves on to the next activated context.
        assert_eq!(wl.pop(), Some(Item::Sub(5, 6)));
        assert_eq!(wl.activations(), 2);
        // A released context is re-activated by a later item, behind the
        // contexts already waiting; the current context keeps priority.
        wl.push(Item::Sub(3, 6));
        wl.push(Item::Sub(1, 2));
        wl.push(Item::Sub(5, 7));
        assert_eq!(wl.pop(), Some(Item::Sub(5, 7)));
        assert_eq!(wl.pop(), Some(Item::Sub(3, 6)));
        assert_eq!(wl.pop(), Some(Item::Sub(1, 2)));
        assert_eq!(wl.pop(), None);
        assert!(wl.is_empty());
        assert_eq!(wl.activations(), 4);
        // Freed slots are recycled: the arena holds the peak pending count.
        let Worklist::Contextual(queue) = &wl else {
            unreachable!("built contextual")
        };
        assert_eq!(queue.slots.len(), 3);
        // Symbols appended by an incremental transaction widen the queue.
        wl.grow(16);
        wl.push(Item::Sub(12, 1));
        assert_eq!(wl.pop(), Some(Item::Sub(12, 1)));
        assert_eq!(wl.pop(), None);
        wl.push(Item::Sub(1, 2));
        wl.push(Item::Sub(2, 3));
        wl.clear();
        assert!(wl.is_empty());
        assert_eq!(wl.pop(), None);
        wl.push(Item::Sub(2, 4));
        assert_eq!(wl.items(), vec![Item::Sub(2, 4)]);
        assert_eq!(wl.pop(), Some(Item::Sub(2, 4)));
        assert_eq!(wl.pop(), None);
        // A repair fork keeps the discipline and the symbol width.
        let forked = wl.new_like();
        assert!(forked.is_empty());
        let Worklist::Contextual(forked) = &forked else {
            unreachable!("forked contextual")
        };
        assert_eq!(forked.head.len(), 16);
        let fifo = Worklist::fifo();
        assert!(matches!(fifo.new_like(), Worklist::Fifo(_)));
        assert_eq!(fifo.activations(), 0);
    }

    #[test]
    fn contextual_scheduling_reaches_the_fifo_closure_on_random_terminologies() {
        // The two disciplines process the same items with the same rule
        // code: the closure, the item counts and the per-item scan counters
        // must agree, and only the contextual queue activates contexts.
        for seed in 1..=32u64 {
            let (nfs, n) = random_terminology(seed);
            let idx = build_idx(&nfs, n);
            let mut fifo = init_state_with(&nfs, n, Worklist::fifo());
            let mut contextual = init_state_with(&nfs, n, Worklist::contextual(n));
            seed_reflexive_edges(&nfs, &idx, &mut fifo);
            seed_reflexive_edges(&nfs, &idx, &mut contextual);
            let mut fifo_prof = Prof::default();
            let mut contextual_prof = Prof::default();
            run(&idx, &mut fifo, &mut fifo_prof);
            run(&idx, &mut contextual, &mut contextual_prof);
            assert_eq!(
                fifo.sub_super, contextual.sub_super,
                "seed {seed}: labels differ"
            );
            assert_eq!(fifo.edges, contextual.edges, "seed {seed}: edges differ");
            assert_eq!(
                fifo_prof.sub_items, contextual_prof.sub_items,
                "seed {seed}: subsumption items"
            );
            assert_eq!(
                fifo_prof.edge_items, contextual_prof.edge_items,
                "seed {seed}: edge items"
            );
            assert_eq!(
                fifo_prof.nf1_scan, contextual_prof.nf1_scan,
                "seed {seed}: NF1 scans"
            );
            assert_eq!(
                fifo_prof.nf3_scan, contextual_prof.nf3_scan,
                "seed {seed}: NF3 scans"
            );
            assert_eq!(fifo_prof.ctx_activations, 0);
            assert!(contextual_prof.ctx_activations > 0, "seed {seed}");
            assert!(
                contextual_prof.ctx_activations
                    <= contextual_prof.sub_items + contextual_prof.edge_items,
                "seed {seed}: an activation processes at least one item"
            );
            assert!(fifo.worklist.is_empty());
            assert!(contextual.worklist.is_empty());
        }
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
        let mut nfs = empty_nfs();
        for &(r1, r2, sup) in chains {
            nfs.nf7.push(Nf7 { r1, r2, sup });
        }
        nfs.role_names = (0..nroles).collect();
        let width = chains
            .iter()
            .map(|&(r1, r2, sup)| r1.max(r2).max(sup) + 1)
            .max()
            .unwrap_or(0)
            .max(nroles);
        build_idx(&nfs, width as usize)
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
            pin_guards: Vec::new(),
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
        assert!(
            idx.members[&A].len() >= 3,
            "the new members must be indexed"
        );
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
        assert!(
            !idx.nodes.contains(&Q),
            "the dead node must leave the domain"
        );
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
        let subs_moved = !st.sub_super[Q as usize]
            .iter()
            .eq(st.sub_super[P as usize].iter());
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
    fn base_check_index_refreshed_over_fork_matches_fresh_build() {
        let (rcs, names, mut st) = idx_fixture();
        const A: u32 = 2;
        const P: u32 = 4;
        st.sub_super[P as usize].insert(A);

        let mut base_idx = CertIdx::default();
        base_idx.refresh(&rcs, &names, &st.sub_super, &st.edges, None, st.edge_epoch);
        let mut fork = st.fork();
        fork.start_journal();
        let delta = fork.drain_journal();
        assert_eq!(delta.as_deref(), Some(&[][..]));
        base_idx.refresh(
            &rcs,
            &names,
            &fork.sub_super,
            &fork.edges,
            delta.as_deref(),
            fork.edge_epoch,
        );
        assert_same_idx(&base_idx, &rebuilt_idx(&rcs, &names, &fork));
        assert_same_idx(&base_idx, &rebuilt_idx(&rcs, &names, &st));
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
        let after =
            classify_inner(rewritten, CertMode::Off, false).expect("the rewritten set is pure EL");
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
        assert_eq!(
            left.join("/"),
            right.join("/"),
            "regression witness must collide"
        );
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

    // -----------------------------------------------------------------------
    // Context-parallel saturation
    // -----------------------------------------------------------------------

    /// Run `body` with the context-parallel worker count forced, without
    /// touching the process environment other tests read concurrently.
    fn with_par_workers<T>(workers: usize, body: impl FnOnce() -> T) -> T {
        TEST_PAR_WORKERS.with(|slot| slot.set(workers));
        let out = body();
        TEST_PAR_WORKERS.with(|slot| slot.set(0));
        out
    }

    /// The label relation in ITERATION order, which is what the classification
    /// output writes row by row. Equality of this rendering is the byte-level
    /// determinism the parallel engine has to provide; equality of the sets
    /// alone would not catch a run-dependent iteration order.
    fn label_order_digest(st: &State) -> String {
        let mut out = String::new();
        for (c, sups) in st.sub_super.iter().enumerate() {
            out.push_str(&format!("{c}:"));
            for &d in sups.iter() {
                out.push_str(&format!("{d},"));
            }
            out.push(';');
        }
        out
    }

    /// The state's fact sets, order-independent, for comparing two engines.
    fn state_facts(st: &State) -> (Vec<(u32, u32)>, Vec<(u32, u32, u32)>) {
        let mut subs: Vec<(u32, u32)> = Vec::new();
        for (c, sups) in st.sub_super.iter().enumerate() {
            for &d in sups {
                subs.push((c as u32, d));
            }
        }
        let mut edges: Vec<(u32, u32, u32)> = Vec::new();
        for (c, out) in st.edges.iter().enumerate() {
            for &(r, d) in out {
                edges.push((c as u32, r, d));
            }
        }
        subs.sort_unstable();
        edges.sort_unstable();
        (subs, edges)
    }

    /// The backward links and propagations, canonicalised: the parallel engine
    /// appends them in a different order but must build the same multisets.
    fn link_facts(st: &State) -> (Vec<(u32, u32, u32)>, Vec<(u32, u32, u32)>) {
        let mut links: Vec<(u32, u32, u32)> = Vec::new();
        for (&(d, r), parents) in st.in_by_role.iter() {
            for &p in parents {
                links.push((d, r, p));
            }
        }
        let mut props: Vec<(u32, u32, u32)> = Vec::new();
        for (&(c, r), sups) in st.prop.iter() {
            for &e in sups {
                props.push((c, r, e));
            }
        }
        links.sort_unstable();
        props.sort_unstable();
        (links, props)
    }

    /// A terminology big enough to spread over every shard and to force real
    /// cross-worker traffic: `size` concepts over four roles, with NF1 chains,
    /// a conjunction hub, existentials, NF4 axioms, a role inclusion, a role
    /// chain, an unsatisfiable concept and a reflexive role.
    fn stress_terminology(seed: u64, size: u32) -> (Nfs, usize) {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
        let nr = 4u32;
        let first_role = 2 + size;
        let n = (first_role + nr) as usize;
        let mut nfs = empty_nfs();
        nfs.concept_names = (2..first_role).collect();
        nfs.concept_names.insert(TOP);
        nfs.role_names = (first_role..first_role + nr).collect();
        let concept = |rng: &mut Rng| 2 + rng.below(size);
        let role = |rng: &mut Rng| first_role + rng.below(nr);
        for i in 0..size {
            // A chain plus a random edge, so the taxonomy is deep and the
            // conclusions travel between shards.
            nfs.nf1.push(Nf1 {
                sub: 2 + i,
                sup: 2 + (i + 1) % size,
            });
            nfs.nf1.push(Nf1 {
                sub: concept(&mut rng),
                sup: concept(&mut rng),
            });
        }
        let hub = concept(&mut rng);
        for _ in 0..64 {
            nfs.nf2.push(Nf2 {
                sub1: hub,
                sub2: concept(&mut rng),
                sup: concept(&mut rng),
            });
        }
        for _ in 0..size / 2 {
            nfs.nf2.push(Nf2 {
                sub1: concept(&mut rng),
                sub2: concept(&mut rng),
                sup: concept(&mut rng),
            });
            nfs.nf3.push(Nf3 {
                sub: concept(&mut rng),
                role: role(&mut rng),
                filler: concept(&mut rng),
            });
            nfs.nf4.push(Nf4 {
                role: role(&mut rng),
                filler: concept(&mut rng),
                sup: concept(&mut rng),
            });
        }
        nfs.nf5.push(concept(&mut rng));
        nfs.nf6.push(Nf6 {
            sub: first_role,
            sup: first_role + 1,
        });
        nfs.nf7.push(Nf7 {
            r1: first_role,
            r2: first_role + 1,
            sup: first_role + 2,
        });
        nfs.reflexive_roles.insert(first_role + 3);
        (nfs, n)
    }

    #[test]
    fn context_parallel_saturation_matches_the_serial_fixpoint() {
        // The sharded engine against the serial one (itself pinned to the
        // naive rule-by-rule fixpoint by
        // `saturation_matches_the_naive_fixpoint_on_random_terminologies`) on
        // the 32 random terminologies, at one, two, three and four workers.
        // One worker exercises the same rule split with every conclusion
        // delivered locally; more workers add the message paths.
        for seed in 1..=32u64 {
            let (nfs, n) = random_terminology(seed);
            let idx = build_idx(&nfs, n);
            let mut serial = init_state(&nfs, n);
            seed_reflexive_edges(&nfs, &idx, &mut serial);
            let mut serial_prof = Prof::default();
            run(&idx, &mut serial, &mut serial_prof);
            let (want_sub, want_edge) = naive_fixpoint(&nfs, n);
            let (serial_subs, serial_edges) = state_facts(&serial);
            let (serial_links, serial_props) = link_facts(&serial);
            for workers in [1usize, 2, 3, 4] {
                let mut prof = Prof::default();
                let st = run_context_parallel(&nfs, &idx, n, workers, &mut prof)
                    .expect("the worker threads start");
                let (subs, edges) = state_facts(&st);
                assert_eq!(subs, serial_subs, "seed {seed}, {workers} workers: labels");
                assert_eq!(edges, serial_edges, "seed {seed}, {workers} workers: edges");
                let got_sub: HashSet<(u32, u32)> = subs.iter().copied().collect();
                let got_edge: HashSet<(u32, u32, u32)> = edges.iter().copied().collect();
                assert_eq!(got_sub, want_sub, "seed {seed}, {workers} workers: closure");
                assert_eq!(got_edge, want_edge, "seed {seed}, {workers} workers: edges");
                // The role graph the rules join over is rebuilt identically,
                // link for link and propagation for propagation.
                let (links, props) = link_facts(&st);
                assert_eq!(links, serial_links, "seed {seed}, {workers} workers: links");
                assert_eq!(props, serial_props, "seed {seed}, {workers} workers: props");
                // Every fact is processed exactly once, by exactly one worker,
                // so the item counts and the per-item scans are invariant. The
                // two halves of the edge rules are counted separately and both
                // equal the number of derived edges.
                assert_eq!(prof.sub_items, serial_prof.sub_items, "seed {seed}");
                assert_eq!(prof.edge_items, serial_prof.edge_items, "seed {seed}");
                assert_eq!(prof.link_items, prof.edge_items, "seed {seed}");
                assert_eq!(prof.nf1_scan, serial_prof.nf1_scan, "seed {seed}");
                assert_eq!(prof.nf3_scan, serial_prof.nf3_scan, "seed {seed}");
                assert_eq!(prof.par_workers, workers as u64);
                assert_eq!(st.edge_epoch, serial.edge_epoch, "seed {seed}");
                assert!(st.worklist.is_empty());
                assert!(st.sub_journal.is_none());
                // Every context that received an item was activated.
                assert!(prof.ctx_activations > 0, "seed {seed}");
                assert!(
                    prof.ctx_activations <= prof.sub_items + prof.edge_items + prof.link_items,
                    "seed {seed}"
                );
            }
        }
    }

    #[test]
    fn context_parallel_labels_iterate_identically_for_every_worker_count() {
        // Byte-level determinism of the state the output is written from: the
        // label of a context iterates in the same order whatever the worker
        // count and whatever the interleaving, so the classification bytes do
        // not depend on either. Repeats catch a scheduling race that only
        // shows up on some interleavings.
        let (nfs, n) = stress_terminology(7, 256);
        let idx = build_idx(&nfs, n);
        let mut reference: Option<String> = None;
        let mut digest_len = 0usize;
        let mut facts: Option<(Vec<(u32, u32)>, Vec<(u32, u32, u32)>)> = None;
        for workers in [1usize, 2, 4, 3, 4, 2, 4, 1] {
            let mut prof = Prof::default();
            let st = run_context_parallel(&nfs, &idx, n, workers, &mut prof)
                .expect("the worker threads start");
            let digest = label_order_digest(&st);
            digest_len = digest.len();
            match &reference {
                None => reference = Some(digest),
                Some(want) => assert_eq!(&digest, want, "{workers} workers: label order"),
            }
            let got = state_facts(&st);
            match &facts {
                None => facts = Some(got),
                Some(want) => assert_eq!(&got, want, "{workers} workers: closure"),
            }
            if workers > 1 {
                // The shards really did exchange conclusions, so the run is a
                // test of the message paths and not of one local worker.
                assert!(prof.par_batches > 0, "{workers} workers: no batch sent");
                assert!(prof.par_messages > 0, "{workers} workers: no message sent");
            } else {
                assert_eq!(prof.par_batches, 0, "one worker sends no message");
            }
        }
        assert!(digest_len > 100_000, "the fixture is too small to race");
    }

    #[test]
    fn context_parallel_stress_matches_the_serial_fixpoint_over_repeated_runs() {
        // Volume plus repetition: four terminologies of a few hundred contexts
        // with every normal form live, each run four times at four workers
        // against the serial engine.
        for seed in 1..=4u64 {
            let (nfs, n) = stress_terminology(seed, 192);
            let idx = build_idx(&nfs, n);
            let mut serial = init_state(&nfs, n);
            seed_reflexive_edges(&nfs, &idx, &mut serial);
            let mut serial_prof = Prof::default();
            run(&idx, &mut serial, &mut serial_prof);
            let want = state_facts(&serial);
            let want_links = link_facts(&serial);
            // A closure worth racing over: tens of thousands of facts spread
            // across every shard, not a handful that one worker finishes
            // before the others have started.
            assert!(
                want.0.len() > 20_000 && want.1.len() > 1_000,
                "seed {seed}: {} subsumptions, {} edges",
                want.0.len(),
                want.1.len()
            );
            for round in 0..4 {
                let mut prof = Prof::default();
                let st = run_context_parallel(&nfs, &idx, n, 4, &mut prof)
                    .expect("the worker threads start");
                assert_eq!(state_facts(&st), want, "seed {seed}, round {round}");
                assert_eq!(link_facts(&st), want_links, "seed {seed}, round {round}");
                assert_eq!(prof.sub_items, serial_prof.sub_items);
                assert_eq!(prof.edge_items, serial_prof.edge_items);
                assert_eq!(prof.link_items, serial_prof.edge_items);
                assert_eq!(prof.nf1_scan, serial_prof.nf1_scan);
                assert_eq!(prof.nf3_scan, serial_prof.nf3_scan);
                assert_eq!(st.edge_epoch, serial.edge_epoch);
            }
        }
    }

    #[test]
    fn context_parallel_classification_is_byte_identical_across_worker_counts() {
        // End to end through `classify`: NF1 chains, a conjunction, an
        // existential pair, an NF4 axiom, a role inclusion, a role chain and
        // an unsatisfiable conjunction, classified serially and at one, two
        // and four workers. The serialised result must be byte for byte the
        // same for every worker count, and must carry the same answers as the
        // serial engine.
        let mut axioms: Vec<String> = Vec::new();
        for i in 0..48u32 {
            axioms.push(cl(
                &[c(&format!("C{i}"), "x")],
                &[c(&format!("C{}", (i + 1) % 48), "x")],
            ));
            axioms.push(cl(
                &[c(&format!("C{i}"), "x")],
                &[c(&format!("D{}", i % 7), "x")],
            ));
        }
        for i in 0..12u32 {
            axioms.push(cl(&[c(&format!("D{}", i % 7), "x")], &[rf("R", "x", "f")]));
            axioms.push(cl(
                &[c(&format!("D{}", i % 7), "x")],
                &[cf(&format!("E{i}"), "f", "x")],
            ));
            axioms.push(cl(
                &[r("R", "x", "y"), c(&format!("E{i}"), "y")],
                &[c(&format!("F{i}"), "x")],
            ));
            axioms.push(cl(
                &[c(&format!("E{i}"), "x"), c(&format!("F{i}"), "x")],
                &[c(&format!("G{i}"), "x")],
            ));
        }
        axioms.push(cl(&[r("R", "x", "y")], &[r("S", "x", "y")]));
        axioms.push(cl(
            &[r("R", "x", "y"), r("S", "y", "z")],
            &[r("T", "x", "z")],
        ));
        axioms.push(cl(&[r("T", "x", "y"), c("E0", "y")], &[c("H", "x")]));
        // An unsatisfiable concept with a predecessor, so ⊥ is derived and
        // then propagated backwards over an edge.
        axioms.push(cl(&[c("Z", "x")], &[c("D0", "x")]));
        axioms.push(cl(&[c("Z", "x")], &[c("E0", "x")]));
        // An empty head is ⊥ (`to_nf`); a named `owl:Nothing` would only be a
        // concept called that.
        axioms.push(cl(&[c("D0", "x"), c("E0", "x")], &[]));
        axioms.push(cl(&[c("Y", "x")], &[rf("R", "x", "g")]));
        axioms.push(cl(&[c("Y", "x")], &[cf("Z", "g", "x")]));
        let source = clauses(&format!("[{}]", axioms.join(",")));

        let serial = classify(source.clone()).expect("the EL route accepts the fixture");
        assert!(!serial.subsumptions.is_empty());
        let mut bytes: Option<String> = None;
        for workers in [1usize, 2, 4, 2, 4] {
            let result = with_par_workers(workers, || classify(source.clone()))
                .expect("the EL route accepts the fixture");
            let rendered = serde_json::to_string(&result).expect("the result serialises");
            match &bytes {
                None => bytes = Some(rendered),
                Some(want) => assert_eq!(&rendered, want, "{workers} workers: output bytes"),
            }
            // Same answers as the serial engine (which orders each row by its
            // own insertion history, so the rows are compared as sets).
            assert_eq!(result.inconsistent, serial.inconsistent);
            assert_eq!(result.unresolved, serial.unresolved);
            assert_eq!(
                result.subsumptions.keys().collect::<Vec<_>>(),
                serial.subsumptions.keys().collect::<Vec<_>>(),
                "{workers} workers: subjects"
            );
            for (subject, sups) in &result.subsumptions {
                let mut got = sups.clone();
                let mut want = serial.subsumptions[subject].clone();
                got.sort();
                want.sort();
                assert_eq!(got, want, "{workers} workers: supers of {subject}");
            }
        }
        // The fixture really exercises ⊥, its backward propagation over an
        // edge, and the existential rules.
        assert!(serial.subsumptions["Z"].iter().any(|s| s == "owl:Nothing"));
        assert!(serial.subsumptions["Y"].iter().any(|s| s == "owl:Nothing"));
        assert!(!serial.inconsistent);
    }

    #[test]
    fn context_parallel_plan_keeps_the_order_sensitive_modes_serial() {
        // The policy, without the environment: the parallel engine is opt-in
        // and declines wherever the serial construction ORDER is load-bearing.
        let plan = |requested, par_nf4, fifo, cert, lean, symbols, available| {
            context_parallel_plan(requested, par_nf4, fifo, cert, lean, symbols, available)
        };
        assert_eq!(
            plan(4, false, false, CertMode::Off, false, 1000, 8),
            Some(4)
        );
        // Off by default, and one worker is the serial engine.
        assert_eq!(plan(0, false, false, CertMode::Off, false, 1000, 8), None);
        assert_eq!(plan(1, false, false, CertMode::Off, false, 1000, 8), None);
        // The frontier batch reads a consecutive edge run off the global FIFO,
        // and the A/B baseline asks for that FIFO outright.
        assert_eq!(plan(4, true, false, CertMode::Off, false, 1000, 8), None);
        assert_eq!(plan(4, false, true, CertMode::Off, false, 1000, 8), None);
        // The certificate check and its repair fork read the saturated state
        // in construction order.
        assert_eq!(plan(4, false, false, CertMode::Check, false, 1000, 8), None);
        assert_eq!(
            plan(4, false, false, CertMode::Repair, false, 1000, 8),
            None
        );
        assert_eq!(plan(4, false, false, CertMode::Off, true, 1000, 8), None);
        // Never more workers than CPUs or contexts.
        assert_eq!(
            plan(16, false, false, CertMode::Off, false, 1000, 4),
            Some(4)
        );
        assert_eq!(plan(8, false, false, CertMode::Off, false, 3, 8), Some(3));
        assert_eq!(plan(8, false, false, CertMode::Off, false, 1, 8), None);
    }

    #[test]
    fn shard_queue_drains_one_activated_context_at_a_time() {
        // The shard-local counterpart of
        // `contextual_worklist_drains_one_activated_context_at_a_time`, over
        // owner slots instead of context ids.
        let mut queue = ShardQueue::new(4);
        assert_eq!(queue.pop(), None);
        queue.push(1, PItem::Sub(5, 4));
        queue.push(2, PItem::Sub(9, 6));
        queue.push(1, PItem::Fwd(5, 0, 7));
        assert_eq!(queue.len, 3);
        // Slot 1 was activated first; its items come back newest first, and a
        // conclusion it produces for itself is taken in the same activation.
        assert_eq!(queue.pop(), Some(PItem::Fwd(5, 0, 7)));
        assert_eq!(queue.activations, 1);
        queue.push(1, PItem::Link(3, 0, 5));
        assert_eq!(queue.pop(), Some(PItem::Link(3, 0, 5)));
        assert_eq!(queue.pop(), Some(PItem::Sub(5, 4)));
        // The context is released by the pop that finds it empty.
        assert_eq!(queue.pop(), Some(PItem::Sub(9, 6)));
        assert_eq!(queue.activations, 2);
        assert_eq!(queue.pop(), None);
        assert_eq!(queue.len, 0);
        // Freed cells are recycled: the arena holds the peak pending count.
        assert_eq!(queue.slots.len(), 3);
    }

    #[test]
    fn context_parallel_propagates_bottom_and_chains_across_shards() {
        // A targeted cross-shard case: consecutive concept ids land on
        // different workers under `c % W`, so this chain of edges forces the
        // ⊥ back-propagation, the NF4 join and the role composition to travel
        // as messages in both directions.
        let mut nfs = empty_nfs();
        let concepts: Vec<u32> = (2..10).collect();
        let (r1, r2, r3) = (10u32, 11u32, 12u32);
        nfs.concept_names = concepts.iter().copied().collect();
        nfs.concept_names.insert(TOP);
        nfs.role_names = [r1, r2, r3].into_iter().collect();
        for window in concepts.windows(2) {
            // Cᵢ ⊑ ∃R1.Cᵢ₊₁
            nfs.nf3.push(Nf3 {
                sub: window[0],
                role: r1,
                filler: window[1],
            });
        }
        // The far end is unsatisfiable, so ⊥ has to walk the whole chain back.
        nfs.nf5.push(9);
        // ∃R1.C9 ⊑ C2 and the chain R1∘R1 ⊑ R3 with ∃R3.C9 ⊑ C3.
        nfs.nf4.push(Nf4 {
            role: r1,
            filler: 9,
            sup: 2,
        });
        nfs.nf4.push(Nf4 {
            role: r3,
            filler: 9,
            sup: 3,
        });
        nfs.nf6.push(Nf6 { sub: r1, sup: r2 });
        nfs.nf7.push(Nf7 {
            r1,
            r2: r1,
            sup: r3,
        });
        let n = 13;
        let idx = build_idx(&nfs, n);
        let mut serial = init_state(&nfs, n);
        seed_reflexive_edges(&nfs, &idx, &mut serial);
        run(&idx, &mut serial, &mut Prof::default());
        let (want_sub, want_edge) = naive_fixpoint(&nfs, n);
        let want = state_facts(&serial);
        assert!(serial.sub_super[2].contains(&BOTTOM), "⊥ reaches the head");
        for workers in [1usize, 2, 3, 4, 5] {
            let mut prof = Prof::default();
            let st = run_context_parallel(&nfs, &idx, n, workers, &mut prof)
                .expect("the worker threads start");
            assert_eq!(state_facts(&st), want, "{workers} workers");
            let (subs, edges) = state_facts(&st);
            assert_eq!(
                subs.iter().copied().collect::<HashSet<(u32, u32)>>(),
                want_sub,
                "{workers} workers"
            );
            assert_eq!(
                edges.iter().copied().collect::<HashSet<(u32, u32, u32)>>(),
                want_edge,
                "{workers} workers"
            );
        }
    }
}
