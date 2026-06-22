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
}

// ---------------------------------------------------------------------------
// to_nf: map frontend DL-clauses to EL++ normal forms
// ---------------------------------------------------------------------------

/// Term kind, matching `el_route._tk`. The `&str` borrows live only within the
/// per-clause scan.
enum Tk<'a> {
    Var(&'a str),
    /// existential filler term `f(x)`: the function name (the bound var is
    /// irrelevant to the EL mapping, exactly as in `_tk`).
    Fun(&'a str),
    /// `ind` / `aux`: not an EL normal-form tree term.
    Other,
}

fn tk(t: &JTerm) -> Tk<'_> {
    match t {
        JTerm::Var { name } => Tk::Var(name),
        JTerm::Fun { function, .. } => Tk::Fun(function),
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

/// Map the clause set onto EL++ normal forms. Clauses outside EL++
/// (disjunctive head, equality/number atom, nominal `ind` term, unsupported
/// shape) are collected into the returned *residual* list instead of aborting:
/// the caller saturates the EL subset and then checks the residual clauses
/// against the canonical model (the completeness certificate). Returns `None`
/// only for an orphan existential-filler half-clause (a shape we don't model
/// at all).
fn to_nf(
    clauses: &[JClause],
    it: &mut Interner,
) -> Option<(Nfs, Vec<JClause>, HashMap<u32, u32>)> {
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
        if b.iter().chain(h.iter()).any(|a| matches!(a, JAtom::Eq { .. })) {
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

        // empty head => ⊥ (NF5 / disjointness)
        if h.is_empty() {
            let all_var = bc.iter().all(|a| matches!(tk(concept_of(a).unwrap().1), Tk::Var(_)));
            if br.is_empty() && !bc.is_empty() && all_var {
                if bc.len() == 1 {
                    let s = addc!(concept_of(bc[0]).unwrap().0);
                    nf5.push(s);
                    continue;
                }
                // A1⊓…⊓Ak ⊑ ⊥ : binary-decompose (k>=2)
                let mut names: Vec<String> =
                    bc.iter().map(|a| concept_of(a).unwrap().0.to_string()).collect();
                names.sort();
                let mut acc = names[0].clone();
                for j in 1..names.len() - 1 {
                    let aux = format!("__conj__{}", names[..=j].join("/"));
                    let s1 = addc!(&acc);
                    let s2 = addc!(&names[j]);
                    let sup = addc!(&aux);
                    nf2.push(Nf2 { sub1: s1, sub2: s2, sup });
                    acc = aux;
                }
                let s1 = addc!(&acc);
                let s2 = addc!(&names[names.len() - 1]);
                nf2.push(Nf2 { sub1: s1, sub2: s2, sup: BOTTOM });
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
                Tk::Var(_) => {
                    let all_var =
                        bc.iter().all(|a| matches!(tk(concept_of(a).unwrap().1), Tk::Var(_)));
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
                                nf2.push(Nf2 { sub1: s1, sub2: s2, sup: hd });
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
                                    let aux = format!("__conj__{}", names[..=j].join("/"));
                                    let s1 = addc!(&acc);
                                    let s2 = addc!(&names[j]);
                                    let sup = addc!(&aux);
                                    nf2.push(Nf2 { sub1: s1, sub2: s2, sup });
                                    acc = aux;
                                }
                                let s1 = addc!(&acc);
                                let s2 = addc!(&names[names.len() - 1]);
                                let hd = addc!(hd_name);
                                nf2.push(Nf2 { sub1: s1, sub2: s2, sup: hd });
                            }
                        }
                        continue;
                    }
                    // NF4:  R(x,y) ∧ A(y) ⊑ B(x)
                    if br.len() == 1 && bc.len() == 1 {
                        if let JAtom::Role { role, source, target } = br[0] {
                            let (cc_name, cc_term) = concept_of(bc[0]).unwrap();
                            if let (Tk::Var(_), Tk::Var(ty)) = (tk(source), tk(target)) {
                                if let Tk::Var(cv) = tk(cc_term) {
                                    if cv == ty {
                                        let r = addr!(role);
                                        let f = addc!(cc_name);
                                        let hd = addc!(hd_name);
                                        nf4.push(Nf4 { role: r, filler: f, sup: hd });
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    residual.push(c.clone());
                    continue;
                }
                Tk::Fun(fname) => {
                    // existential filler: A(x) -> B(f(x))
                    if bc.len() == 1
                        && br.is_empty()
                        && matches!(tk(concept_of(bc[0]).unwrap().1), Tk::Var(_))
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
            if let JAtom::Role { role, source, target } = hr[0] {
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
                if let Tk::Fun(fname) = st {
                    if matches!(sxs, Tk::Var(_))
                        && bc.len() == 1
                        && br.is_empty()
                        && matches!(tk(concept_of(bc[0]).unwrap().1), Tk::Var(_))
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
                        let fwd = match (
                            vname(&tk(bs)),
                            vname(&tk(bt)),
                            vname(&sxs),
                            vname(&st),
                        ) {
                            (Some(a), Some(b), Some(c), Some(d)) => a == c && b == d,
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
                            if a1 == b0 && hs == a0 && ht == b1 {
                                Some((ra, rb)) // R=br0, S=br1
                            } else if b1 == a0 && hs == b0 && ht == a1 {
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
    // function's filler node for the residual certificate (the canonical
    // model interprets `f(x)` as the constant filler node). A skolem reused
    // with conflicting fillers (never emitted by the frontend) is dropped
    // from the map, so residuals mentioning it bail conservatively.
    let mut skolem_filler: HashMap<u32, u32> = HashMap::default();
    let mut skolem_ambiguous: HashSet<u32> = HashSet::default();
    for ((sub, fnid), (role, filler)) in pending_ex.into_iter() {
        match role {
            Some(r) => {
                let f = filler.unwrap_or(TOP);
                role_names.insert(r);
                concept_names.insert(sub);
                concept_names.insert(f);
                nf3.push(Nf3 { sub, role: r, filler: f });
                match skolem_filler.entry(fnid) {
                    std::collections::hash_map::Entry::Occupied(e) if *e.get() != f => {
                        skolem_ambiguous.insert(fnid);
                    }
                    std::collections::hash_map::Entry::Occupied(_) => {}
                    std::collections::hash_map::Entry::Vacant(v) => {
                        v.insert(f);
                    }
                }
            }
            None => return None, // filler with no role edge: shape we don't model
        }
    }
    for fnid in skolem_ambiguous {
        skolem_filler.remove(&fnid);
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
        },
        residual,
        skolem_filler,
    ))
}

// ---------------------------------------------------------------------------
// Saturation
// ---------------------------------------------------------------------------

/// Worklist item, mirroring the Python `("sub", ...)` / `("edge", ...)` tuples.
enum Item {
    Sub(u32, u32),
    Edge(u32, u32, u32),
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
    // target -> [(parent, role)]. A `Vec`, not a `HashSet`: duplicates are
    // already excluded because an `(parent, role)` pair is appended only inside
    // the `edges[parent].insert(...)` success branch of `add_edge`, which fires
    // at most once per distinct edge. Storing it as a slice lets the hot NF4
    // rule iterate predecessors with a clone-free index loop (add_sub never
    // mutates in_edges), instead of `.collect()`-ing the set on every Sub item.
    in_edges: Vec<Vec<(u32, u32)>>,
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
}

impl State {
    #[inline]
    fn add_sub(&mut self, c: u32, d: u32) {
        if self.sub_super[c as usize].insert(d) {
            self.worklist.push_back(Item::Sub(c, d));
        }
    }

    #[inline]
    fn add_edge(&mut self, c: u32, r: u32, d: u32) {
        if self.edges[c as usize].insert((r, d)) {
            self.in_edges[d as usize].push((c, r));
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
            in_edges: self.in_edges.clone(),
            prop: self.prop.clone(),
            worklist: VecDeque::new(),
        }
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
        nf3_by_sub.entry(a.sub).or_default().push((a.role, a.filler));
    }
    // NF4 (∃R.D⊑E) indexed by filler D -> [(role R, sup E)]. The Sub rule reads
    // it to register propagations; the Edge rule consults the `prop` store the
    // Sub rule fills, so no `(role,filler)` index is needed.
    let mut nf4_by_filler: HashMap<u32, Vec<(u32, u32)>> = HashMap::default();
    for a in &nfs.nf4 {
        nf4_by_filler.entry(a.filler).or_default().push((a.role, a.sup));
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
        in_edges: vec![Vec::new(); n],
        prop: HashMap::default(),
        worklist: VecDeque::new(),
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
    nf4_sub_scan: u64,  // (in_edge, super_role) lookups in the Sub-NF4 rule
    nf4_edge_scan: u64, // (super_role, d_super) lookups in the Edge-NF4 rule
    nf7_scan: u64,      // out-edges scanned in the NF7 rule
    botback: u64,
}

/// Run the completion rules to fixpoint over whatever is on `st`'s worklist.
/// Re-entrant: the certificate repair re-enters with extra seeded facts and the
/// SAME `idx` (the rule set never changes), so a repaired structure is again
/// closed under every EL rule — i.e. it stays a model of the EL clause set.
fn run(idx: &Idx, st: &mut State, nf4_buf: &mut Vec<u32>, prof: &mut Prof) {
    // Empty fallback so an unindexed role still yields the empty super-set
    // without a per-lookup allocation (it never occurs for edge roles in
    // practice, but keeps the borrow simple).
    let empty: HashSet<u32> = HashSet::default();

    // ----- Main loop -----
    // `idx` is borrowed immutably throughout; `st` mutably. Because they are
    // distinct objects, a rule can scan an index slice while pushing into the
    // state. Snapshots (`.collect()`) are taken only when iterating one of the
    // state's *own* mutated collections (sub_super[d], edges[d], in_edges[c]).
    while let Some(item) = st.worklist.pop_front() {
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
                // R⊥-edge : C ⊑ ⊥ propagates backwards along edges into C.
                // `add_sub` never touches `in_edges`, so iterate predecessors by
                // index (the list length is stable across the calls) with no clone.
                if d == BOTTOM {
                    let mut k = 0;
                    while k < st.in_edges[c as usize].len() {
                        prof.botback += 1;
                        let parent = st.in_edges[c as usize][k].0;
                        st.add_sub(parent, BOTTOM);
                        k += 1;
                    }
                }
                // R∃⁻ (NF4) + ELK propagation registration. `d` is a new subsumer
                // of `c`; if it is an NF4 filler, each axiom `∃R.d ⊑ E` is a new
                // propagation in context `c`: (a) record it in `prop[(c,R)]` so any
                // FUTURE edge into `c` with exact role R fires it (edge-side), and
                // (b) fire it now against the backward links already at `c` -- the
                // edges into `c` whose EXACT role is R (super-role edges exist by
                // the lift, so an `==` test suffices; no role-closure scan).
                // `add_sub` never mutates `in_edges`, so the index loop is
                // clone-free.
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
                    let mut k = 0;
                    while k < st.in_edges[c as usize].len() {
                        let (parent, role) = st.in_edges[c as usize][k];
                        prof.nf4_sub_scan += axs.len() as u64;
                        for &(s, e) in axs {
                            if role == s {
                                st.add_sub(parent, e);
                            }
                        }
                        k += 1;
                    }
                }
            }
            Item::Edge(c, r, d) => {
                prof.edge_items += 1;
                // R∃⁻ (NF4), ELK backward-link join: this new edge `(c,r,d)` is a
                // backward link arriving at context `d` with EXACT role `r`. Fire
                // it against the propagations already stored at `d` for that exact
                // role -- a single hashmap lookup yielding the conclusions `E`
                // (`∃r.X⊑E`, X∈label[d]), instead of rescanning the whole filler
                // label crossed with the role closure. Super-role matches are
                // covered because the lift below materialises a separate edge
                // (c,super_role,d), which fires `prop[(d,super_role)]` in turn.
                // Collect into nf4_buf first so the read of `prop` (part of `st`)
                // ends before any `add_sub` (also `st`); snapshot-safe for a
                // self-edge c==d. Skipped entirely when there are no NF4 axioms.
                if !idx.nf4_by_filler.is_empty() {
                    if let Some(es) = st.prop.get(&(d, r)) {
                        prof.nf4_edge_scan += es.len() as u64;
                        nf4_buf.clear();
                        nf4_buf.extend_from_slice(es);
                        for &sup in nf4_buf.iter() {
                            st.add_sub(c, sup);
                        }
                    }
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
                                for &super_role in idx.role_sub.get(nfsup as usize).unwrap_or(&empty) {
                                    st.add_edge(c, super_role, e);
                                }
                            }
                        }
                    }
                    // Symmetric: edge into c with role r0 plus this new edge.
                    let preds: Vec<(u32, u32)> = st.in_edges[c as usize].clone();
                    for (parent, r0) in preds {
                        if let Some(sups) = idx.nf7_by_pair.get(&(r0, r)) {
                            for &nfsup in sups {
                                for &super_role in idx.role_sub.get(nfsup as usize).unwrap_or(&empty) {
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

/// A residual clause: `body -> head`, universally quantified over `nvars`
/// variables.  Skolem terms `f(x)` are compiled to *pinned* variables, fixed
/// to the canonical node of the skolem's NF3 filler: the canonical model
/// interprets every skolem function as the constant map to its filler node
/// (consistent with the NF3 edges/memberships the completion materialises),
/// which makes ≥n witness-distinctness clauses
/// (`Q(x) ∧ f₀(x) ≈ f₁(x) → ⊥`) and other fun-term residuals checkable:
/// distinct fillers are distinct domain elements.
struct RClause {
    nvars: usize,
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
    skolem_filler: &HashMap<u32, u32>,
) -> Option<Vec<RClause>> {
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
    fn vid<'a>(vars: &mut Vec<&'a str>, name: &'a str) -> usize {
        if let Some(i) = vars.iter().position(|v| *v == name) {
            return i;
        }
        vars.push(name);
        vars.len() - 1
    }
    let mut out = Vec::with_capacity(residual.len());
    for c in residual {
        let mut vars: Vec<&str> = Vec::new();
        let mut pins: Vec<(usize, u32)> = Vec::new();
        let mut body = Vec::with_capacity(c.body.len());
        let mut head = Vec::with_capacity(c.head.len());
        // a term: plain variable, or a skolem `f(x)` pinned to its filler node
        macro_rules! term_v {
            ($t:expr) => {
                match $t {
                    JTerm::Var { name } => vid(&mut vars, name),
                    JTerm::Fun { function, arg } => {
                        if !matches!(arg.as_ref(), JTerm::Var { .. }) {
                            bail!(c, "nested fun term");
                        }
                        let fnid = it.intern(function);
                        let filler = match skolem_filler.get(&fnid) {
                            Some(&f) => f,
                            None => bail!(c, "fun term without NF3 filler"),
                        };
                        let v = vid(&mut vars, function);
                        if !pins.iter().any(|&(pv, _)| pv == v) {
                            pins.push((v, filler));
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
                    JAtom::Role { role, source, target } => {
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
            body,
            head,
            pins,
        });
    }
    Some(out)
}

/// Hard cap on violations recorded per repair round: bounds round memory; the
/// uncollected remainder is caught by the recheck after this round's repairs.
const REPAIR_VIOL_CAP: usize = 100_000;

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
) -> bool {
    let n = sub_super.len();
    // domain: satisfiable concept nodes
    let mut alive = vec![false; n];
    let mut nodes: Vec<u32> = Vec::new();
    for &cn in concept_names {
        if cn != BOTTOM && !sub_super[cn as usize].contains(&BOTTOM) {
            alive[cn as usize] = true;
            nodes.push(cn);
        }
    }
    // enumeration indexes for the body atoms
    let mut needed_c: HashSet<u32> = HashSet::default();
    let mut needed_r: HashSet<u32> = HashSet::default();
    for rc in rcs {
        for a in &rc.body {
            match a {
                RAtom::C { cid, .. } => {
                    needed_c.insert(*cid);
                }
                RAtom::R { rid, .. } => {
                    needed_r.insert(*rid);
                }
                RAtom::Eq { .. } => {}
            }
        }
    }
    let mut members: HashMap<u32, Vec<u32>> = HashMap::default();
    for &c in &nodes {
        for &s in &sub_super[c as usize] {
            if needed_c.contains(&s) {
                members.entry(s).or_default().push(c);
            }
        }
    }
    let mut edges_by_role: HashMap<u32, Vec<(u32, u32)>> = HashMap::default();
    for &c in &nodes {
        for &(r, d) in &edges[c as usize] {
            if needed_r.contains(&r) && alive[d as usize] {
                edges_by_role.entry(r).or_default().push((c, d));
            }
        }
    }
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
                        rc, rci, order, depth, asg, nodes, alive, sub_super, edges, repr, members,
                        edges_by_role, empty_m, empty_e, budget, collect,
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
                        rc, rci, order, depth + 1, asg, nodes, alive, sub_super, edges, repr, members,
                        edges_by_role, empty_m, empty_e, budget, collect,
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
                            rc, rci, order, depth + 1, asg, nodes, alive, sub_super, edges, repr,
                            members, edges_by_role, empty_m, empty_e, budget, collect,
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
                        rc, rci, order, depth + 1, asg, nodes, alive, sub_super, edges, repr, members,
                        edges_by_role, empty_m, empty_e, budget, collect,
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
                            rc, rci, order, depth + 1, asg, nodes, alive, sub_super, edges, repr,
                            members, edges_by_role, empty_m, empty_e, budget, collect,
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
                            rc, rci, order, depth + 1, asg, nodes, alive, sub_super, edges, repr,
                            members, edges_by_role, empty_m, empty_e, budget, collect,
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
                        rc, rci, order, depth + 1, asg, nodes, alive, sub_super, edges, repr, members,
                        edges_by_role, empty_m, empty_e, budget, collect,
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
            rc, i, &order, 0, &mut asg, &nodes, &alive, sub_super, edges, repr, &members,
            &edges_by_role, &empty_m, &empty_e, budget, &mut collect,
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
    cert_round(rcs, &nfs.concept_names, &st.sub_super, &st.edges, None, &mut budget, None, debug)
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
    let ins: Vec<(u32, u32)> = std::mem::take(&mut st.in_edges[b as usize]);
    for (src, r) in ins {
        st.edges[src as usize].remove(&(r, b));
        st.add_edge(src, r, a);
    }
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
        let mut nf4_buf: Vec<u32> = Vec::new();
        let mut budget: u64 = 400_000_000;
        let mut adds: u64 = 0;
        let mut repr: Vec<u32> = (0..n as u32).collect();
        let mut merged: Vec<u32> = Vec::new();
        let mut prov: HashMap<(u32, u32), usize> = HashMap::default();
        // chronological choice log (node, clause, disjunct) for blame when
        // the direct lookup misses (conflicting facts often arrive via the
        // closure, not directly)
        let mut chrono: Vec<(u32, usize, u32)> = Vec::new();
        for round in 1..=MAX_ROUNDS {
            let mut viols: Vec<(usize, Vec<u32>)> = Vec::new();
            let crep: Vec<u32> = (0..n as u32).map(|i| uf_find(&mut repr, i)).collect();
            let clean = cert_round(
                rcs,
                &nfs.concept_names,
                &st.sub_super,
                &st.edges,
                Some(&crep),
                &mut budget,
                Some(&mut viols),
                false,
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
            for (rci, asg) in &viols {
                let head = &rcs[*rci].head;
                // addable candidates in this clause's preference order
                let cands: Vec<&RAtom> = if polv[*rci] {
                    head.iter().rev().filter(|a| !matches!(a, RAtom::Eq { .. })).collect()
                } else {
                    head.iter().filter(|a| !matches!(a, RAtom::Eq { .. })).collect()
                };
                // choice: prefer an unbanned candidate not disjoint with
                // the node's labels, then any unbanned one, then anything
                let mut pick: Option<&RAtom> = None;
                for a in &cands {
                    let ok = match **a {
                        RAtom::C { cid, v } => {
                            let nd = uf_find(&mut repr, asg[v]);
                            !banned.contains(&(nd, *rci, cid))
                                && !disj.get(&cid).is_some_and(|ds| {
                                    ds.iter().any(|d| st.sub_super[nd as usize].contains(d))
                                })
                        }
                        _ => true,
                    };
                    if ok {
                        pick = Some(*a);
                        break;
                    }
                }
                if pick.is_none() {
                    for a in &cands {
                        let ok = match **a {
                            RAtom::C { cid, v } => {
                                let nd = uf_find(&mut repr, asg[v]);
                                !banned.contains(&(nd, *rci, cid))
                            }
                            _ => true,
                        };
                        if ok {
                            pick = Some(*a);
                            break;
                        }
                    }
                }
                if pick.is_none() {
                    pick = cands.first().copied();
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
                    None => match head.iter().find_map(|a| match *a {
                        RAtom::Eq { s, t } => Some((s, t)),
                        _ => None,
                    }) {
                        Some((s, t)) => {
                            // an earlier merge in THIS round may already have
                            // unified the pair (violations were enumerated
                            // against the round-start state)
                            if uf_find(&mut repr, asg[s]) == uf_find(&mut repr, asg[t]) {
                                continue;
                            }
                            merge_nodes(&mut st, &mut repr, &mut merged, asg[s], asg[t]);
                        }
                        None => {
                            // ⊥-clause violated: blame the direct repair
                            // choice that put a body concept there; failing
                            // that, the last choice made at the conflicting
                            // node; failing that, the last choice globally
                            // (chronological backtracking).
                            let mut blame: Option<(u32, usize, u32)> = None;
                            for a in &rcs[*rci].body {
                                if let RAtom::C { cid, v } = *a {
                                    let nd = uf_find(&mut repr, asg[v]);
                                    if let Some(&src) = prov.get(&(nd, cid)) {
                                        if !banned.contains(&(nd, src, cid)) {
                                            blame = Some((nd, src, cid));
                                            break;
                                        }
                                    }
                                }
                            }
                            if blame.is_none() {
                                let mut conf_nodes: Vec<u32> = Vec::new();
                                for a in &rcs[*rci].body {
                                    if let RAtom::C { v, .. } | RAtom::R { s: v, .. } = *a {
                                        conf_nodes.push(uf_find(&mut repr, asg[v]));
                                    }
                                }
                                blame = chrono
                                    .iter()
                                    .rev()
                                    .find(|t| {
                                        conf_nodes.contains(&uf_find(&mut repr, t.0))
                                            && !banned.contains(*t)
                                    })
                                    .copied()
                                    .or_else(|| {
                                        chrono
                                            .iter()
                                            .rev()
                                            .find(|t| !banned.contains(*t))
                                            .copied()
                                    });
                            }
                            match blame {
                                Some(triple) => {
                                    if debug {
                                        eprintln!(
                                            "KM_ELC_CERT repair pass {pass_label}: clause \
                                             {rci} conflict, banning choice {:?}",
                                            triple
                                        );
                                    }
                                    return PassOut::Conflict(triple);
                                }
                                None => {
                                    if debug {
                                        eprintln!(
                                            "KM_ELC_CERT repair pass {pass_label}: clause \
                                             {rci} violated with empty head (no choices made \
                                             — genuine inconsistency)"
                                        );
                                    }
                                    return PassOut::Fail;
                                }
                            }
                        }
                    },
                }
                adds += 1;
            }
            // Re-close under the EL rules: the repaired structure must again
            // be a model of the EL clause set before the next recheck.
            run(idx, &mut st, &mut nf4_buf, &mut Prof::default());
            // Re-sync merged ids as mirrors of their (closed) representative,
            // so every concept's canonical witness remains in the domain with
            // exactly the representative's labels and edges.
            for &b in &merged {
                let a = uf_find(&mut repr, b);
                if a != b {
                    st.sub_super[b as usize] = st.sub_super[a as usize].clone();
                    st.edges[b as usize] = st.edges[a as usize].clone();
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
                                .find(|t| {
                                    uf_find(&mut repr, t.0) == cr && !banned.contains(*t)
                                })
                                .copied()
                        })
                        .or_else(|| {
                            chrono.iter().rev().find(|t| !banned.contains(*t)).copied()
                        });
                    match blame {
                        Some(triple) => {
                            if debug {
                                eprintln!(
                                    "KM_ELC_CERT repair pass {pass_label}: witness {} died, \
                                     banning choice {:?}",
                                    c, triple
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

    const RESTART_CAP: usize = 64;
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
                    eprintln!(
                        "KM_ELC_CERT repair pass {seed}: death-tolerant model accepted"
                    );
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
pub struct ElResult {
    /// named subjects the certificate could NOT determine (nonempty only in
    /// repair mode): the caller must classify exactly these with the context
    /// engine and merge; every other subject's answer is exact.
    pub unresolved: Vec<String>,
    /// `concept -> [super-concepts]` (full internal names; `owl:Nothing` for ⊥).
    pub subsumptions: std::collections::BTreeMap<String, Vec<String>>,
    pub inconsistent: bool,
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
    let mut unresolved: Vec<String> = Vec::new();
    let mut it = Interner::new();
    let (mut nfs, residual, skolem_filler) = to_nf(&clauses, &mut it)?;
    // ELK discards the OWL parse tree once axioms are indexed. `to_nf` has
    // interned the EL part into `nfs` (u32-keyed) and cloned the non-EL part into
    // `residual`; the original `clauses` (millions of `JClause`, each owning
    // `String` IRIs -- a multi-GB block on the giants) is dead from here on.
    // Drop it BEFORE saturation so the parse tree never coexists with the peak
    // saturation state. On a pure-EL ont (`residual` empty) this is the whole
    // input freed; the saturation then peaks on the interned state alone.
    drop(clauses);
    let rcs = if residual.is_empty() {
        Vec::new()
    } else {
        if cert == CertMode::Off {
            return None;
        }
        match compile_residual(&residual, &mut it, &mut nfs, &skolem_filler) {
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
    let mut nf4_buf: Vec<u32> = Vec::new();
    let mut prof = Prof::default();
    run(&idx, &mut st, &mut nf4_buf, &mut prof);
    if std::env::var_os("KM_ELC_PROFILE").is_some() {
        eprintln!(
            "KM_ELC_PROFILE sub_items={} edge_items={} | nf1_scan={} nf2_scan={} nf3_scan={} \
             nf4_sub_scan={} nf4_edge_scan={} nf7_scan={} botback={}",
            prof.sub_items, prof.edge_items, prof.nf1_scan, prof.nf2_scan, prof.nf3_scan,
            prof.nf4_sub_scan, prof.nf4_edge_scan, prof.nf7_scan, prof.botback
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
    let mut subsumptions = std::collections::BTreeMap::new();
    for (c, sups) in res.sub_super.iter().enumerate() {
        let c = c as u32;
        // ⊤/⊥ as a *subject* give trivially-true ⊤⊑X / ⊥⊑X, which no reasoner
        // reports as a class subsumption — skip them.
        if c == TOP || c == BOTTOM {
            continue;
        }
        // unresolved subjects are answered by the context engine instead
        if unresolved_set.contains(it.name(c)) {
            continue;
        }
        let mut out = Vec::new();
        for &d in sups.iter() {
            if d == c || d == TOP {
                continue;
            }
            out.push(if d == BOTTOM {
                "owl:Nothing".to_string()
            } else {
                it.name(d).to_string()
            });
        }
        if !out.is_empty() {
            subsumptions.insert(it.name(c).to_string(), out);
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

    fn clauses(json: &str) -> Vec<JClause> {
        serde_json::from_str::<Vec<JClause>>(json).expect("test clause JSON")
    }
    fn v(n: &str) -> String {
        format!("{{\"kind\":\"var\",\"name\":\"{}\"}}", n)
    }
    fn c(name: &str, t: &str) -> String {
        format!("{{\"kind\":\"concept\",\"concept\":\"{}\",\"term\":{}}}", name, v(t))
    }
    fn cf(name: &str, f: &str, t: &str) -> String {
        format!(
            "{{\"kind\":\"concept\",\"concept\":\"{}\",\"term\":{{\"kind\":\"fun\",\"function\":\"{}\",\"arg\":{}}}}}",
            name, f, v(t)
        )
    }
    fn r(role: &str, s: &str, t: &str) -> String {
        format!("{{\"kind\":\"role\",\"role\":\"{}\",\"source\":{},\"target\":{}}}", role, v(s), v(t))
    }
    fn rf(role: &str, s: &str, f: &str) -> String {
        format!(
            "{{\"kind\":\"role\",\"role\":\"{}\",\"source\":{},\"target\":{{\"kind\":\"fun\",\"function\":\"{}\",\"arg\":{}}}}}",
            role, v(s), f, v(s)
        )
    }
    fn cl(body: &[String], head: &[String]) -> String {
        format!("{{\"body\":[{}],\"head\":[{}]}}", body.join(","), head.join(","))
    }

    fn subs_of(res: &ElResult, sub: &str) -> Vec<String> {
        res.subsumptions.get(sub).cloned().unwrap_or_default()
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
        let (a, b, x, d) = (it.intern("A"), it.intern("B"), it.intern("X"), it.intern("D"));
        let mut sub_super: Vec<HashSet<u32>> = vec![HashSet::default(); it.len()];
        sub_super[a as usize].insert(x);
        sub_super[b as usize].insert(x);
        let residual = clauses(&format!("[{}]", cl(&[c("D", "x")], &[c("A", "x"), c("B", "x")])));
        let added = hoist_residual_disjuncts(&residual, &it, &mut sub_super);
        assert_eq!(added, 1, "exactly D⊑X recovered");
        assert!(sub_super[d as usize].contains(&x), "D⊑X must be derived");
    }

    #[test]
    fn elc_hoist_skips_when_no_common_super() {
        // A⊑X, B⊑Y. D ⊑ A ∨ B has no common super ⟹ nothing recovered.
        let mut it = Interner::new();
        let (a, b, x, y, _d) =
            (it.intern("A"), it.intern("B"), it.intern("X"), it.intern("Y"), it.intern("D"));
        let mut sub_super: Vec<HashSet<u32>> = vec![HashSet::default(); it.len()];
        sub_super[a as usize].insert(x);
        sub_super[b as usize].insert(y);
        let residual = clauses(&format!("[{}]", cl(&[c("D", "x")], &[c("A", "x"), c("B", "x")])));
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
        let res = classify_inner(cs_pass, CertMode::Check, false).expect("range satisfied by B ⊑ C");
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
        let res = classify_inner(cs1, CertMode::Check, false).expect("functional with one successor");
        assert!(subs_of(&res, "A").is_empty() || !res.inconsistent);
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
        let res = classify_inner(clauses(&format!("[{},{}]", base, constraint)), CertMode::Check, false)
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
}
