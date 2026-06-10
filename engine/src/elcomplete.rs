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

/// Map the clause set onto EL++ normal forms. Returns `None` as soon as any
/// clause lies outside EL++ (disjunctive head, equality/number atom, nominal
/// `ind` term, unsupported shape) — a sound, conservative EL router.
fn to_nf(clauses: &[JClause], it: &mut Interner) -> Option<Nfs> {
    let mut nf1 = Vec::new();
    let mut nf2 = Vec::new();
    let mut nf3 = Vec::new();
    let mut nf4 = Vec::new();
    let mut nf5 = Vec::new();
    let mut nf6 = Vec::new();
    let mut nf7 = Vec::new();
    let mut concept_names: HashSet<u32> = HashSet::default();
    let mut role_names: HashSet<u32> = HashSet::default();

    // (sub_concept, skolem_fn) -> (role, filler) halves of an A ⊑ ∃R.B axiom.
    let mut pending_ex: HashMap<(u32, u32), (Option<u32>, Option<u32>)> = HashMap::default();

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
            return None;
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
            return None;
        }
        // disjunctive head => not EL (Horn only)
        if h.len() != 1 {
            return None;
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
                    return None;
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
                    return None;
                }
                Tk::Other => return None,
            }
        }

        // ---- role head ----
        if !hr.is_empty() {
            if let JAtom::Role { role, source, target } = hr[0] {
                let st = tk(target);
                let sxs = tk(source);
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
                            return None;
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
                            _ => return None,
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
                            None => return None,
                        };
                        let r1 = addr!(first);
                        let r2 = addr!(second);
                        let sup = addr!(role);
                        nf7.push(Nf7 { r1, r2, sup });
                        continue;
                    }
                }
            }
            return None;
        }
        return None;
    }

    // assemble NF3 (A ⊑ ∃R.B) from its two half-clauses
    for ((sub, _fn), (role, filler)) in pending_ex.into_iter() {
        match role {
            Some(r) => {
                let f = filler.unwrap_or(TOP);
                role_names.insert(r);
                concept_names.insert(sub);
                concept_names.insert(f);
                nf3.push(Nf3 { sub, role: r, filler: f });
            }
            None => return None, // filler with no role edge: shape we don't model
        }
    }

    Some(Nfs {
        nf1,
        nf2,
        nf3,
        nf4,
        nf5,
        nf6,
        nf7,
        concept_names,
        role_names,
    })
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
    nf4_by_role_filler: HashMap<(u32, u32), Vec<u32>>, // (role,filler) -> [sup]
    nf5_subs: HashSet<u32>,
    nf7_by_pair: HashMap<(u32, u32), Vec<u32>>, // (r1,r2) -> [sup]
    role_sub: Vec<HashSet<u32>>,                // role -> {super roles} (computed once)
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
    in_edges: Vec<HashSet<(u32, u32)>>, // target -> {(parent, role)}
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
            self.in_edges[d as usize].insert((c, r));
            self.worklist.push_back(Item::Edge(c, r, d));
        }
    }
}

/// Result of saturation: `sub_super[c]` = `{d : ⊨ c ⊑ d}`.
struct SatResult {
    sub_super: Vec<HashSet<u32>>,
}

fn saturate(nfs: &Nfs, n: usize) -> SatResult {
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
    let mut nf4_by_role_filler: HashMap<(u32, u32), Vec<u32>> = HashMap::default();
    for a in &nfs.nf4 {
        nf4_by_role_filler
            .entry((a.role, a.filler))
            .or_default()
            .push(a.sup);
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

    let idx = Idx {
        nf1_by_sub,
        nf2_by_sub,
        nf3_by_sub,
        nf4_by_role_filler,
        nf5_subs,
        nf7_by_pair,
        role_sub,
    };
    let mut st = State {
        sub_super: vec![HashSet::default(); n],
        edges: vec![HashSet::default(); n],
        in_edges: vec![HashSet::default(); n],
        worklist: VecDeque::new(),
    };

    // ----- Init rule R₀: C ⊑ C and C ⊑ ⊤ for every concept C -----
    for &c in &nfs.concept_names {
        if c == BOTTOM {
            continue;
        }
        st.add_sub(c, c);
        st.add_sub(c, TOP);
    }

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
                // R⊑ : C ⊑ D, D ⊑ E ⟹ C ⊑ E  (NF1)
                if let Some(sups) = idx.nf1_by_sub.get(&d) {
                    for &sup in sups {
                        st.add_sub(c, sup);
                    }
                }
                // R⊓ : C ⊑ D, C ⊑ D', D ⊓ D' ⊑ E ⟹ C ⊑ E  (NF2)
                if let Some(cand) = idx.nf2_by_sub.get(&d) {
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
                    for &(role, filler) in edges {
                        st.add_edge(c, role, filler);
                    }
                }
                // R⊥-edge : C ⊑ ⊥ propagates backwards along edges into C.
                if d == BOTTOM {
                    let preds: Vec<(u32, u32)> = st.in_edges[c as usize].iter().copied().collect();
                    for (parent, _role) in preds {
                        st.add_sub(parent, BOTTOM);
                    }
                }
                // R∃⁻ (NF4): edge (X,S,C) with ∃S'.D ⊑ E, S ⊑ S' ⟹ X ⊑ E.
                let preds: Vec<(u32, u32)> = st.in_edges[c as usize].iter().copied().collect();
                for (parent, role) in preds {
                    for &super_role in idx.role_supers(role) {
                        if let Some(sups) = idx.nf4_by_role_filler.get(&(super_role, d)) {
                            for &sup in sups {
                                st.add_sub(parent, sup);
                            }
                        }
                    }
                }
            }
            Item::Edge(c, r, d) => {
                // R∃⁻ (NF4): fire the new edge against everything above d.
                let d_supers: Vec<u32> = st.sub_super[d as usize].iter().copied().collect();
                for &super_role in idx.role_supers(r) {
                    for &d_super in &d_supers {
                        if let Some(sups) = idx.nf4_by_role_filler.get(&(super_role, d_super)) {
                            for &sup in sups {
                                st.add_sub(c, sup);
                            }
                        }
                    }
                }
                // R⊥-edge: edge to a known-unsat target propagates.
                if st.sub_super[d as usize].contains(&BOTTOM) {
                    st.add_sub(c, BOTTOM);
                }
                // R∘ (NF7): compose with edges leaving d.
                let out: Vec<(u32, u32)> = st.edges[d as usize].iter().copied().collect();
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
                let preds: Vec<(u32, u32)> = st.in_edges[c as usize].iter().copied().collect();
                for (parent, r0) in preds {
                    if let Some(sups) = idx.nf7_by_pair.get(&(r0, r)) {
                        for &nfsup in sups {
                            for &super_role in idx.role_sub.get(nfsup as usize).unwrap_or(&empty) {
                                st.add_edge(parent, super_role, d);
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

    SatResult {
        sub_super: st.sub_super,
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// The engine-shaped classification result (mirrors `el_route.classify`'s dict).
pub struct ElResult {
    /// `concept -> [super-concepts]` (full internal names; `owl:Nothing` for ⊥).
    pub subsumptions: std::collections::BTreeMap<String, Vec<String>>,
    pub inconsistent: bool,
}

/// Classify `clauses` with EL++ completion. Returns `Some(result)` iff the whole
/// clause set lies in EL++ (so the caller routes here); `None` otherwise (caller
/// must use the disjunctive context engine).
pub fn classify(clauses: &[JClause]) -> Option<ElResult> {
    let mut it = Interner::new();
    let nfs = to_nf(clauses, &mut it)?;
    let n = it.len();
    let res = saturate(&nfs, n);

    let mut subsumptions = std::collections::BTreeMap::new();
    for (c, sups) in res.sub_super.iter().enumerate() {
        let c = c as u32;
        // ⊤/⊥ as a *subject* give trivially-true ⊤⊑X / ⊥⊑X, which no reasoner
        // reports as a class subsumption — skip them.
        if c == TOP || c == BOTTOM {
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

    let inconsistent = res.sub_super[TOP as usize].contains(&BOTTOM);
    Some(ElResult {
        subsumptions,
        inconsistent,
    })
}
