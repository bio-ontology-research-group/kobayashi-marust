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

use std::collections::{HashMap, HashSet, VecDeque};

use crate::json_io::{JAtom, JClause, JTerm};

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
            map: HashMap::new(),
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
    let mut concept_names: HashSet<u32> = HashSet::new();
    let mut role_names: HashSet<u32> = HashSet::new();

    // (sub_concept, skolem_fn) -> (role, filler) halves of an A ⊑ ∃R.B axiom.
    let mut pending_ex: HashMap<(u32, u32), (Option<u32>, Option<u32>)> = HashMap::new();

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
                // role inclusion: R(x,y) -> S(x,y)
                if matches!(st, Tk::Var(_)) && br.len() == 1 && bc.is_empty() {
                    if let JAtom::Role { role: br0, .. } = br[0] {
                        let sub = addr!(br0);
                        let sup = addr!(role);
                        nf6.push(Nf6 { sub, sup });
                        continue;
                    }
                }
                // role chain: R(x,y) ∧ S(y,z) -> T(x,z)
                if matches!(st, Tk::Var(_)) && br.len() == 2 && bc.is_empty() {
                    if let (JAtom::Role { role: r1, .. }, JAtom::Role { role: r2, .. }) =
                        (br[0], br[1])
                    {
                        let r1 = addr!(r1);
                        let r2 = addr!(r2);
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

struct Sat {
    // indexes (read-only during the loop)
    nf1_by_sub: HashMap<u32, Vec<u32>>,        // sub -> [sup]
    nf2_by_sub: HashMap<u32, Vec<(u32, u32)>>, // key -> [(other, sup)]
    nf3_by_sub: HashMap<u32, Vec<(u32, u32)>>, // sub -> [(role, filler)]
    nf4_by_role_filler: HashMap<(u32, u32), Vec<u32>>, // (role,filler) -> [sup]
    nf5_subs: HashSet<u32>,
    nf7_by_pair: HashMap<(u32, u32), Vec<u32>>, // (r1,r2) -> [sup]
    role_sub: Vec<HashSet<u32>>,                // role -> {super roles} (computed once)

    // mutable state
    sub_super: Vec<HashSet<u32>>,
    edges: Vec<HashSet<(u32, u32)>>,
    in_edges: Vec<HashSet<(u32, u32)>>, // target -> {(parent, role)}
    worklist: VecDeque<Item>,
}

impl Sat {
    fn add_sub(&mut self, c: u32, d: u32) {
        if self.sub_super[c as usize].insert(d) {
            self.worklist.push_back(Item::Sub(c, d));
        }
    }

    fn add_edge(&mut self, c: u32, r: u32, d: u32) {
        if self.edges[c as usize].insert((r, d)) {
            self.in_edges[d as usize].insert((c, r));
            self.worklist.push_back(Item::Edge(c, r, d));
        }
    }

    /// Super-roles of `r` (always includes `r`).
    fn role_supers(&self, r: u32) -> Vec<u32> {
        let s = &self.role_sub[r as usize];
        if s.is_empty() {
            vec![r]
        } else {
            s.iter().copied().collect()
        }
    }
}

/// Result of saturation: `sub_super[c]` = `{d : ⊨ c ⊑ d}`.
struct SatResult {
    sub_super: Vec<HashSet<u32>>,
}

fn saturate(nfs: &Nfs, n: usize) -> SatResult {
    // ----- build indexes -----
    let mut nf1_by_sub: HashMap<u32, Vec<u32>> = HashMap::new();
    for a in &nfs.nf1 {
        nf1_by_sub.entry(a.sub).or_default().push(a.sup);
    }
    let mut nf2_by_sub: HashMap<u32, Vec<(u32, u32)>> = HashMap::new();
    for a in &nfs.nf2 {
        // indexed by both sides; store the *other* side + the conclusion
        nf2_by_sub.entry(a.sub1).or_default().push((a.sub2, a.sup));
        nf2_by_sub.entry(a.sub2).or_default().push((a.sub1, a.sup));
    }
    let mut nf3_by_sub: HashMap<u32, Vec<(u32, u32)>> = HashMap::new();
    for a in &nfs.nf3 {
        nf3_by_sub.entry(a.sub).or_default().push((a.role, a.filler));
    }
    let mut nf4_by_role_filler: HashMap<(u32, u32), Vec<u32>> = HashMap::new();
    for a in &nfs.nf4 {
        nf4_by_role_filler
            .entry((a.role, a.filler))
            .or_default()
            .push(a.sup);
    }
    let nf5_subs: HashSet<u32> = nfs.nf5.iter().copied().collect();
    let mut nf7_by_pair: HashMap<(u32, u32), Vec<u32>> = HashMap::new();
    for a in &nfs.nf7 {
        nf7_by_pair.entry((a.r1, a.r2)).or_default().push(a.sup);
    }

    // ----- role hierarchy: reflexive-transitive closure of NF6 -----
    let mut role_sub: Vec<HashSet<u32>> = vec![HashSet::new(); n];
    for &r in &nfs.role_names {
        role_sub[r as usize].insert(r);
    }
    let mut nf6_by_sub: HashMap<u32, Vec<u32>> = HashMap::new();
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

    let mut sat = Sat {
        nf1_by_sub,
        nf2_by_sub,
        nf3_by_sub,
        nf4_by_role_filler,
        nf5_subs,
        nf7_by_pair,
        role_sub,
        sub_super: vec![HashSet::new(); n],
        edges: vec![HashSet::new(); n],
        in_edges: vec![HashSet::new(); n],
        worklist: VecDeque::new(),
    };

    // ----- Init rule R₀: C ⊑ C and C ⊑ ⊤ for every concept C -----
    for &c in &nfs.concept_names {
        if c == BOTTOM {
            continue;
        }
        sat.add_sub(c, c);
        sat.add_sub(c, TOP);
    }

    // ----- Main loop -----
    while let Some(item) = sat.worklist.pop_front() {
        match item {
            Item::Sub(c, d) => {
                // R⊑ : C ⊑ D, D ⊑ E ⟹ C ⊑ E  (NF1)
                if let Some(sups) = sat.nf1_by_sub.get(&d) {
                    let sups = sups.clone();
                    for sup in sups {
                        sat.add_sub(c, sup);
                    }
                }
                // R⊓ : C ⊑ D, C ⊑ D', D ⊓ D' ⊑ E ⟹ C ⊑ E  (NF2)
                if let Some(cand) = sat.nf2_by_sub.get(&d) {
                    let cand = cand.clone();
                    for (other, sup) in cand {
                        if sat.sub_super[c as usize].contains(&other) {
                            sat.add_sub(c, sup);
                        }
                    }
                }
                // R⊥ : D ⊑ ⊥ axiomatically (NF5) ⟹ C ⊑ ⊥
                if sat.nf5_subs.contains(&d) {
                    sat.add_sub(c, BOTTOM);
                }
                // R∃ : C ⊑ D, D ⊑ ∃R.E ⟹ edge (C,R,E)  (NF3)
                if let Some(edges) = sat.nf3_by_sub.get(&d) {
                    let edges = edges.clone();
                    for (role, filler) in edges {
                        sat.add_edge(c, role, filler);
                    }
                }
                // R⊥-edge : C ⊑ ⊥ propagates backwards along edges into C.
                if d == BOTTOM {
                    let preds: Vec<(u32, u32)> =
                        sat.in_edges[c as usize].iter().copied().collect();
                    for (parent, _role) in preds {
                        sat.add_sub(parent, BOTTOM);
                    }
                }
                // R∃⁻ (NF4): edge (X,S,C) with ∃S'.D ⊑ E, S ⊑ S' ⟹ X ⊑ E.
                let preds: Vec<(u32, u32)> = sat.in_edges[c as usize].iter().copied().collect();
                for (parent, role) in preds {
                    for super_role in sat.role_supers(role) {
                        if let Some(sups) = sat.nf4_by_role_filler.get(&(super_role, d)) {
                            let sups = sups.clone();
                            for sup in sups {
                                sat.add_sub(parent, sup);
                            }
                        }
                    }
                }
            }
            Item::Edge(c, r, d) => {
                // R∃⁻ (NF4): fire the new edge against everything above d.
                for super_role in sat.role_supers(r) {
                    let d_supers: Vec<u32> = sat.sub_super[d as usize].iter().copied().collect();
                    for d_super in d_supers {
                        if let Some(sups) = sat.nf4_by_role_filler.get(&(super_role, d_super)) {
                            let sups = sups.clone();
                            for sup in sups {
                                sat.add_sub(c, sup);
                            }
                        }
                    }
                }
                // R⊥-edge: edge to a known-unsat target propagates.
                if sat.sub_super[d as usize].contains(&BOTTOM) {
                    sat.add_sub(c, BOTTOM);
                }
                // R∘ (NF7): compose with edges leaving d.
                let out: Vec<(u32, u32)> = sat.edges[d as usize].iter().copied().collect();
                for (r2, e) in out {
                    if let Some(sups) = sat.nf7_by_pair.get(&(r, r2)) {
                        let sups = sups.clone();
                        for nfsup in sups {
                            for super_role in sat.role_supers(nfsup) {
                                sat.add_edge(c, super_role, e);
                            }
                        }
                    }
                }
                // Symmetric: edge into c with role r0 plus this new edge.
                let preds: Vec<(u32, u32)> = sat.in_edges[c as usize].iter().copied().collect();
                for (parent, r0) in preds {
                    if let Some(sups) = sat.nf7_by_pair.get(&(r0, r)) {
                        let sups = sups.clone();
                        for nfsup in sups {
                            for super_role in sat.role_supers(nfsup) {
                                sat.add_edge(parent, super_role, d);
                            }
                        }
                    }
                }
                // Plain role-hierarchy lift: an R-edge is also an S-edge for R ⊑ S.
                for super_role in sat.role_supers(r) {
                    if super_role != r {
                        sat.add_edge(c, super_role, d);
                    }
                }
            }
        }
    }

    SatResult {
        sub_super: sat.sub_super,
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
