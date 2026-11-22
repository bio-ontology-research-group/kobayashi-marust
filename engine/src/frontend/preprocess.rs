//! Sound nominal / transitivity / role-chain / domain-range preprocessing.
//!
//! Direct port of `engine/py/preprocess.py`: `nominal_clauses`,
//! `domain_range_clauses`, `detect_role_chains`, `transitivity_clauses`,
//! `chain_clauses`, `_is_chain_axiom`, and `augment`.

use std::collections::VecDeque;
// Membership/lookup tables; iteration order is per-process random as before.
type HashMap<K, V> = crate::fxhash::FxHashMap<K, V>;
type HashSet<T> = crate::fxhash::FxHashSet<T>;

use super::clauses::{clause, var_x, var_y, Atom, DLClause, Term};
use super::normalise::GroundHooks;
use super::rbox::RboxRecord;

fn is_role(a: &Atom) -> bool {
    matches!(a, Atom::Role(..))
}

/// Port of `nominal_clauses`.
pub fn nominal_clauses(abox: &[DLClause], hooks: &GroundHooks) -> Vec<DLClause> {
    // ind -> nom (inverse of nominal_to_individual). Python builds a dict from
    // nom->ind; if several noms map to one ind the last wins. We mirror by
    // letting later inserts overwrite.
    let mut ind_to_nom: HashMap<&str, &str> = HashMap::default();
    for (nom, ind) in &hooks.nominal_to_individual {
        ind_to_nom.insert(ind.as_str(), nom.as_str());
    }
    let x = var_x();
    let mut extra = Vec::new();
    let mut seen_links: std::collections::HashSet<(String, String, String)> =
        std::collections::HashSet::default();
    for c in abox {
        if !c.body.is_empty() {
            continue; // only unconditional ABox facts
        }
        for a in &c.head {
            match a {
                Atom::Concept(concept, Term::Ind(name)) => {
                    if let Some(nom) = ind_to_nom.get(name.as_str()) {
                        extra.push(clause(
                            [Atom::Concept(nom.to_string(), x.clone())],
                            [Atom::Concept(concept.clone(), x.clone())],
                        ));
                    }
                }
                // Role assertion between two nominal-proxied individuals:
                // `R(a,b)` entails `{a} ⊑ ∃R.{b}`, i.e. in proxy form
                // `__nom__a(x) → R(x, f(x))` and `__nom__a(x) → __nom__b(f(x))`.
                // Sound: interpreting each proxy as exactly its singleton (the
                // canonical extension under which every emitted proxy clause
                // holds) makes this a semantic consequence of the assertion.
                // This is the ABox-role half of the augmentation above (the
                // concept-assertion half has been emitted for years); without
                // it a hasValue successor carrying `__nom__a` never sees a's
                // asserted role edges, so transitive-role recognition through
                // the ABox graph cannot fire (ore_ont_10702: all 23 missing
                // `X ⊑ FrenchWine` need locatedIn(aRegion, FrenchRegion) at
                // the `__nom__aRegion` successor). Dedup so repeated
                // assertions emit one clause pair.
                Atom::Role(role, Term::Ind(src), Term::Ind(tgt)) => {
                    let (Some(nom_s), Some(nom_t)) =
                        (ind_to_nom.get(src.as_str()), ind_to_nom.get(tgt.as_str()))
                    else {
                        continue;
                    };
                    let key = (nom_s.to_string(), role.clone(), nom_t.to_string());
                    if !seen_links.insert(key) {
                        continue;
                    }
                    let f = Term::Fun(
                        format!("f_nomlink_{}_{}_{}", nom_s, role, nom_t),
                        Box::new(x.clone()),
                    );
                    extra.push(clause(
                        [Atom::Concept(nom_s.to_string(), x.clone())],
                        [Atom::Role(role.clone(), x.clone(), f.clone())],
                    ));
                    extra.push(clause(
                        [Atom::Concept(nom_s.to_string(), x.clone())],
                        [Atom::Concept(nom_t.to_string(), f)],
                    ));
                }
                _ => {}
            }
        }
    }
    extra
}

/// Port of `domain_range_clauses`.
pub fn domain_range_clauses(rbox: &[RboxRecord]) -> Vec<DLClause> {
    let x = var_x();
    let y = var_y();
    let mut out = Vec::new();
    for rec in rbox {
        match rec {
            RboxRecord::Domain(r, d) => {
                out.push(clause(
                    [Atom::Role(r.clone(), x.clone(), y.clone())],
                    [Atom::Concept(d.clone(), x.clone())],
                ));
            }
            RboxRecord::Range(r, c) => {
                out.push(clause(
                    [Atom::Role(r.clone(), x.clone(), y.clone())],
                    [Atom::Concept(c.clone(), y.clone())],
                ));
            }
            _ => {}
        }
    }
    out
}

/// A detected chain triple `(R, S, T)` for `R∘S⊑T`, or a transitive role.
pub struct ChainInfo {
    trans: Vec<String>,
    chains: Vec<(String, String, String)>,
    /// Same-orientation role inclusions `U(x,y) → V(x,y)` as `(U, V)`.
    sub_same: Vec<(String, String)>,
    /// Inverted role inclusions `U(x,y) → V(y,x)` as `(U, V)`, including a
    /// symmetric role's `(R, R)`.
    sub_inv: Vec<(String, String)>,
    /// Chain-affected consumers that [`chain_consumer_automaton_clauses`]
    /// could not encode (set by `augment`).
    pub unencoded_chain_consumers: u64,
    /// The clause stream carries ground role assertions (nominal mode with an
    /// ABox): their edges are not created by existentials, so the existential
    /// recognitions of transitive roles do not stand in for `∀` propagation.
    pub ground_edges: bool,
    /// Roles with an edge-creating clause in the stream (set by `augment`);
    /// `None` means every role. A letter of another role never fires.
    pub generated_roles: Option<HashSet<String>>,
}

/// The `R(x,y) ∧ S(y,z) → T(x,z)` shape: exactly two body atoms, both roles,
/// and one role head. Returned in body order, without allocating.
fn binary_role_composition(c: &DLClause) -> Option<(&Atom, &Atom, &Atom)> {
    match (c.body.as_slice(), c.head.as_slice()) {
        ([r0, r1], [h]) if is_role(r0) && is_role(r1) && is_role(h) => Some((r0, r1, h)),
        _ => None,
    }
}

/// Port of `detect_role_chains`.
fn detect_role_chains(tbox: &[DLClause]) -> ChainInfo {
    let mut trans: Vec<String> = Vec::new();
    let mut chains: Vec<(String, String, String)> = Vec::new();
    for c in tbox {
        if let Some((r0, r1, h)) = binary_role_composition(c) {
            let (r0r, r0s, r0t) = role_parts(r0);
            let (r1r, r1s, r1t) = role_parts(r1);
            let (hr, hs, ht) = role_parts(h);
            // orient: first.target == second.source == middle
            let pair: Option<((&str, &Term, &Term), (&str, &Term, &Term))> = if r0t == r1s {
                Some(((r0r, r0s, r0t), (r1r, r1s, r1t)))
            } else if r1t == r0s {
                Some(((r1r, r1s, r1t), (r0r, r0s, r0t)))
            } else {
                None
            };
            if let Some(((fr, fs, _ft), (sr, _ss, st))) = pair {
                if hs == fs && ht == st && fs != st {
                    if fr == sr && sr == hr {
                        if !trans.iter().any(|t| t == hr) {
                            trans.push(hr.to_string());
                        }
                    } else {
                        chains.push((fr.to_string(), sr.to_string(), hr.to_string()));
                    }
                }
            }
        }
    }
    // Converse-equivalent roles share transitivity. A one-way inclusion of
    // the converse is insufficient: require both unguarded universal bridges.
    let mut converse = HashSet::default();
    for c in tbox {
        if let ([Atom::Role(r, a, b)], [Atom::Role(s, c, d)]) =
            (c.body.as_slice(), c.head.as_slice())
        {
            if a == d && b == c && a != b
                && matches!(a, Term::Var(_)) && matches!(b, Term::Var(_))
            {
                converse.insert((r.clone(), s.clone()));
            }
        }
    }
    let mut inverse_pairs: Vec<_> = converse.iter()
        .filter(|(r,s)| converse.contains(&(s.clone(),r.clone())))
        .cloned().collect();
    inverse_pairs.sort();
    let mut index = 0;
    while index < trans.len() {
        let role = trans[index].clone();
        for (r,s) in &inverse_pairs {
            if *r == role && !trans.contains(s) { trans.push(s.clone()); }
        }
        index += 1;
    }
    let mut sub_same: Vec<(String, String)> = Vec::new();
    let mut sub_inv: Vec<(String, String)> = Vec::new();
    for c in tbox {
        if let ([Atom::Role(u, a, b)], [Atom::Role(v, c2, d)]) = (c.body.as_slice(), c.head.as_slice()) {
            if a == b || !matches!(a, Term::Var(_)) || !matches!(b, Term::Var(_)) {
                continue;
            }
            if a == c2 && b == d && u != v {
                sub_same.push((u.clone(), v.clone()));
            } else if a == d && b == c2 {
                sub_inv.push((u.clone(), v.clone()));
            }
        }
    }
    sub_same.sort();
    sub_same.dedup();
    sub_inv.sort();
    sub_inv.dedup();
    ChainInfo { trans, chains, sub_same, sub_inv, unencoded_chain_consumers: 0, ground_edges: false, generated_roles: None }
}

fn role_parts(a: &Atom) -> (&str, &Term, &Term) {
    match a {
        Atom::Role(r, s, t) => (r.as_str(), s, t),
        _ => unreachable!("role_parts on non-role atom"),
    }
}

/// Port of `transitivity_clauses`.
pub fn transitivity_clauses(tbox: &[DLClause]) -> Vec<DLClause> {
    transitivity_clauses_with(tbox, &detect_role_chains(tbox))
}

/// The single role atom of a clause body, if the body has exactly one.
fn single_body_role(c: &DLClause) -> Option<&Atom> {
    let mut roles = c.body.iter().filter(|a| is_role(a));
    let role = roles.next()?;
    roles.next().is_none().then_some(role)
}

/// [`transitivity_clauses`] over an already detected [`ChainInfo`] for the
/// same clause set, so one detection pass serves every derived family.
fn transitivity_clauses_with(tbox: &[DLClause], info: &ChainInfo) -> Vec<DLClause> {
    if info.trans.is_empty() {
        return Vec::new();
    }
    let trans: std::collections::HashSet<&str> = info.trans.iter().map(|s| s.as_str()).collect();
    let x = var_x();
    let mut extra = Vec::new();
    // seen: (role, sorted concepts-on-y) -> P name
    let mut seen: HashMap<(String, Vec<String>), String> = HashMap::default();
    for c in tbox {
        let Some(role) = single_body_role(c) else {
            continue;
        };
        let (rrole, rsource, rtarget) = role_parts(role);
        if !trans.contains(rrole) || *rsource != x {
            continue;
        }
        let y = rtarget.clone();
        if y == x {
            continue;
        }
        let mut c_on_y: Vec<String> = c
            .body
            .iter()
            .filter_map(|a| match a {
                Atom::Concept(name, t) if *t == y => Some(name.clone()),
                _ => None,
            })
            .collect();
        c_on_y.sort();
        let gamma_x: Vec<Atom> = c
            .body
            .iter()
            .filter(|a| matches!(a, Atom::Concept(_, t) if *t == x))
            .cloned()
            .collect();
        if c_on_y.is_empty() || c.head.is_empty() {
            continue;
        }
        if !c
            .head
            .iter()
            .all(|h| matches!(h, Atom::Concept(_, t) if *t == x))
        {
            continue;
        }
        let key = (rrole.to_string(), c_on_y.clone());
        let p = if let Some(p) = seen.get(&key) {
            p.clone()
        } else {
            let p = format!("__trans__{}__{}", rrole, c_on_y.join("_"));
            seen.insert(key, p.clone());
            // R(x,y) ∧ ⋀C_i(y) → P(x)
            let mut body1: Vec<Atom> = vec![Atom::Role(rrole.to_string(), x.clone(), y.clone())];
            for ci in &c_on_y {
                body1.push(Atom::Concept(ci.clone(), y.clone()));
            }
            extra.push(clause(body1, [Atom::Concept(p.clone(), x.clone())]));
            // R(x,y) ∧ P(y) → P(x)
            extra.push(clause(
                [
                    Atom::Role(rrole.to_string(), x.clone(), y.clone()),
                    Atom::Concept(p.clone(), y.clone()),
                ],
                [Atom::Concept(p.clone(), x.clone())],
            ));
            p
        };
        // Γ_x ∧ P(x) → Δ_x
        let mut body3 = gamma_x;
        body3.push(Atom::Concept(p, x.clone()));
        extra.push(clause(body3, c.head.iter().cloned()));
    }
    extra
}

/// A role literal: a role name and whether it is read backwards (`R⁻`).
type RoleLit = (String, bool);

/// `∀`-propagation over transitive roles (Horrocks and Sattler's
/// transitivity encoding for SHI, as in the CB calculus papers).
///
/// The clause stream carries a universal as `Γ(x) ∧ R(x,y) ∧ ⋀D(y) → ⋁C(y)`
/// (a universal over an inverse uses the `__inv__R` name). The raw transitivity axioms
/// `T(x,y) ∧ T(y,z) → T(x,z)` are filtered from the stream (they bloat the
/// CB contexts), and the transitivity recognitions above cover only
/// `∃`-consumers, so a universal over a role with a transitive sub-role was
/// applied to one edge only: `Q ⊑ ∀t.F` with transitive `t` missed
/// `Q ⊑ ∀t.∀t.F`, and with `s ⊑ t`, `s` symmetric and `D ⊑ ∃s.⊤`, missed
/// `D ⊓ ∀t.F ⊑ F` (the loop `t(d,x), t(x,d)`).
///
/// For every such clause and every transitive role literal `T` with
/// `T ⊑* R` in the reflexive-transitive closure of the role inclusions
/// closed under inverses (a symmetric role and an inverse pair are inclusions
/// in both orientations; the inverse of a transitive role is transitive),
/// with a fresh marker `M` read as `∀T.(¬⋀D ⊔ ⋁C)`:
///
///   Γ(x) → M(x)
///   M(x) ∧ L(x,y) ∧ ⋀D(y) → ⋁C(y)      for every literal L ⊑* T
///   M(x) ∧ L(x,y) → M(y)                for every literal L ⊑* T
///
/// where `L(x,y)` is `l(x,y)` for `L = l` and `l(y,x)` for `L = l⁻`
/// (written as `l(x,y)` with the marker moving from y to x).
/// Soundness: every model of the clauses extends to the marker by
/// `M := ∀T.(¬⋀D ⊔ ⋁C)`. The first clause holds because `T ⊑* R` and the
/// original clause, the second because `L ⊑* T` and the definition, and the
/// third because `L ⊑* T` and `T` is transitive (`∀T.E ⊑ ∀T.∀T.E ⊑ ∀L.∀T.E`). So the clauses are a conservative
/// extension and no answer over the source signature changes except by
/// completeness. Completeness: these are the propagations the standard
/// elimination of transitive roles adds (`∀R.E ⊑ ∀T.∀T.E` for transitive
/// `T ⊑* R`).
fn forall_transitivity_clauses(tbox: &[DLClause], info: &ChainInfo) -> Vec<DLClause> {
    if info.trans.is_empty() {
        return Vec::new();
    }
    let inv = |l: &RoleLit| -> RoleLit { (l.0.clone(), !l.1) };
    // Direct inclusions between literals, from `u(x,y) → v(x,y)` and
    // `u(x,y) → v(y,x)` clauses (symmetric roles and inverse pairs included).
    let mut up: HashMap<RoleLit, Vec<RoleLit>> = HashMap::default();
    let add = |a: RoleLit, b: RoleLit, up: &mut HashMap<RoleLit, Vec<RoleLit>>| {
        let (ia, ib) = (inv(&a), inv(&b));
        up.entry(a).or_default().push(b);
        up.entry(ia).or_default().push(ib);
    };
    for c in tbox {
        if let ([Atom::Role(u, a, b)], [Atom::Role(v, c2, d)]) = (c.body.as_slice(), c.head.as_slice()) {
            if a == b || !matches!(a, Term::Var(_)) || !matches!(b, Term::Var(_)) {
                continue;
            }
            if a == c2 && b == d {
                add((u.clone(), false), (v.clone(), false), &mut up);
            } else if a == d && b == c2 {
                add((u.clone(), false), (v.clone(), true), &mut up);
            }
        }
    }
    let supers = |start: &RoleLit| -> HashSet<RoleLit> {
        let mut seen: HashSet<RoleLit> = HashSet::default();
        let mut stack = vec![start.clone()];
        while let Some(l) = stack.pop() {
            if seen.insert(l.clone()) {
                for n in up.get(&l).map(Vec::as_slice).unwrap_or(&[]) {
                    stack.push(n.clone());
                }
            }
        }
        seen
    };
    // Transitive literals: the detected transitive roles, both orientations,
    // and every literal equivalent to one.
    let mut transitive: Vec<RoleLit> = Vec::new();
    for t in &info.trans {
        for lit in [(t.clone(), false), (t.clone(), true)] {
            if !transitive.contains(&lit) {
                transitive.push(lit);
            }
        }
    }
    let base_trans = transitive.clone();
    for t in &base_trans {
        for e in supers(t) {
            if supers(&e).contains(t) && !transitive.contains(&e) {
                transitive.push(e);
            }
        }
    }
    transitive.sort();
    // For each transitive literal, the literals above it.
    let trans_supers: Vec<(RoleLit, HashSet<RoleLit>)> =
        transitive.iter().map(|t| (t.clone(), supers(t))).collect();
    // Every literal below each transitive literal: the engine labels an edge
    // with the super-roles of its own direction only, so a T-edge reached
    // through an inverse inclusion (s2 ⊑ s0⁻, s0 ⊑ ti, ti symmetric) is not
    // seen as T on the existential's edge. The propagation clauses are
    // therefore emitted for every sub-literal L ⊑* T in L's own name.
    let mut universe: HashSet<RoleLit> = HashSet::default();
    for (k, vs) in &up {
        universe.insert(k.clone());
        universe.extend(vs.iter().cloned());
    }
    for t in &transitive {
        universe.insert(t.clone());
    }
    let mut lit_supers: HashMap<RoleLit, HashSet<RoleLit>> = HashMap::default();
    for l in &universe {
        lit_supers.insert(l.clone(), supers(l));
    }
    let subs_of = |t: &RoleLit| -> Vec<RoleLit> {
        let mut v: Vec<RoleLit> = lit_supers
            .iter()
            .filter(|(_, ups)| ups.contains(t))
            .map(|(l, _)| l.clone())
            .collect();
        v.sort();
        v
    };
    let x = var_x();
    let y = var_y();
    let rename = |t: &Term, cx: &Term| -> Term { if t == cx { x.clone() } else { y.clone() } };
    let mut out = Vec::new();
    let mut markers: HashMap<(RoleLit, Vec<Atom>, Vec<Atom>), String> = HashMap::default();
    for c in tbox {
        let Some(role) = single_body_role(c) else { continue };
        let (r, a, b) = role_parts(role);
        if a == b || !matches!(a, Term::Var(_)) || !matches!(b, Term::Var(_)) || c.head.is_empty() {
            continue;
        }
        // The far end carries every head atom; the near end is `x`.
        let far = match c.head.first() {
            Some(Atom::Concept(_, t)) => t.clone(),
            _ => continue,
        };
        if far != *a && far != *b {
            continue;
        }
        // Only the universal form `Γ(x) ∧ R(x,y) → C(y)` with a guard Γ: the
        // `∃`-consumer form (head on the role's source) is the business of
        // the recognitions above, and keeping it out leaves EL clause streams
        // (which have no universals) unchanged. An unguarded universal (a
        // range) already holds at every element, so it needs no marker.
        if far != *b {
            continue;
        }
        let near = a.clone();
        if !c.head.iter().all(|h| matches!(h, Atom::Concept(_, t) if *t == far)) {
            continue;
        }
        if !c.body.iter().all(|at| match at {
            Atom::Role(..) => true,
            Atom::Concept(_, t) => *t == near || *t == far,
            Atom::Eq(..) => false,
        }) {
            continue;
        }
        let lit: RoleLit = (r.to_string(), false);
        let gamma: Vec<Atom> = c
            .body
            .iter()
            .filter(|at| matches!(at, Atom::Concept(_, t) if *t == near))
            .map(|at| match at {
                Atom::Concept(n, _) => Atom::Concept(n.clone(), x.clone()),
                _ => unreachable!(),
            })
            .collect();
        let mut on_far: Vec<Atom> = c
            .body
            .iter()
            .filter(|at| matches!(at, Atom::Concept(_, t) if *t == far))
            .map(|at| match at {
                Atom::Concept(n, t) => Atom::Concept(n.clone(), rename(t, &near)),
                _ => unreachable!(),
            })
            .collect();
        on_far.sort();
        let mut head: Vec<Atom> = c
            .head
            .iter()
            .map(|h| match h {
                Atom::Concept(n, t) => Atom::Concept(n.clone(), rename(t, &near)),
                _ => unreachable!(),
            })
            .collect();
        head.sort();
        if gamma.is_empty() {
            continue;
        }
        for (t, ups) in &trans_supers {
            if !ups.contains(&lit) {
                continue;
            }
            let key = (t.clone(), on_far.clone(), head.clone());
            let next = markers.len();
            let (m, fresh) = match markers.get(&key) {
                Some(m) => (m.clone(), false),
                None => {
                    let m = format!("__forall__{}{}__{}", if t.1 { "inv_" } else { "" }, t.0, next);
                    markers.insert(key, m.clone());
                    (m, true)
                }
            };
            // Γ(x) → M(x)
            out.push(clause(gamma.clone(), [Atom::Concept(m.clone(), x.clone())]));
            if fresh {
                for l in subs_of(t) {
                    // A literal L ⊑* T: its edge `l(x,y)` runs from x to y
                    // for L = l and from y to x for L = l⁻ (the same clause
                    // read with the variables swapped, so no reversed atom).
                    let edge = Atom::Role(l.0.clone(), x.clone(), y.clone());
                    let (from, to) = if l.1 { (&y, &x) } else { (&x, &y) };
                    let at = |a: &Atom| -> Atom {
                        match a {
                            Atom::Concept(n, _) => Atom::Concept(n.clone(), to.clone()),
                            other => other.clone(),
                        }
                    };
                    // M(from) ∧ L(from,to) ∧ ⋀D(to) → ⋁C(to)
                    let mut body2 = vec![Atom::Concept(m.clone(), from.clone()), edge.clone()];
                    body2.extend(on_far.iter().map(at));
                    out.push(clause(body2, head.iter().map(at)));
                    // M(from) ∧ L(from,to) → M(to)
                    out.push(clause(
                        [Atom::Concept(m.clone(), from.clone()), edge],
                        [Atom::Concept(m.clone(), to.clone())],
                    ));
                }
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// KM_TRANS_CHAIN_COMPOSE (gated, additive): glue role CHAINS into a TRANSITIVE
/// role's reachability, the way Konclude's role automaton folds a chain's
/// transitions into the super-role's automaton (ws Konclude trace: the
/// `has_start∘start_of` chain is glued into the `part_of` automaton, and
/// `RO_0002224 ⊑ part_of`). For a transitive role `T` with reachability predicate
/// `P = __trans__T__{C}` (from `transitivity_clauses`) and a chain `R∘S ⊑ U` whose
/// super `U` is `T` or a sub-role of `T`, a node `x` with `x R y`, `y S z` has
/// `x T z`, so `x` inherits whatever `z` reaches via `T`:
///   S(y,z) ∧ P(z)   → __cmpp(y);  R(x,y) ∧ __cmpp(y) → P(x)   (P rides the chain)
///   S(y,z) ∧ ⋀C_i(z)→ __cmpc(y);  R(x,y) ∧ __cmpc(y) → P(x)   (chain reaches a C-node)
/// The P names mirror `transitivity_clauses` exactly so they line up. Sound (T
/// transitive + U⊑T). Default OFF; validate on 14817 + corpus before default-on.
pub fn transitive_chain_compose_clauses(tbox: &[DLClause]) -> Vec<DLClause> {
    if std::env::var_os("KM_TRANS_CHAIN_COMPOSE").is_none() {
        return Vec::new();
    }
    transitive_chain_compose_impl(tbox)
}

fn transitive_chain_compose_impl(tbox: &[DLClause]) -> Vec<DLClause> {
    let info = detect_role_chains(tbox);
    if info.trans.is_empty() || info.chains.is_empty() {
        return Vec::new();
    }
    let trans: HashSet<String> = info.trans.iter().cloned().collect();
    // sub-role hierarchy U ⊑ V from single role-body→role-head clauses U(x,y)→V(x,y).
    let mut sub_super: HashMap<String, Vec<String>> = HashMap::default();
    for c in tbox {
        if c.body.len() == 1 && c.head.len() == 1 {
            if let (Atom::Role(u, us, ut), Atom::Role(v, vs, vt)) = (&c.body[0], &c.head[0]) {
                if us == vs && ut == vt && us != ut && u != v {
                    sub_super.entry(u.clone()).or_default().push(v.clone());
                }
            }
        }
    }
    // first transitive role on the ⊑* chain above `u`, if any.
    fn super_trans(
        u: &str,
        sub_super: &HashMap<String, Vec<String>>,
        trans: &HashSet<String>,
        seen: &mut HashSet<String>,
    ) -> Option<String> {
        if trans.contains(u) {
            return Some(u.to_string());
        }
        if !seen.insert(u.to_string()) {
            return None;
        }
        for v in sub_super.get(u).map(|x| x.as_slice()).unwrap_or(&[]) {
            if let Some(t) = super_trans(v, sub_super, trans, seen) {
                return Some(t);
            }
        }
        None
    }
    let x = var_x();
    let y = var_y();
    let z = Term::Var("z".to_string());
    // rebuild (T, sorted C_i) -> P name exactly as transitivity_clauses.
    let mut seen_p: HashMap<(String, Vec<String>), String> = HashMap::default();
    for c in tbox {
        let roles: Vec<&Atom> = c.body.iter().filter(|a| is_role(a)).collect();
        if roles.len() != 1 {
            continue;
        }
        let (rrole, rsource, rtarget) = role_parts(roles[0]);
        if !trans.contains(rrole) || *rsource != x {
            continue;
        }
        let yt = rtarget.clone();
        if yt == x {
            continue;
        }
        let mut c_on_y: Vec<String> = c
            .body
            .iter()
            .filter_map(|a| match a {
                Atom::Concept(name, t) if *t == yt => Some(name.clone()),
                _ => None,
            })
            .collect();
        c_on_y.sort();
        if c_on_y.is_empty() || c.head.is_empty() {
            continue;
        }
        if !c
            .head
            .iter()
            .all(|h| matches!(h, Atom::Concept(_, t) if *t == x))
        {
            continue;
        }
        let key = (rrole.to_string(), c_on_y.clone());
        seen_p
            .entry(key)
            .or_insert_with(|| format!("__trans__{}__{}", rrole, c_on_y.join("_")));
    }
    let mut extra = Vec::new();
    let mut seen_mid: HashSet<String> = HashSet::default();
    for (r, s, u) in &info.chains {
        let mut seen2 = HashSet::default();
        let t = match super_trans(u, &sub_super, &trans, &mut seen2) {
            Some(t) => t,
            None => continue,
        };
        for ((pt, c_on_y), p) in &seen_p {
            if *pt != t {
                continue;
            }
            // P rides the chain: S(y,z)∧P(z)→__cmpp(y) ; R(x,y)∧__cmpp(y)→P(x)
            let midp = format!("__cmpp__{}__{}", s, p);
            if seen_mid.insert(midp.clone()) {
                extra.push(clause(
                    [
                        Atom::Role(s.clone(), y.clone(), z.clone()),
                        Atom::Concept(p.clone(), z.clone()),
                    ],
                    [Atom::Concept(midp.clone(), y.clone())],
                ));
            }
            extra.push(clause(
                [
                    Atom::Role(r.clone(), x.clone(), y.clone()),
                    Atom::Concept(midp.clone(), y.clone()),
                ],
                [Atom::Concept(p.clone(), x.clone())],
            ));
            // chain reaches a C-node: S(y,z)∧⋀C_i(z)→__cmpc(y) ; R(x,y)∧__cmpc(y)→P(x)
            let midc = format!("__cmpc__{}__{}", s, p);
            if seen_mid.insert(midc.clone()) {
                let mut body1: Vec<Atom> = vec![Atom::Role(s.clone(), y.clone(), z.clone())];
                for ci in c_on_y {
                    body1.push(Atom::Concept(ci.clone(), z.clone()));
                }
                extra.push(clause(body1, [Atom::Concept(midc.clone(), y.clone())]));
            }
            extra.push(clause(
                [
                    Atom::Role(r.clone(), x.clone(), y.clone()),
                    Atom::Concept(midc.clone(), y.clone()),
                ],
                [Atom::Concept(p.clone(), x.clone())],
            ));
        }
    }
    extra
}

/// Port of `chain_clauses`.
pub fn chain_clauses(tbox: &[DLClause]) -> Vec<DLClause> {
    chain_clauses_with(tbox, &detect_role_chains(tbox))
}

/// [`chain_clauses`] over an already detected [`ChainInfo`] for the same
/// clause set.
fn chain_clauses_with(tbox: &[DLClause], info: &ChainInfo) -> Vec<DLClause> {
    if info.chains.is_empty() {
        return Vec::new();
    }
    // by_t: T -> [(R,S)]
    let mut by_t: HashMap<String, Vec<(String, String)>> = HashMap::default();
    for (r, s, t) in &info.chains {
        by_t.entry(t.clone())
            .or_default()
            .push((r.clone(), s.clone()));
    }
    let x = var_x();
    let mut extra = Vec::new();
    // seen: (S, sorted concepts-on-y) -> Q name
    let mut seen: HashMap<(String, Vec<String>), String> = HashMap::default();
    for c in tbox {
        let Some(role) = single_body_role(c) else {
            continue;
        };
        let (trole, tsource, ttarget) = role_parts(role);
        if *tsource != x || *ttarget == x || !by_t.contains_key(trole) {
            continue;
        }
        let y = ttarget.clone();
        let mut c_on_y: Vec<String> = c
            .body
            .iter()
            .filter_map(|a| match a {
                Atom::Concept(name, t) if *t == y => Some(name.clone()),
                _ => None,
            })
            .collect();
        c_on_y.sort();
        // NOTE (known gap, docs/role-chain): an empty `c_on_y` is the
        // pure-domain consumer `T(x,y) → Head(x)` (`ObjectPropertyDomain`).
        // The chain `R∘S⊑T` should still fire (`∃R.∃S.⊤ ⊑ Head`), but two
        // things block it here: (1) `domain_range_clauses` are added in
        // mod.rs pass 2, AFTER this runs in `augment` pass 1, so the domain
        // consumer is not yet visible; (2) reordering breaks the reg.short
        // name-assignment invariant (byte-identity). Plus the 11745 case also
        // needs the chain to compose with TRANSITIVE `part_of`. Reproducer:
        // /tmp/probe_chain_domain.ofn; minimal real witness:
        // oracle/ontologies/11745_unsat_core.ofn (GO_0008046 unsat missed).
        if c_on_y.is_empty() || c.head.is_empty() {
            continue;
        }
        if !c
            .head
            .iter()
            .all(|h| matches!(h, Atom::Concept(_, t) if *t == x))
        {
            continue;
        }
        let pairs = by_t.get(trole).unwrap().clone();
        for (r, s) in pairs {
            let key = (s.clone(), c_on_y.clone());
            let q = if let Some(q) = seen.get(&key) {
                q.clone()
            } else {
                let q = format!("__chain__{}__{}", s, c_on_y.join("_"));
                seen.insert(key, q.clone());
                let mut body1: Vec<Atom> = vec![Atom::Role(s.clone(), x.clone(), y.clone())];
                for ci in &c_on_y {
                    body1.push(Atom::Concept(ci.clone(), y.clone()));
                }
                extra.push(clause(body1, [Atom::Concept(q.clone(), x.clone())]));
                q
            };
            extra.push(clause(
                [
                    Atom::Role(r.clone(), x.clone(), y.clone()),
                    Atom::Concept(q.clone(), y.clone()),
                ],
                c.head.iter().cloned(),
            ));
        }
    }
    extra
}

/// Regular role-inclusion automata for the consumers that the one-level
/// [`transitivity_clauses`] and [`chain_clauses`] encodings do not cover.
///
/// For a role `T`, let `L(T)` be the set of role words `w` with `w ⊑ T` under
/// the role hierarchy, the role chains, and transitivity. An OWL 2 DL role
/// hierarchy is regular, so `L(T)` is accepted by a finite automaton built by
/// unfolding (Horrocks, Kutz, and Sattler, KR 2006): `T` itself; `L(U)` for
/// every strict sub-role `U`; `L(R)L(S)` for every chain `R∘S ⊑ T`; `L(S)*`
/// after `T` for a left-recursive chain `T∘S ⊑ T`; `L(R)*` before `T` for a
/// right-recursive chain `R∘T ⊑ T`; and `L(T)+` when `T` is transitive. A
/// consumer `Γ(x) ∧ T(x,y) ∧ ⋀C_i(y) → Δ(x)` holds for every `T`-path that
/// spells a word of `L(T)`, so it is encoded by markers propagated backwards
/// along the automaton:
///
///   ⋀C_i(x) → M_f(x)                    (final state)
///   R(x,y) ∧ M_q'(y) → M_q(x)           (transition q --R--> q')
///   M_q'(x) → M_q(x)                     (ε-transition q --> q')
///   Γ(x) ∧ M_s(x) → Δ(x)                 (initial state)
///
/// Every marker clause is entailed: `M_q(x)` holds only if some path from `x`
/// spelling a word accepted from `q` reaches a node satisfying every `C_i`,
/// and every accepted word is below `T`. The clauses are therefore additive
/// and sound, and they complete the encoding for consumers of roles whose
/// language is not covered by one chain step or one transitive closure: roles
/// with a non-simple strict sub-role, chains over non-simple roles,
/// self-recursive chains, and transitive roles that are also chain targets.
/// Transitions on a role also fire on edges of its simple sub-roles, which
/// the role-inclusion clauses lift to the super-role.
fn regular_role_automaton_clauses(tbox: &[DLClause], info: &ChainInfo) -> Vec<DLClause> {
    if info.chains.is_empty() && info.trans.is_empty() {
        return Vec::new();
    }
    let trans: HashSet<&str> = info.trans.iter().map(String::as_str).collect();
    let mut sub_roles: HashMap<&str, Vec<&str>> = HashMap::default();
    for c in tbox {
        if let ([Atom::Role(u, us, ut)], [Atom::Role(v, vs, vt)]) = (c.body.as_slice(), c.head.as_slice()) {
            if us == vs && ut == vt && us != ut && u != v {
                sub_roles.entry(v.as_str()).or_default().push(u.as_str());
            }
        }
    }
    for subs in sub_roles.values_mut() {
        subs.sort_unstable();
        subs.dedup();
    }
    let mut chains_into: HashMap<&str, Vec<(&str, &str)>> = HashMap::default();
    for (r, s, t) in &info.chains {
        chains_into.entry(t.as_str()).or_default().push((r.as_str(), s.as_str()));
    }
    // Non-simple roles: chain targets and transitive roles, closed upwards
    // under the role hierarchy.
    let mut super_roles: HashMap<&str, Vec<&str>> = HashMap::default();
    for (sup, subs) in &sub_roles {
        for sub in subs {
            super_roles.entry(sub).or_default().push(sup);
        }
    }
    let mut non_simple: HashSet<&str> = HashSet::default();
    let mut queue: VecDeque<&str> = chains_into.keys().copied().chain(trans.iter().copied()).collect();
    while let Some(role) = queue.pop_front() {
        if non_simple.insert(role) {
            for sup in super_roles.get(role).map(Vec::as_slice).unwrap_or(&[]) {
                queue.push_back(sup);
            }
        }
    }
    // Consumer roles whose language the one-level encodings already cover.
    let needs_automaton = |t: &str| -> bool {
        if !non_simple.contains(t) {
            return false;
        }
        let strict_non_simple_sub = {
            let mut seen: HashSet<&str> = HashSet::default();
            let mut stack: Vec<&str> = sub_roles.get(t).cloned().unwrap_or_default();
            let mut found = false;
            while let Some(u) = stack.pop() {
                if u == t || !seen.insert(u) {
                    continue;
                }
                if non_simple.contains(u) {
                    found = true;
                    break;
                }
                stack.extend(sub_roles.get(u).cloned().unwrap_or_default());
            }
            found
        };
        let chains = chains_into.get(t).map(Vec::as_slice).unwrap_or(&[]);
        strict_non_simple_sub
            || (trans.contains(t) && !chains.is_empty())
            || chains.iter().any(|(r, s)| {
                *r == t || *s == t || non_simple.contains(r) || non_simple.contains(s)
            })
    };

    struct Nfa<'a> {
        states: usize,
        moves: Vec<(usize, &'a str, usize)>,
        epsilon: Vec<(usize, usize)>,
    }
    // Each unfolding gets its own entry and exit states, joined to its
    // context by ε-transitions, so loops of a sub-language stay local to it.
    #[allow(clippy::too_many_arguments)]
    fn build<'a>(
        role: &'a str,
        from: usize,
        to: usize,
        nfa: &mut Nfa<'a>,
        stack: &mut Vec<&'a str>,
        sub_roles: &HashMap<&'a str, Vec<&'a str>>,
        chains_into: &HashMap<&'a str, Vec<(&'a str, &'a str)>>,
        non_simple: &HashSet<&'a str>,
        trans: &HashSet<&'a str>,
    ) {
        let (a, b) = (nfa.states, nfa.states + 1);
        nfa.states += 2;
        nfa.epsilon.push((from, a));
        nfa.epsilon.push((b, to));
        nfa.moves.push((a, role, b));
        if stack.contains(&role) {
            // An equivalent role on the unfolding stack: its words are
            // already produced by the enclosing unfolding.
            return;
        }
        stack.push(role);
        for &sub in sub_roles.get(role).map(Vec::as_slice).unwrap_or(&[]) {
            if non_simple.contains(sub) {
                build(sub, a, b, nfa, stack, sub_roles, chains_into, non_simple, trans);
            }
        }
        for &(r, s) in chains_into.get(role).map(Vec::as_slice).unwrap_or(&[]) {
            if r == role && s == role {
                continue;
            } else if r == role {
                // L(role) L(s)*
                build(s, b, b, nfa, stack, sub_roles, chains_into, non_simple, trans);
            } else if s == role {
                // L(r)* L(role)
                build(r, a, a, nfa, stack, sub_roles, chains_into, non_simple, trans);
            } else {
                let mid = nfa.states;
                nfa.states += 1;
                build(r, a, mid, nfa, stack, sub_roles, chains_into, non_simple, trans);
                build(s, mid, b, nfa, stack, sub_roles, chains_into, non_simple, trans);
            }
        }
        if trans.contains(role) {
            // L(role)+: after a complete word, another one may follow.
            nfa.epsilon.push((b, a));
        }
        stack.pop();
    }

    let x = var_x();
    let y = var_y();
    let mut automata: HashMap<&str, Nfa<'_>> = HashMap::default();
    let mut emitted: HashSet<(String, Vec<String>)> = HashSet::default();
    let mut extra = Vec::new();
    for c in tbox {
        let Some(role) = single_body_role(c) else { continue };
        let (t, source, target) = role_parts(role);
        if *source != x || *target == x || !needs_automaton(t) {
            continue;
        }
        let yt = target.clone();
        let mut c_on_y: Vec<String> = c
            .body
            .iter()
            .filter_map(|a| match a {
                Atom::Concept(name, term) if *term == yt => Some(name.clone()),
                _ => None,
            })
            .collect();
        c_on_y.sort();
        if c_on_y.is_empty()
            || c.head.is_empty()
            || !c.head.iter().all(|h| matches!(h, Atom::Concept(_, term) if *term == x))
        {
            continue;
        }
        let nfa = automata.entry(t).or_insert_with(|| {
            let mut nfa = Nfa { states: 2, moves: Vec::new(), epsilon: Vec::new() };
            let mut stack = Vec::new();
            build(t, 0, 1, &mut nfa, &mut stack, &sub_roles, &chains_into, &non_simple, &trans);
            nfa.moves.sort_unstable();
            nfa.moves.dedup();
            nfa.epsilon.sort_unstable();
            nfa.epsilon.dedup();
            nfa
        });
        let marker = |q: usize| format!("__ria__{}__q{}__{}", t, q, c_on_y.join("_"));
        if emitted.insert((t.to_string(), c_on_y.clone())) {
            extra.push(clause(
                c_on_y.iter().map(|ci| Atom::Concept(ci.clone(), x.clone())),
                [Atom::Concept(marker(1), x.clone())],
            ));
            for &(q, r, q2) in &nfa.moves {
                extra.push(clause(
                    [
                        Atom::Role(r.to_string(), x.clone(), y.clone()),
                        Atom::Concept(marker(q2), y.clone()),
                    ],
                    [Atom::Concept(marker(q), x.clone())],
                ));
            }
            for &(q, q2) in &nfa.epsilon {
                extra.push(clause(
                    [Atom::Concept(marker(q2), x.clone())],
                    [Atom::Concept(marker(q), x.clone())],
                ));
            }
        }
        let mut body: Vec<Atom> = c
            .body
            .iter()
            .filter(|a| matches!(a, Atom::Concept(_, term) if *term == x))
            .cloned()
            .collect();
        body.push(Atom::Concept(marker(0), x.clone()));
        extra.push(clause(body, c.head.iter().cloned()));
    }
    extra
}

/// A minimal automaton over role-atom letters `(role, reversed)` for the
/// marker clauses of [`chain_consumer_automaton_clauses`]: deterministic and
/// minimized when the subset construction stays small, else the ε-free
/// nondeterministic automaton (markers are sets, so either is exact).
#[derive(PartialEq, Eq)]
struct MarkerAutomaton {
    start: usize,
    finals: Vec<usize>,
    moves: Vec<(usize, (String, bool), usize)>,
}

impl MarkerAutomaton {
    const MAX_DFA_STATES: usize = 1024;

    /// The automaton for the forward language (start 0, final 1) or, with
    /// `forward == false`, for its reversal (start 1, final 0).
    fn new(
        states: usize,
        moves: &[(usize, (String, bool), usize)],
        epsilon: &[(usize, usize)],
        forward: bool,
    ) -> Self {
        let (start, final_state) = if forward { (0, 1) } else { (1, 0) };
        let mut out_moves: Vec<Vec<(usize, usize)>> = vec![Vec::new(); states];
        let mut out_eps: Vec<Vec<usize>> = vec![Vec::new(); states];
        let mut letters: Vec<(String, bool)> = moves.iter().map(|(_, l, _)| l.clone()).collect();
        letters.sort();
        letters.dedup();
        let letter_id = |l: &(String, bool)| letters.binary_search(l).expect("letter");
        for (q, l, q2) in moves {
            let (from, to) = if forward { (*q, *q2) } else { (*q2, *q) };
            out_moves[from].push((letter_id(l), to));
        }
        for &(q, q2) in epsilon {
            let (from, to) = if forward { (q, q2) } else { (q2, q) };
            out_eps[from].push(to);
        }
        let closure = |set: &mut Vec<usize>| {
            let mut seen: HashSet<usize> = set.iter().copied().collect();
            let mut stack = set.clone();
            while let Some(q) = stack.pop() {
                for &q2 in &out_eps[q] {
                    if seen.insert(q2) {
                        set.push(q2);
                        stack.push(q2);
                    }
                }
            }
            set.sort_unstable();
            set.dedup();
        };
        // Subset construction.
        let mut first = vec![start];
        closure(&mut first);
        let mut index: HashMap<Vec<usize>, usize> = HashMap::default();
        let mut subsets = vec![first.clone()];
        index.insert(first, 0);
        let mut trans: Vec<Vec<(usize, usize)>> = vec![Vec::new()];
        let mut cursor = 0;
        let mut too_big = false;
        while cursor < subsets.len() {
            let mut by_letter: Vec<Vec<usize>> = vec![Vec::new(); letters.len()];
            for &q in &subsets[cursor] {
                for &(l, q2) in &out_moves[q] {
                    by_letter[l].push(q2);
                }
            }
            for (l, mut target) in by_letter.into_iter().enumerate() {
                if target.is_empty() {
                    continue;
                }
                closure(&mut target);
                let id = match index.get(&target) {
                    Some(&id) => id,
                    None => {
                        let id = subsets.len();
                        index.insert(target.clone(), id);
                        subsets.push(target);
                        trans.push(Vec::new());
                        id
                    }
                };
                trans[cursor].push((l, id));
            }
            cursor += 1;
            if subsets.len() > Self::MAX_DFA_STATES {
                too_big = true;
                break;
            }
        }
        let (n, start, accepting, trans) = if too_big {
            // ε-free automaton over the original states.
            let mut accepting = vec![false; states];
            let mut trans: Vec<Vec<(usize, usize)>> = vec![Vec::new(); states];
            for q in 0..states {
                let mut set = vec![q];
                closure(&mut set);
                accepting[q] = set.contains(&final_state);
                for &q1 in &set {
                    for &(l, q2) in &out_moves[q1] {
                        trans[q].push((l, q2));
                    }
                }
                trans[q].sort_unstable();
                trans[q].dedup();
            }
            (states, start, accepting, trans)
        } else {
            let accepting = subsets.iter().map(|set| set.contains(&final_state)).collect();
            (subsets.len(), 0, accepting, trans)
        };
        // Keep states reachable from the start and co-reachable to a final.
        let mut reach = vec![false; n];
        reach[start] = true;
        let mut stack = vec![start];
        while let Some(q) = stack.pop() {
            for &(_, q2) in &trans[q] {
                if !reach[q2] {
                    reach[q2] = true;
                    stack.push(q2);
                }
            }
        }
        let mut back: Vec<Vec<usize>> = vec![Vec::new(); n];
        for q in 0..n {
            for &(_, q2) in &trans[q] {
                back[q2].push(q);
            }
        }
        let mut live: Vec<bool> = accepting.clone();
        let mut stack: Vec<usize> = (0..n).filter(|&q| live[q]).collect();
        while let Some(q) = stack.pop() {
            for &q0 in &back[q] {
                if !live[q0] {
                    live[q0] = true;
                    stack.push(q0);
                }
            }
        }
        let keep: Vec<bool> = (0..n).map(|q| reach[q] && live[q]).collect();
        // Moore refinement (exact for the deterministic case, a sound
        // bisimulation quotient for the nondeterministic one).
        let mut block: Vec<usize> = (0..n).map(|q| usize::from(accepting[q])).collect();
        let mut count = 0;
        loop {
            let mut signatures: HashMap<(usize, Vec<(usize, usize)>), usize> = HashMap::default();
            let mut next = vec![usize::MAX; n];
            for q in 0..n {
                if !keep[q] {
                    continue;
                }
                let mut sig: Vec<(usize, usize)> = trans[q]
                    .iter()
                    .filter(|&&(_, q2)| keep[q2])
                    .map(|&(l, q2)| (l, block[q2]))
                    .collect();
                sig.sort_unstable();
                sig.dedup();
                let len = signatures.len();
                next[q] = *signatures.entry((block[q], sig)).or_insert(len);
            }
            let new_count = signatures.len();
            block = next;
            if new_count == count {
                break;
            }
            count = new_count;
        }
        // Renumber blocks in order of first appearance from the start.
        let mut number: HashMap<usize, usize> = HashMap::default();
        let mut order = vec![start];
        number.insert(block[start], 0);
        let mut i = 0;
        let mut out_moves = Vec::new();
        while i < order.len() {
            let q = order[i];
            i += 1;
            let mut row: Vec<(usize, usize)> = trans[q].iter().copied().filter(|&(_, q2)| keep[q2]).collect();
            row.sort_unstable();
            for (l, q2) in row {
                let len = number.len();
                let target = *number.entry(block[q2]).or_insert_with(|| {
                    order.push(q2);
                    len
                });
                out_moves.push((number[&block[q]], letters[l].clone(), target));
            }
        }
        out_moves.sort();
        out_moves.dedup();
        let mut finals: Vec<usize> =
            (0..n).filter(|&q| keep[q] && accepting[q]).filter_map(|q| number.get(&block[q]).copied()).collect();
        finals.sort_unstable();
        finals.dedup();
        MarkerAutomaton { start: 0, finals, moves: out_moves }
    }

    /// The automaton without the letters that another letter stands in for:
    /// `l1` is dropped when some kept letter `l2` has every move of `l1` and
    /// every `l1` edge of the clause stream is also an `l2` edge
    /// (`implies(l1, l2)`). Over the stream's edges the two automata accept
    /// the same paths: a path through an `l1` edge runs through the `l2` edge
    /// beside it with the same states, and the reduced automaton's paths are
    /// paths of this one. Re-minimized, so it compares with `==`.
    fn without_implied_letters(&self, implies: &impl Fn(&(String, bool), &(String, bool)) -> bool) -> Self {
        let mut profile: std::collections::BTreeMap<&(String, bool), Vec<(usize, usize)>> =
            std::collections::BTreeMap::new();
        for (q, letter, q2) in &self.moves {
            profile.entry(letter).or_default().push((*q, *q2));
        }
        let letters: Vec<&(String, bool)> = profile.keys().copied().collect();
        let mut dropped: HashSet<&(String, bool)> = HashSet::default();
        // A stand-in stays: its role must keep occurring in the bodies of the
        // emitted clauses, which keeps the inclusions into it alive.
        let mut stand_ins: HashSet<&(String, bool)> = HashSet::default();
        for &l1 in &letters {
            if stand_ins.contains(l1) {
                continue;
            }
            let moves1 = &profile[l1];
            let stand_in = letters.iter().copied().find(|&l2| {
                l2 != l1
                    && !dropped.contains(l2)
                    && moves1.iter().all(|pair| profile[l2].binary_search(pair).is_ok())
                    && implies(l1, l2)
            });
            if let Some(l2) = stand_in {
                dropped.insert(l1);
                stand_ins.insert(l2);
            }
        }
        if dropped.is_empty() {
            return MarkerAutomaton { start: self.start, finals: self.finals.clone(), moves: self.moves.clone() };
        }
        // Re-minimize: state q becomes q + 2, a fresh start 0 enters the
        // start by ε and every final leaves to the fresh final 1 by ε.
        let states = self.moves.iter().flat_map(|(q, _, q2)| [*q, *q2]).chain([self.start]).max().unwrap_or(0) + 3;
        let moves: Vec<(usize, (String, bool), usize)> = self
            .moves
            .iter()
            .filter(|(_, letter, _)| !dropped.contains(letter))
            .map(|(q, letter, q2)| (q + 2, letter.clone(), q2 + 2))
            .collect();
        let mut epsilon = vec![(0, self.start + 2)];
        epsilon.extend(self.finals.iter().map(|f| (f + 2, 1)));
        MarkerAutomaton::new(states, &moves, &epsilon, true)
    }
}

/// Which consumer family a [`chain_consumer_automaton_clauses`] call scans.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ChainConsumerPass {
    /// The normalized TBox that `augment` scans (prefix `c`).
    Tbox,
    /// The `domain_range_clauses` added after `augment` (prefix `d`).
    DomainRange,
    /// Ground negative role assertions in guarded form (prefix `n`).
    Abox,
}

/// Complete role-automaton encoding for every consumer of a role whose
/// language contains a role-chain word.
///
/// The CB worker never materializes chain edges: the raw `R∘S ⊑ T`
/// compositions are filtered from the clause stream, and the one-level
/// [`chain_clauses`] and backward [`regular_role_automaton_clauses`] markers
/// cover only consumers `Γ(x) ∧ T(x,y) ∧ ⋀C_i(y) → Δ(x)` whose head lies on
/// the source of `T` and whose filler is not empty. Three families were
/// therefore lost:
///
/// * consumers with a head atom on the target, `Γ(x) ∧ T(x,y) → Δ(y)`
///   (`∀T.C`, ranges): `chain(s,t) ⊑ r`, `A ⊑ ∃s.∃t.D`, `A ⊑ ∀r.C` missed
///   `A ⊑ ∃r.(C ⊓ D)`;
/// * consumers of a role that reaches a chain only through an inverse
///   (`T⁻` proxies, `U ⊑ T⁻`), whose words the same-orientation unfolding
///   does not produce;
/// * consumers with an empty filler or an empty head on such roles.
///
/// For a role `P`, the unfolding below builds an automaton for `L(P)`, the
/// role words below `P` under the role hierarchy (both orientations),
/// chains and transitivity (Horrocks, Kutz and Sattler, KR 2006). A letter is
/// a role and a direction; a backward letter uses the role's converse proxy
/// when one exists. A consumer is written relative to `P(a,b)` as
/// `Γa(a) ∧ P(a,b) ∧ Γb(b) → Δa(a) ∨ Δb(b)`.
///
/// Forward markers (any consumer with `Δb` non-empty). `F_q(n)` means: for
/// every path from `n` spelling a word accepted from state `q`, its endpoint
/// satisfies `Γb → Δb`:
///
///   Γa(x) → Δa(x) ∨ F_0(x)              (start)
///   F_q(x) ∧ R(x,y) → F_q'(y)            (q --R--> q')
///   F_q(x) → F_q'(x)                     (ε)
///   F_1(x) ∧ Γb(x) → Δb(x)               (final)
///
/// Backward markers (`Δb` empty), as in [`regular_role_automaton_clauses`]:
/// `M_q(n)` means some path from `n` spelling a word accepted from `q`
/// reaches a `Γb` node:
///
///   Γb(x) → M_1(x);  R(x,y) ∧ M_q'(y) → M_q(x);  M_q'(x) → M_q(x);
///   Γa(x) ∧ M_0(x) → Δa(x)
///
/// Every emitted clause holds in each model of the ontology under the stated
/// marker interpretation, so the encoding is a conservative extension
/// (sound). Every word of `L(P)` labels an accepting path, and every letter
/// is a role whose direct edges the clause stream materializes (non-simple
/// letters are unfolded), so the markers reach every node that a chain
/// edge would (complete). The worker and its rules are unchanged; only the
/// clause stream gains these clauses.
///
/// Backward consumers that the existing encodings already cover completely
/// (same-orientation languages: [`chain_clauses`] for a one-level chain
/// target, the backward automaton otherwise, [`domain_consumer_chain_clauses`]
/// for a one-level pure domain) are left to them, so inputs outside the
/// three families keep their clause stream byte for byte.
///
/// Returns the clauses and the number of chain-affected consumers whose shape
/// it cannot encode (atoms other than concepts on the two role endpoints).
pub fn chain_consumer_automaton_clauses(
    consumers: &[DLClause],
    info: &ChainInfo,
    pass: ChainConsumerPass,
) -> (Vec<DLClause>, u64) {
    if info.chains.is_empty() && !(info.ground_edges && !info.trans.is_empty()) {
        return (Vec::new(), 0);
    }
    let trans: HashSet<&str> = info.trans.iter().map(String::as_str).collect();
    let mut same_into: HashMap<&str, Vec<&str>> = HashMap::default();
    let mut same_up: HashMap<&str, Vec<&str>> = HashMap::default();
    for (u, v) in &info.sub_same {
        same_into.entry(v.as_str()).or_default().push(u.as_str());
        same_up.entry(u.as_str()).or_default().push(v.as_str());
    }
    let mut inv_into: HashMap<&str, Vec<&str>> = HashMap::default();
    let mut inv_up: HashMap<&str, Vec<&str>> = HashMap::default();
    let inv_pairs: HashSet<(&str, &str)> =
        info.sub_inv.iter().map(|(u, v)| (u.as_str(), v.as_str())).collect();
    for (u, v) in &info.sub_inv {
        inv_into.entry(v.as_str()).or_default().push(u.as_str());
        inv_up.entry(u.as_str()).or_default().push(v.as_str());
    }
    // A converse proxy: `R(x,y) → S(y,x)` and `S(x,y) → R(y,x)` both present.
    let converse = |r: &str| -> Option<&str> {
        // A symmetric role (`R(x,y) → R(y,x)`) is its own converse.
        if let Some(&own) = inv_up.get(r).and_then(|ups| ups.iter().find(|&&s| s == r)) {
            return Some(own);
        }
        let mut best: Option<&str> = None;
        for &s in inv_up.get(r).map(Vec::as_slice).unwrap_or(&[]) {
            if s != r && inv_pairs.contains(&(s, r)) && best.is_none_or(|b| s < b) {
                best = Some(s);
            }
        }
        best
    };
    let mut chains_into: HashMap<&str, Vec<(&str, &str)>> = HashMap::default();
    for (r, s, t) in &info.chains {
        chains_into.entry(t.as_str()).or_default().push((r.as_str(), s.as_str()));
    }
    // Upward closure (both orientations) from a seed set.
    fn close_up<'a>(
        seed: Vec<&'a str>,
        same_up: &HashMap<&'a str, Vec<&'a str>>,
        inv_up: &HashMap<&'a str, Vec<&'a str>>,
    ) -> HashSet<&'a str> {
        let mut out: HashSet<&str> = HashSet::default();
        let mut queue: VecDeque<&str> = seed.into_iter().collect();
        while let Some(role) = queue.pop_front() {
            if out.insert(role) {
                for &v in same_up.get(role).map(Vec::as_slice).unwrap_or(&[]) {
                    queue.push_back(v);
                }
                for &v in inv_up.get(role).map(Vec::as_slice).unwrap_or(&[]) {
                    queue.push_back(v);
                }
            }
        }
        out
    }
    // Roles whose language contains a chain word.
    // Over ground role assertions a transitive role's closure is not created
    // by existentials either, so its consumers need the automaton as well.
    let affected = close_up(
        chains_into
            .keys()
            .copied()
            .chain(trans.iter().copied().filter(|_| info.ground_edges))
            .collect(),
        &same_up,
        &inv_up,
    );
    if affected.is_empty() {
        return (Vec::new(), 0);
    }
    // Roles whose edges the clause stream does not all materialize.
    let non_simple = close_up(
        chains_into.keys().copied().chain(trans.iter().copied()).collect(),
        &same_up,
        &inv_up,
    );
    // The existing (same-orientation) encodings' notion of non-simple roles
    // and of the roles that receive a backward automaton.
    let existing_non_simple = {
        let mut out: HashSet<&str> = HashSet::default();
        let mut queue: VecDeque<&str> =
            chains_into.keys().copied().chain(trans.iter().copied()).collect();
        while let Some(role) = queue.pop_front() {
            if out.insert(role) {
                for &v in same_up.get(role).map(Vec::as_slice).unwrap_or(&[]) {
                    queue.push_back(v);
                }
            }
        }
        out
    };
    let existing_automaton = |t: &str| -> bool {
        if !existing_non_simple.contains(t) {
            return false;
        }
        let mut seen: HashSet<&str> = HashSet::default();
        let mut stack: Vec<&str> = same_into.get(t).cloned().unwrap_or_default();
        while let Some(u) = stack.pop() {
            if u == t || !seen.insert(u) {
                continue;
            }
            if existing_non_simple.contains(u) {
                return true;
            }
            stack.extend(same_into.get(u).cloned().unwrap_or_default());
        }
        let chains = chains_into.get(t).map(Vec::as_slice).unwrap_or(&[]);
        (trans.contains(t) && !chains.is_empty())
            || chains.iter().any(|(r, s)| {
                *r == t || *s == t || existing_non_simple.contains(r) || existing_non_simple.contains(s)
            })
    };

    type Letter<'a> = (&'a str, bool);
    struct Nfa<'a> {
        states: usize,
        moves: Vec<(usize, Letter<'a>, usize)>,
        epsilon: Vec<(usize, usize)>,
        inverted: bool,
    }
    struct Graph<'g, 'a> {
        same_into: &'g HashMap<&'a str, Vec<&'a str>>,
        inv_into: &'g HashMap<&'a str, Vec<&'a str>>,
        chains_into: &'g HashMap<&'a str, Vec<(&'a str, &'a str)>>,
        non_simple: &'g HashSet<&'a str>,
        trans: &'g HashSet<&'a str>,
    }
    // Words of `L(role)` (forward) or of its converse (`fwd == false`), from
    // `from` to `to`; each unfolding gets its own entry and exit states.
    fn build<'a>(
        role: &'a str,
        fwd: bool,
        from: usize,
        to: usize,
        nfa: &mut Nfa<'a>,
        stack: &mut Vec<Letter<'a>>,
        g: &Graph<'_, 'a>,
    ) {
        let (a, b) = (nfa.states, nfa.states + 1);
        nfa.states += 2;
        nfa.epsilon.push((from, a));
        nfa.epsilon.push((b, to));
        nfa.moves.push((a, (role, fwd), b));
        if !fwd {
            nfa.inverted = true;
        }
        if stack.contains(&(role, fwd)) {
            return;
        }
        stack.push((role, fwd));
        for &sub in g.same_into.get(role).map(Vec::as_slice).unwrap_or(&[]) {
            if g.non_simple.contains(sub) {
                build(sub, fwd, a, b, nfa, stack, g);
            }
        }
        for &sub in g.inv_into.get(role).map(Vec::as_slice).unwrap_or(&[]) {
            if g.non_simple.contains(sub) {
                build(sub, !fwd, a, b, nfa, stack, g);
            }
        }
        for &(r, s) in g.chains_into.get(role).map(Vec::as_slice).unwrap_or(&[]) {
            // Forward words are L(r)L(s); converse words are L(s⁻)L(r⁻).
            let (first, second) = if fwd { (r, s) } else { (s, r) };
            if r == role && s == role {
                continue;
            } else if first == role {
                build(second, fwd, b, b, nfa, stack, g);
            } else if second == role {
                build(first, fwd, a, a, nfa, stack, g);
            } else {
                let mid = nfa.states;
                nfa.states += 1;
                build(first, fwd, a, mid, nfa, stack, g);
                build(second, fwd, mid, b, nfa, stack, g);
            }
        }
        if g.trans.contains(role) {
            nfa.epsilon.push((b, a));
        }
        stack.pop();
    }
    let graph = Graph {
        same_into: &same_into,
        inv_into: &inv_into,
        chains_into: &chains_into,
        non_simple: &non_simple,
        trans: &trans,
    };
    // `edge_implies(l1, l2)`: every edge of letter `l1` (a role read forward
    // or reversed) is an edge of letter `l2` through role inclusion clauses
    // of the stream: same-orientation inclusions, then at most one inverted
    // inclusion whose head is `l2`'s role. That head occurs in the bodies of
    // the encodings `l2` belongs to, so neither bridge pruning pass removes
    // the inverted inclusion; same-orientation inclusions are never pruned.
    let edge_implies = |l1: &(String, bool), l2: &(String, bool)| -> bool {
        let mut seen: HashSet<&str> = HashSet::default();
        let mut stack = vec![l1.0.as_str()];
        while let Some(u) = stack.pop() {
            if !seen.insert(u) {
                continue;
            }
            if l1.1 == l2.1 && u == l2.0 {
                return true;
            }
            if l1.1 != l2.1 && inv_pairs.contains(&(u, l2.0.as_str())) {
                return true;
            }
            stack.extend(same_up.get(u).map(Vec::as_slice).unwrap_or(&[]).iter().copied());
        }
        false
    };
    // A letter of a role that no clause of the stream ever creates an edge
    // for can never fire; dropping it removes only unrealizable words.
    let generated = |role: &str| info.generated_roles.as_ref().is_none_or(|set| set.contains(role));
    let mut nfas: HashMap<&str, Nfa<'_>> = HashMap::default();
    let mut dfas: HashMap<(&str, bool), MarkerAutomaton> = HashMap::default();
    let mut grouped: HashMap<(&str, bool), Vec<(usize, (String, bool), usize)>> = HashMap::default();
    let mut same_language: HashMap<&str, bool> = HashMap::default();
    let no_inverse: HashMap<&str, Vec<&str>> = HashMap::default();
    let same_graph = Graph {
        same_into: &same_into,
        inv_into: &no_inverse,
        chains_into: &chains_into,
        non_simple: &existing_non_simple,
        trans: &trans,
    };
    let tag = match pass {
        ChainConsumerPass::Tbox => "c",
        ChainConsumerPass::DomainRange => "d",
        ChainConsumerPass::Abox => "n",
    };
    let x = var_x();
    let y = var_y();
    let mut extra = Vec::new();
    let mut emitted: HashSet<DLClause> = HashSet::default();
    let mut unencoded = 0u64;
    // A marker family is shared by every consumer with the same role,
    // direction and seed condition: `Γa ∧ ¬Δa` forward, `Γb` backward.
    let mut families: HashMap<(bool, &str, Vec<String>, Vec<String>), usize> = HashMap::default();
    // Plain consumers with an empty seed side on any role: `q(x,y) ∧ Γ(y) →
    // Δ(y)` (forward) and `q(x,y) ∧ Γ(x) → Δ(x)` (backward).
    type Plain<'c> = HashMap<&'c str, Vec<(Vec<String>, Vec<String>)>>;
    let mut plain_forward: Plain<'_> = HashMap::default();
    let mut plain_backward: Plain<'_> = HashMap::default();
    for c in consumers {
        let Some(Atom::Role(q, Term::Var(a), Term::Var(b))) = single_body_role(c) else { continue };
        if a == b {
            continue;
        }
        let on = |atoms: &[Atom], v: &str| -> Option<Vec<String>> {
            let mut out = Vec::new();
            for atom in atoms {
                match atom {
                    Atom::Role(..) => {}
                    Atom::Concept(name, Term::Var(t)) if t == v => out.push(name.clone()),
                    Atom::Concept(_, Term::Var(t)) if t == a || t == b => {}
                    _ => return None,
                }
            }
            Some(out)
        };
        let (Some(ba), Some(bb), Some(ha), Some(hb)) = (on(&c.body, a), on(&c.body, b), on(&c.head, a), on(&c.head, b))
        else {
            continue;
        };
        if c.head.iter().any(|atom| !matches!(atom, Atom::Concept(..))) {
            continue;
        }
        if ba.is_empty() && ha.is_empty() && !hb.is_empty() {
            plain_forward.entry(q.as_str()).or_default().push((bb, hb));
        } else if bb.is_empty() && hb.is_empty() {
            plain_backward.entry(q.as_str()).or_default().push((ba, ha));
        }
    }
    let up_same = |role: &str| -> Vec<String> {
        let mut out = vec![role.to_string()];
        let mut i = 0;
        while i < out.len() {
            let current = out[i].clone();
            for &sup in same_up.get(current.as_str()).map(Vec::as_slice).unwrap_or(&[]) {
                if !out.iter().any(|r| r == sup) {
                    out.push(sup.to_string());
                }
            }
            i += 1;
        }
        out
    };
    for c in consumers {
        let Some(role_atom) = single_body_role(c) else { continue };
        let (p, a, b) = role_parts(role_atom);
        if !affected.contains(p) {
            continue;
        }
        if c.body.len() == 1 && c.head.len() == 1 && matches!(c.head[0], Atom::Role(..)) {
            continue; // a role inclusion, part of the automaton itself
        }
        let concept_on = |atoms: &[Atom], term: &Term| -> Vec<String> {
            let mut out: Vec<String> = atoms
                .iter()
                .filter_map(|atom| match atom {
                    Atom::Concept(name, t) if t == term => Some(name.clone()),
                    _ => None,
                })
                .collect();
            out.sort();
            out.dedup();
            out
        };
        let representable = matches!(a, Term::Var(_))
            && matches!(b, Term::Var(_))
            && a != b
            && c.body.iter().all(|atom| {
                atom == role_atom || matches!(atom, Atom::Concept(_, t) if t == a || t == b)
            })
            && c.head.iter().all(|atom| matches!(atom, Atom::Concept(_, t) if t == a || t == b));
        if !representable {
            unencoded += 1;
            continue;
        }
        let gamma_a = concept_on(&c.body, a);
        let gamma_b = concept_on(&c.body, b);
        let delta_a = concept_on(&c.head, a);
        let delta_b = concept_on(&c.head, b);
        let forward = !delta_b.is_empty();
        let nfa = nfas.entry(p).or_insert_with(|| {
            let mut nfa = Nfa { states: 2, moves: Vec::new(), epsilon: Vec::new(), inverted: false };
            let mut stack = Vec::new();
            build(p, true, 0, 1, &mut nfa, &mut stack, &graph);
            nfa.moves.sort_unstable();
            nfa.moves.dedup();
            nfa.epsilon.sort_unstable();
            nfa.epsilon.dedup();
            nfa
        });
        let automaton: &MarkerAutomaton = dfas.entry((p, forward)).or_insert_with(|| {
            // Resolve each letter to a role atom: a backward letter uses the
            // converse proxy when there is one, else the reversed atom.
            let moves: Vec<(usize, (String, bool), usize)> = nfa
                .moves
                .iter()
                .map(|&(q, (r, fwd), q2)| {
                    let letter = match (fwd, converse(r)) {
                        (true, _) => (r.to_string(), false),
                        (false, Some(s)) => (s.to_string(), false),
                        (false, None) => (r.to_string(), true),
                    };
                    (q, letter, q2)
                })
                .filter(|(_, (role, _), _)| generated(role))
                .collect();
            // Letters whose edges another letter with the same moves already
            // carries add no path (and would each need a copy of their edges
            // in a group role).
            MarkerAutomaton::new(nfa.states, &moves, &nfa.epsilon, forward).without_implied_letters(&edge_implies)
        });
        if !forward {
            // Leave consumers that the same-orientation encodings already
            // cover completely to them: those encodings implement exactly the
            // language of the same-orientation unfolding, so they are
            // complete when that language equals `L(p)`.
            let one_level = chains_into.contains_key(p) && !existing_automaton(p);
            // `transitivity_clauses` and `domain_consumer_chain_clauses`
            // recognize `p⁺` for a transitive role without chains.
            let transitive_only = trans.contains(p) && !chains_into.contains_key(p);
            let shape = match pass {
                ChainConsumerPass::Tbox => {
                    *a == x
                        && !gamma_b.is_empty()
                        && !c.head.is_empty()
                        && (one_level || existing_automaton(p) || transitive_only)
                }
                ChainConsumerPass::DomainRange => {
                    *a == x && gamma_b.is_empty() && !c.head.is_empty() && (one_level || transitive_only)
                }
                ChainConsumerPass::Abox => false,
            };
            let covered = shape
                && *same_language.entry(p).or_insert_with(|| {
                    let mut same = Nfa { states: 2, moves: Vec::new(), epsilon: Vec::new(), inverted: false };
                    let mut stack = Vec::new();
                    build(p, true, 0, 1, &mut same, &mut stack, &same_graph);
                    let same_moves: Vec<(usize, (String, bool), usize)> = same
                        .moves
                        .iter()
                        .map(|&(q, (r, _), q2)| (q, (r.to_string(), false), q2))
                        .filter(|(_, (role, _), _)| generated(role))
                        .collect();
                    if same.inverted {
                        return false;
                    }
                    let same_automaton = MarkerAutomaton::new(same.states, &same_moves, &same.epsilon, false);
                    // A letter whose every edge the stream also materializes as
                    // an edge of another letter with the same moves adds no
                    // path (a reversed sub-role of an inverse, say `starts⁻`
                    // beside `has_part` when `starts ⊑ part_of`); compare
                    // without such letters.
                    same_automaton == *automaton || same_automaton.without_implied_letters(&edge_implies) == *automaton
                });
            if covered {
                continue;
            }
        }
        // A consumer with an empty seed condition (a range `p(x,y) → C(y)`,
        // a domain `p(x,y) → D(x)`, or the like) needs only the last letter
        // of an accepted word (forward), respectively its first letter
        // (backward; the reversed automaton's last letter): the word's edge
        // for that letter exists in the clause stream, as an edge of every
        // role above it in the same orientation. If each such letter has a
        // plain consumer of at least the same strength on one of those
        // roles, that consumer already fires wherever the markers would
        // (the EL-style range condition `range(p) ⊆ range(last letter)`,
        // which OBO ontologies satisfy), and the family is redundant.
        let seed_empty = if forward {
            gamma_a.is_empty() && delta_a.is_empty()
        } else {
            gamma_b.is_empty()
        };
        if seed_empty {
            let (need_body, need_head) = if forward { (&gamma_b, &delta_b) } else { (&gamma_a, &delta_a) };
            let plain = if forward { &plain_forward } else { &plain_backward };
            let covered_by_letters = automaton.moves.iter().all(|(_, (letter, reversed), q2)| {
                if !automaton.finals.contains(q2) {
                    return true;
                }
                !*reversed
                    && up_same(letter).iter().any(|role| {
                        plain.get(role.as_str()).is_some_and(|list| {
                            list.iter().any(|(body, head)| {
                                body.iter().all(|c| need_body.contains(c))
                                    && head.iter().all(|c| need_head.contains(c))
                            })
                        })
                    })
            });
            if covered_by_letters {
                continue;
            }
        }
        let seed_key = if forward { (gamma_a.clone(), delta_a.clone()) } else { (gamma_b.clone(), Vec::new()) };
        let next = families.len();
        let mut fresh = false;
        let index = *families
            .entry((forward, p, seed_key.0.clone(), seed_key.1.clone()))
            .or_insert_with(|| {
                fresh = true;
                next
            });
        let kind = if forward { "riaf" } else { "riab" };
        // The seed state holds everywhere when the seed condition is empty.
        let universal = seed_key.0.is_empty() && seed_key.1.is_empty();
        let marker = |q: usize| format!("__{kind}__{p}__{tag}{index}__q{q}");
        let marker_atom = |q: usize, term: &Term| -> Option<Atom> {
            (!(universal && q == automaton.start)).then(|| Atom::Concept(marker(q), term.clone()))
        };
        let mut push = |clause: DLClause, extra: &mut Vec<DLClause>| {
            if emitted.insert(clause.clone()) {
                extra.push(clause);
            }
        };
        if fresh && !grouped.contains_key(&(p, forward)) {
            // Letters with the same transitions everywhere in this automaton
            // are merged into one fresh super-role, materialized once per
            // automaton, so each marker family pays one move per group
            // instead of one per letter (OBO roles have dozens of letters
            // that only loop on one state).
            let mut profile: std::collections::BTreeMap<(String, bool), Vec<(usize, usize)>> =
                std::collections::BTreeMap::new();
            for (q, letter, q2) in &automaton.moves {
                profile.entry(letter.clone()).or_default().push((*q, *q2));
            }
            let mut by_profile: std::collections::BTreeMap<Vec<(usize, usize)>, Vec<(String, bool)>> =
                std::collections::BTreeMap::new();
            for (letter, mut pairs) in profile {
                pairs.sort_unstable();
                by_profile.entry(pairs).or_default().push(letter);
            }
            let dir = if forward { "f" } else { "b" };
            let mut moves = Vec::new();
            let mut defs = Vec::new();
            for (index, (pairs, letters)) in by_profile.into_iter().enumerate() {
                let letter = if letters.len() >= 2 {
                    let group = format!("__riaz__{p}__{tag}{dir}{index}");
                    for (role, reversed) in &letters {
                        let (s0, t0) = if *reversed { (y.clone(), x.clone()) } else { (x.clone(), y.clone()) };
                        defs.push(clause(
                            [Atom::Role(role.clone(), x.clone(), y.clone())],
                            [Atom::Role(group.clone(), s0, t0)],
                        ));
                    }
                    (group, false)
                } else {
                    letters.into_iter().next().expect("a profile has a letter")
                };
                for (q, q2) in pairs {
                    moves.push((q, letter.clone(), q2));
                }
            }
            moves.sort();
            for def in defs {
                push(def, &mut extra);
            }
            grouped.insert((p, forward), moves);
        }
        if fresh {
            for (q, (role, reversed), q2) in &grouped[&(p, forward)] {
                // Every transition clause uses the role atom `role(x,y)`. A
                // reversed letter moves a marker against the edge, which is
                // the same clause read with the two variables swapped.
                let edge = Atom::Role(role.clone(), x.clone(), y.clone());
                // Forward markers move from the letter's source to its target,
                // backward markers from target to source.
                let (from, to) = if forward != *reversed { (&x, &y) } else { (&y, &x) };
                let Some(head) = marker_atom(*q2, to) else { continue };
                push(clause(marker_atom(*q, from).into_iter().chain([edge]), [head]), &mut extra);
            }
            if !universal {
                let seed_body = seed_key.0.iter().map(|name| Atom::Concept(name.clone(), x.clone()));
                let seed_head = seed_key
                    .1
                    .iter()
                    .map(|name| Atom::Concept(name.clone(), x.clone()))
                    .chain(marker_atom(automaton.start, &x));
                push(clause(seed_body, seed_head), &mut extra);
            }
        }
        // The consumer's own clause at every accepting state.
        for &f in &automaton.finals {
            if forward {
                // R_f(x) ∧ Γb(x) → Δb(x)
                push(
                    clause(
                        marker_atom(f, &x)
                            .into_iter()
                            .chain(gamma_b.iter().map(|name| Atom::Concept(name.clone(), x.clone()))),
                        delta_b.iter().map(|name| Atom::Concept(name.clone(), x.clone())),
                    ),
                    &mut extra,
                );
            } else {
                // Γa(x) ∧ M_f(x) → Δa(x)
                push(
                    clause(
                        gamma_a
                            .iter()
                            .map(|name| Atom::Concept(name.clone(), x.clone()))
                            .chain(marker_atom(f, &x)),
                        delta_a.iter().map(|name| Atom::Concept(name.clone(), x.clone())),
                    ),
                    &mut extra,
                );
            }
        }
    }
    (extra, unencoded)
}

/// Drop inverse-bridge clauses whose derived atoms nothing can consume.
///
/// `link_inverse` emits both `R(x,y) -> S(y,x)` and `S(x,y) -> R(y,x)` for
/// every inverse pair. A bridge only does work if the atoms it derives can
/// fire another clause, i.e. its head role occurs in the body of some
/// non-bridge clause. Run after `augment` and `domain_range_clauses`, so the
/// transitivity/chain encodings and domain/range consumers are all visible.
///
/// Completeness argument for the drop: if the head role `S` has no non-bridge
/// body occurrence, the only clause that can consume a derived `S(y,x)` is the
/// partner bridge `S(x,y) -> R(y,x)`, and that round trip re-derives exactly
/// the `R(x,y)` the bridge fired from. The derived set of concept atoms is
/// unchanged, so subsumptions and unsatisfiability are unaffected. If `S` has
/// a bridge onward to a third role the clause is kept (conservatively, even
/// though that bridge may itself be dead).
///
/// On taxonomy-plus-positive-existential ontologies the pair is never
/// consumed and both directions go away, removing the per-edge backward
/// propagation entirely (ore_ont_3414: 7515 `∃part_of` successors each also
/// spawned a `has_part` back edge, tipping it over the 240 s budget).
pub fn prune_dead_inverse_bridges(tbox: &mut Vec<DLClause>, pairs: &[(String, String)]) {
    if pairs.is_empty() {
        return;
    }
    let mut bridge_edges: HashSet<(&str, &str)> = HashSet::default();
    let mut partners: HashMap<&str, Vec<&str>> = HashMap::default();
    for (r, s) in pairs {
        bridge_edges.insert((r.as_str(), s.as_str()));
        bridge_edges.insert((s.as_str(), r.as_str()));
        partners.entry(r.as_str()).or_default().push(s.as_str());
        partners.entry(s.as_str()).or_default().push(r.as_str());
    }
    // A bridge is exactly the swapped-orientation shape `link_inverse` emits,
    // over a registered pair.
    let is_bridge = |c: &DLClause| -> bool {
        if c.body.len() != 1 || c.head.len() != 1 {
            return false;
        }
        match (&c.body[0], &c.head[0]) {
            (Atom::Role(r, rs, rt), Atom::Role(s, ss, st)) => {
                rs == st && rt == ss && rs != rt && bridge_edges.contains(&(r.as_str(), s.as_str()))
            }
            _ => false,
        }
    };
    let mut consumed: HashSet<String> = HashSet::default();
    for c in tbox.iter() {
        if is_bridge(c) {
            continue;
        }
        for a in &c.body {
            if let Atom::Role(r, _, _) = a {
                consumed.insert(r.clone());
            }
        }
    }
    tbox.retain(|c| {
        if !is_bridge(c) {
            return true;
        }
        let (r, s) = match (&c.body[0], &c.head[0]) {
            (Atom::Role(r, _, _), Atom::Role(s, _, _)) => (r.as_str(), s.as_str()),
            _ => unreachable!("is_bridge admits only role-role clauses"),
        };
        if consumed.contains(s) {
            return true;
        }
        partners
            .get(s)
            .map(|ts| ts.iter().any(|t| *t != r))
            .unwrap_or(false)
    });
}

/// Roles whose edges can influence a named-concept subsumption ("concept
/// relevant"). The set of roles whose edges can influence a *named*-class
/// subsumption or unsatisfiability. Computed as a BACKWARD slice from the query
/// goals: named concepts (a subsumption query is about named classes),
/// equalities (merges), and empty heads (`⊥` / unsat constraints). A clause is
/// "active" if its head contains a goal atom — a named concept, an equality, an
/// empty head, or an *already-needed* synthetic concept or role. Every atom in
/// an active clause's body then becomes needed, and the slice iterates to a
/// fixpoint. A role is relevant iff it ends up needed.
///
/// Symmetric / inverse axioms only add *reverse* edges for their role. If the
/// role is not in the slice, no reverse edge it produces is ever read along a
/// chain that reaches a named concept, equality, or `⊥`, so the symmetry /
/// inverse is inert: dropping it changes no named-class subsumption and the
/// ontology can take the EL fast path. (A forward "feeds any concept head"
/// test is too coarse — it flags a role that only feeds a synthetic existential
/// definer `Q_i ≡ ∃R.C` that no named subsumption ever consumes, e.g.
/// RO_0002158 in the ORE giants. The backward slice excludes those.)
///
/// Conservative toward soundness: equalities and empty heads are always goals,
/// and any concept that is not recognisably synthetic (`Q_*` / `__*`) is a
/// goal, so the slice only ever errs toward marking a role relevant (keeping it
/// on the CB engine).
pub fn concept_relevant_roles(tbox: &[DLClause]) -> HashSet<String> {
    fn is_synthetic(name: &str) -> bool {
        name.starts_with("Q_") || name.starts_with("__")
    }
    // Building reverse indexes has a fixed allocation cost and only pays off
    // on large normalized clause sets. Keep the established scan on ordinary
    // ontologies, which also leaves the corpus-median memory path untouched.
    if tbox.len() < 10_000 {
        let mut needed_concepts: HashSet<&str> = HashSet::default();
        let mut needed_roles: HashSet<String> = HashSet::default();
        let mut changed = true;
        while changed {
            changed = false;
            for c in tbox {
                let active = c.head.is_empty()
                    || c.head.iter().any(|a| match a {
                        Atom::Concept(n, t) => {
                            (!is_synthetic(n) && !matches!(t, Term::Fun(..)))
                                || needed_concepts.contains(n.as_str())
                        }
                        Atom::Eq(..) => true,
                        Atom::Role(r, _, _) => needed_roles.contains(r),
                    });
                if !active {
                    continue;
                }
                for a in &c.body {
                    match a {
                        Atom::Concept(n, _) => changed |= needed_concepts.insert(n),
                        Atom::Role(r, _, _) => changed |= needed_roles.insert(r.clone()),
                        Atom::Eq(..) => {}
                    }
                }
            }
        }
        return needed_roles;
    }
    // This is backward graph reachability. The former implementation rescanned
    // every clause after each growing wave of needed symbols. Index the heads
    // of clauses that are not goals initially, then activate each clause once
    // when one of its head symbols becomes needed.
    let mut concept_heads: HashMap<&str, Vec<usize>> = HashMap::default();
    let mut role_heads: HashMap<&str, Vec<usize>> = HashMap::default();
    let mut pending = VecDeque::new();
    for (index, c) in tbox.iter().enumerate() {
        let initial = c.head.is_empty()
            || c.head.iter().any(|a| match a {
                // A named concept is a query goal only on a non-Skolem term:
                // a named concept on a function term f(x) is an existential
                // filler rather than a central subsumption goal.
                Atom::Concept(n, t) => !is_synthetic(n) && !matches!(t, Term::Fun(..)),
                Atom::Eq(..) => true,
                Atom::Role(..) => false,
            });
        if initial {
            pending.push_back(index);
        } else {
            for atom in &c.head {
                match atom {
                    Atom::Concept(name, _) => concept_heads.entry(name).or_default().push(index),
                    Atom::Role(role, _, _) => role_heads.entry(role).or_default().push(index),
                    Atom::Eq(..) => unreachable!("equality heads are initial goals"),
                }
            }
        }
    }

    let mut activated = vec![false; tbox.len()];
    let mut needed_concepts: HashSet<&str> = HashSet::default();
    let mut needed_roles: HashSet<&str> = HashSet::default();
    while let Some(index) = pending.pop_front() {
        if std::mem::replace(&mut activated[index], true) {
            continue;
        }
        for atom in &tbox[index].body {
            let dependents = match atom {
                Atom::Concept(name, _) if needed_concepts.insert(name) => {
                    concept_heads.get(name.as_str())
                }
                Atom::Role(role, _, _) if needed_roles.insert(role) => {
                    role_heads.get(role.as_str())
                }
                _ => None,
            };
            if let Some(dependents) = dependents {
                pending.extend(dependents.iter().copied());
            }
        }
    }
    needed_roles.into_iter().map(str::to_owned).collect()
}

/// Drop the reverse-edge clauses for *inert* symmetric and inverse roles — the
/// symmetric self-bridge `R(x,y) -> R(y,x)` for a symmetric `R` and the inverse
/// bridges `R(x,y) -> S(y,x)` / `S(x,y) -> R(y,x)` for an inverse pair `(R, S)`,
/// whenever every role involved is not in `relevant`. Removing an inert bridge
/// changes no named-concept subsumption (its reverse edges feed no concept), so
/// this is sound for the CB engine and leaves a pure-EL clause set that the EL
/// fast path accepts (it otherwise rejects the swapped-orientation role head).
pub fn prune_inert_role_bridges(
    tbox: &mut Vec<DLClause>,
    symmetric_roles: &[String],
    inverse_pairs: &[(String, String)],
    relevant: &HashSet<String>,
) {
    let sym_inert: HashSet<&str> = symmetric_roles
        .iter()
        .map(String::as_str)
        .filter(|r| !relevant.contains(*r))
        .collect();
    let inv_inert: HashSet<(&str, &str)> = inverse_pairs
        .iter()
        .filter(|(r, s)| !relevant.contains(r) && !relevant.contains(s))
        .flat_map(|(r, s)| [(r.as_str(), s.as_str()), (s.as_str(), r.as_str())])
        .collect();
    if sym_inert.is_empty() && inv_inert.is_empty() {
        return;
    }
    tbox.retain(|c| {
        if c.body.len() != 1 || c.head.len() != 1 {
            return true;
        }
        match (&c.body[0], &c.head[0]) {
            (Atom::Role(r, rs, rt), Atom::Role(s, ss, st)) if rs == st && rt == ss && rs != rt => {
                let drop = (r == s && sym_inert.contains(r.as_str()))
                    || inv_inert.contains(&(r.as_str(), s.as_str()));
                !drop
            }
            _ => true,
        }
    });
}

// ===========================================================================
// Role-automaton reachability (KM_ROLE_AUTOMATON)
//
// Konclude compiles transitive roles + role chains + the sub-role hierarchy
// into a per-role automaton, then propagates `∃R.C` (and `∀R.C`) through it
// at tableau runtime via a per-node per-role reapply queue that re-fires on
// every newly created edge (incl. generated successors).  See
// CRoleChainAutomataTransformationPreProcess + applyALLRule +
// CExtractPropagationIntoCreationDirectionPreProcess.
//
// KM's shared-filler QoSat model cannot fire that forward push across a
// generated/shared successor soundly (the r-Succ gap), so the marker
// `__trans__R__C` — which propagates `∃R.C ⊑ D` consumers up a transitive R —
// never reaches the root on chain-composed routes (ore_ont_14817: 71 missing
// `X ⊑ ∃develops_from.UBERON_0000926`-style subsumptions, all reached only
// through `part_of ∘ develops_from ⊑ develops_from` / dev-transitivity).
//
// This pass closes that gap with a SOUND, FINITE preprocessing closure over
// NAMED classes, mirroring what Konclude's automaton derives at runtime:
//   - transitivity of R:     `A ⊑ ∃R.B ∧ B ⊑ ∃R.C  ⟹  A ⊑ ∃R.C`
//   - chain R1∘R2 ⊑ R:       `A ⊑ ∃R1.B ∧ B ⊑ ∃R2.C  ⟝  A ⊑ ∃R.C`
//   - sub-role S ⊑ R:        `A ⊑ ∃S.C  ⟝  A ⊑ ∃R.C`   (and in the filler)
// Each newly-derived `A ⊑ ∃R.C` is emitted as the two clausal fragments the
// rest of the pipeline already consumes:
//   introducer: `A(x) → marker_R_C(x)`         (the exists obligation, as the
//              marker concept the transitivity/chain machinery propagates)
//   consumer:   `marker_R_C(x) → D(x)`          for every `∃R.C ⊑ D` consumer
// where `marker_R_C` is the existing `__trans__R__C` name so the in-engine
// propagation rides the SAME predicate (no new derivation paths, only new
// SEED facts — the derived set grows monotonically, soundly).  Additive: only
// emits clauses for (A, R, C) triples not already present.  Default OFF.
// ===========================================================================

/// Collect `∃R.C` introducers `A ⊑ ∃R.C` from the clausified tbox.  After
/// normalisation an `A ⊑ ∃R.C` axiom is the exists-introducing clause
/// `A(x) → R(x,f) ∧ C(f)` (role + filler concept in the HEAD).  Returns the
/// set of `(A, R, C)` triples (A and C are concept names, R a role name).
fn collect_exists_introducers(tbox: &[DLClause]) -> HashSet<(String, String, String)> {
    let x = var_x();
    let mut out = HashSet::default();
    for c in tbox {
        // introducer shape: body = [Concept(A, x)], head = [Role(R, x, t), Concept(C, t)]
        if c.body.len() != 1 || c.head.len() != 2 {
            continue;
        }
        let ba = match &c.body[0] {
            Atom::Concept(name, t) if *t == x => name.clone(),
            _ => continue,
        };
        let mut role: Option<(&str, &Term)> = None;
        let mut fil: Option<&str> = None;
        for h in &c.head {
            match h {
                Atom::Role(r, s, t) if *s == x => role = Some((r.as_str(), t)),
                Atom::Concept(name, t) if *t != x => {
                    if fil.is_none() {
                        fil = Some(name.as_str());
                    }
                }
                _ => {}
            }
        }
        let (r, t) = match role {
            Some((r, t)) => (r.to_string(), t),
            None => continue,
        };
        let c_name = match fil {
            Some(c) => c.to_string(),
            None => continue,
        };
        if t == &x {
            continue;
        }
        out.insert((ba, r, c_name));
    }
    out
}

/// Collect `∃R.C` consumers `∃R.C ⊑ D`, i.e. the role-body clause
/// `R(x,y) ∧ C(y) → D(x)`.  Returns `(R, C) → [D, ...]`.
fn collect_exists_consumers(tbox: &[DLClause]) -> HashMap<(String, String), Vec<String>> {
    let x = var_x();
    let y = var_y();
    let mut out: HashMap<(String, String), Vec<String>> = HashMap::default();
    for c in tbox {
        if c.head.is_empty() {
            continue;
        }
        let roles: Vec<&Atom> = c.body.iter().filter(|a| is_role(a)).collect();
        if roles.len() != 1 {
            continue;
        }
        let (r, s, t) = role_parts(roles[0]);
        if *s != x || *t != y || *t == x {
            continue;
        }
        let mut fil: Option<String> = None;
        for a in &c.body {
            if let Atom::Concept(name, tt) = a {
                if *tt == y {
                    if fil.is_none() {
                        fil = Some(name.clone());
                    } else {
                        fil = None;
                        break;
                    }
                }
            }
        }
        let fil = match fil {
            Some(f) => f,
            None => continue,
        };
        if !c
            .head
            .iter()
            .all(|h| matches!(h, Atom::Concept(_, t) if *t == x))
        {
            continue;
        }
        for h in &c.head {
            if let Atom::Concept(name, _) = h {
                out.entry((r.to_string(), fil.clone()))
                    .or_default()
                    .push(name.clone());
            }
        }
    }
    out
}

/// Build the sub-role hierarchy `S ⊑ R` from single role-body→role-head clauses.
fn collect_sub_roles(tbox: &[DLClause]) -> HashMap<String, Vec<String>> {
    let mut sub_super: HashMap<String, Vec<String>> = HashMap::default();
    for c in tbox {
        if c.body.len() == 1 && c.head.len() == 1 {
            if let (Atom::Role(u, us, ut), Atom::Role(v, vs, vt)) = (&c.body[0], &c.head[0]) {
                if us == vs && ut == vt && us != ut && u != v {
                    sub_super.entry(u.clone()).or_default().push(v.clone());
                }
            }
        }
    }
    sub_super
}

/// Marker name matching `transitivity_clauses` for `(R, [C])`.
fn marker_name(r: &str, c: &str) -> String {
    format!("__trans__{}__{}", r, c)
}

/// KM_ROLE_AUTOMATON (gated, additive): derive the finite `∃R.C` reachability
/// closure over named classes via the role automaton (transitivity + chains +
/// sub-role hierarchy) and emit the derived `A ⊑ ∃R.C` as marker-seed +
/// consumer clauses.  Sound + finite (named-to-named closure only).
pub fn role_automaton_reachability_clauses(tbox: &[DLClause]) -> Vec<DLClause> {
    if std::env::var_os("KM_ROLE_AUTOMATON").is_none() {
        return Vec::new();
    }
    let info = detect_role_chains(tbox);
    if info.trans.is_empty() && info.chains.is_empty() {
        return Vec::new();
    }
    let trans: HashSet<String> = info.trans.iter().cloned().collect();
    let sub_super = collect_sub_roles(tbox);

    let super_close = |r: &str| -> HashSet<String> {
        let mut out = HashSet::default();
        out.insert(r.to_string());
        let mut stack = vec![r.to_string()];
        while let Some(u) = stack.pop() {
            for v in sub_super.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
                if out.insert(v.clone()) {
                    stack.push(v.clone());
                }
            }
        }
        out
    };

    let mut intros = collect_exists_introducers(tbox);
    let consumers = collect_exists_consumers(tbox);

    let mut two_step: HashMap<String, Vec<(String, String)>> = HashMap::default();
    for (r1, r2, u) in &info.chains {
        for sup in super_close(u) {
            two_step
                .entry(sup)
                .or_default()
                .push((r1.clone(), r2.clone()));
        }
    }
    for r in &trans {
        two_step
            .entry(r.clone())
            .or_default()
            .push((r.clone(), r.clone()));
    }

    let mut by_rf: HashMap<(String, String), HashSet<String>> = HashMap::default();
    for (a, r, c) in &intros {
        by_rf
            .entry((r.clone(), c.clone()))
            .or_default()
            .insert(a.clone());
    }
    let mut changed = true;
    let mut iters = 0u32;
    while changed {
        changed = false;
        iters += 1;
        if iters > 1000 {
            break;
        }
        let snapshot = by_rf.clone();
        for (r, routes) in &two_step {
            for (r1, r2) in routes {
                let r2_cs: Vec<(String, String)> = snapshot
                    .keys()
                    .filter(|(rr, _)| rr == r2)
                    .cloned()
                    .collect();
                for (_rr2, c) in r2_cs {
                    let bs = match snapshot.get(&(r2.clone(), c.clone())) {
                        Some(s) => s.iter().cloned().collect::<Vec<_>>(),
                        None => continue,
                    };
                    for b in bs {
                        if let Some(as_) = snapshot.get(&(r1.clone(), b.clone())) {
                            for a in as_ {
                                let key = (r.clone(), c.clone());
                                let set = by_rf.entry(key).or_default();
                                if set.insert(a.clone()) {
                                    intros.insert((a.clone(), r.clone(), c.clone()));
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        for (s, sups) in &sub_super {
            for r in sups {
                let s_cs: Vec<(String, String)> =
                    snapshot.keys().filter(|(rr, _)| rr == s).cloned().collect();
                for (_ss, c) in s_cs {
                    let as_ = match snapshot.get(&(s.clone(), c.clone())) {
                        Some(s2) => s2.iter().cloned().collect::<Vec<_>>(),
                        None => continue,
                    };
                    for a in as_ {
                        let key = (r.clone(), c.clone());
                        let set = by_rf.entry(key).or_default();
                        if set.insert(a.clone()) {
                            intros.insert((a.clone(), r.clone(), c.clone()));
                            changed = true;
                        }
                    }
                }
            }
        }
    }

    let x = var_x();
    let mut out = Vec::new();
    let mut emitted: HashSet<(String, String, String)> = HashSet::default();
    for (a, r, c) in &intros {
        if !emitted.insert((a.clone(), r.clone(), c.clone())) {
            continue;
        }
        let m = marker_name(r, c);
        out.push(clause(
            [Atom::Concept(a.clone(), x.clone())],
            [Atom::Concept(m.clone(), x.clone())],
        ));
        let mut ds: Vec<String> = Vec::new();
        if let Some(v) = consumers.get(&(r.clone(), c.clone())) {
            ds.extend(v.iter().cloned());
        }
        for (s, sups) in &sub_super {
            if sups.iter().any(|rr| rr == r) {
                if let Some(v) = consumers.get(&(s.clone(), c.clone())) {
                    ds.extend(v.iter().cloned());
                }
            }
        }
        ds.sort();
        ds.dedup();
        for d in ds {
            out.push(clause(
                [Atom::Concept(m.clone(), x.clone())],
                [Atom::Concept(d, x.clone())],
            ));
        }
    }
    out
}

/// Port of `_is_chain_axiom`.
fn is_chain_axiom(c: &DLClause) -> bool {
    if let Some((r0, r1, h)) = binary_role_composition(c) {
        let (_r0r, r0s, r0t) = role_parts(r0);
        let (_r1r, r1s, r1t) = role_parts(r1);
        let (_hr, hs, ht) = role_parts(h);
        let pair: Option<((&Term, &Term), (&Term, &Term))> = if r0t == r1s {
            Some(((r0s, r0t), (r1s, r1t)))
        } else if r1t == r0s {
            Some(((r1s, r1t), (r0s, r0t)))
        } else {
            None
        };
        if let Some(((fs, _ft), (_ss, st))) = pair {
            if hs == fs && ht == st && fs != st {
                return true;
            }
        }
    }
    false
}

fn is_canonical_long_chain_axiom(c: &DLClause) -> bool {
    c.body.iter().chain(&c.head).any(|atom| match atom {
        Atom::Role(role, _, _) => role.starts_with("__chain__"),
        _ => false,
    })
}

/// A transitive closure preserves the set of sources and targets of a role.
/// Thus pure domain/range consumers cannot distinguish that closure. Guarded
/// source-endpoint consumers of explicit transitive roles use the existing
/// recognition clauses. All other
/// body occurrences (including ground negatives, functionality, and mixed
/// chains) prevent this model-extension certificate. Direct/inverse inclusions
/// are preserved by closing a set of roles upward along those inclusions.
fn endpoint_only_transitive_roles(tbox: &[DLClause], abox: &[DLClause]) -> HashSet<String> {
    fn transitive_role(c: &DLClause) -> Option<&str> {
        let (first, second, head) = binary_role_composition(c)?;
        let (r, a, b) = role_parts(first);
        let (s, c, d) = role_parts(second);
        let (t, e, f) = role_parts(head);
        if r != s || r != t || ![a, b, c, d, e, f].iter().all(|term| matches!(term, Term::Var(_))) {
            return None;
        }
        ((b == c && a == e && d == f && a != b && b != d && a != d)
            || (d == a && c == e && b == f && c != d && d != b && c != b)).then_some(r)
    }
    let mut candidates: HashSet<String> = tbox.iter().chain(abox)
        .filter_map(transitive_role).map(str::to_owned).collect();
    let mut unsafe_roles = HashSet::default();
    let mut inclusion_predecessors: HashMap<String, Vec<String>> = HashMap::default();
    for c in tbox.iter().chain(abox) {
        if transitive_role(c).is_some() {
            continue;
        }
        // R o S <= S remains true if either relation is transitively closed.
        // Keep this chain itself, but it does not obstruct projecting a pure
        // transitivity axiom. The variable/path checks exclude repeated nodes
        // and ground constraints, which do not have this extension property.
        if binary_role_composition(c).is_some_and(|(first, second, head)| {
            let (r, a, b) = role_parts(first);
            let (s, c, d) = role_parts(second);
            let (t, e, f) = role_parts(head);
            [a,b,c,d,e,f].iter().all(|term| matches!(term, Term::Var(_)))
                && ((b == c && a == e && d == f && s == t && a != b && b != d && a != d)
                    || (d == a && c == e && b == f && r == t && c != d && d != b && c != b))
        }) { continue; }
        if let ([Atom::Role(left, a, b)], [Atom::Role(right, c, d)]) =
            (c.body.as_slice(), c.head.as_slice())
        {
            if matches!(a, Term::Var(_)) && matches!(b, Term::Var(_)) && a != b
                && ((a == c && b == d) || (a == d && b == c))
            {
                inclusion_predecessors.entry(right.clone()).or_default().push(left.clone());
                continue;
            }
        }
        let endpoint_consumer = match (c.body.as_slice(), c.head.as_slice()) {
            ([Atom::Role(_, source, target)], [Atom::Concept(_, term)]) =>
                matches!(source, Term::Var(_)) && matches!(target, Term::Var(_))
                && source != target && (term == source || term == target),
            _ => false,
        };
        // The three recognition clauses emitted below replace this exact
        // guarded consumer on an explicitly transitive role. Do not admit a
        // nontransitive super-role: closing it could change class entailments.
        let recognized_consumer = single_body_role(c).is_some_and(|atom| {
            let (role, source, target) = role_parts(atom);
            candidates.contains(role) && *source == var_x() && source != target
                && matches!(target, Term::Var(_))
                && c.body.iter().all(|a| a == atom || matches!(a,
                    Atom::Concept(_, term) if term == source || term == target))
                && c.body.iter().any(|a| matches!(a, Atom::Concept(_, term) if term == target))
                && !c.head.is_empty()
                && c.head.iter().all(|a| matches!(a, Atom::Concept(_, term) if term == source))
        });
        if !endpoint_consumer && !recognized_consumer {
            for atom in &c.body {
                if let Atom::Role(role, _, _) = atom { unsafe_roles.insert(role.clone()); }
            }
        }
    }
    // If extending S would violate a consumer, extending R cannot be certified
    // when R is included in S or its inverse. Propagate that restriction through
    // the complete dependency graph, including cycles and nontransitive roles.
    let mut pending: Vec<_> = unsafe_roles.iter().cloned().collect();
    while let Some(role) = pending.pop() {
        for predecessor in inclusion_predecessors.get(&role).into_iter().flatten() {
            if unsafe_roles.insert(predecessor.clone()) { pending.push(predecessor.clone()); }
        }
    }
    candidates.retain(|role| !unsafe_roles.contains(role));
    candidates
}

/// Port of `augment`: tbox minus raw chain axioms, plus nominal / transitivity /
/// chain encodings.
pub fn augment(tbox: Vec<DLClause>, abox: &[DLClause], hooks: &GroundHooks) -> Vec<DLClause> {
    augment_with_chains(tbox, abox, hooks).0
}

/// Like [`augment`] but also returns the detected [`ChainInfo`], so a later
/// pass (after `domain_range_clauses` are available) can build chain /
/// transitivity recognitions for pure-domain consumers of chain targets — the
/// consumers `T(x,y) → D(x)` that are not yet visible when `augment` runs.
/// See [`domain_consumer_chain_clauses`].
pub fn augment_with_chains(
    tbox: Vec<DLClause>,
    abox: &[DLClause],
    hooks: &GroundHooks,
) -> (Vec<DLClause>, ChainInfo) {
    augment_with_chains_retaining_role_axioms(tbox, abox, hooks, false)
}

pub(super) fn augment_with_chains_retaining_role_axioms(
    tbox: Vec<DLClause>,
    abox: &[DLClause],
    hooks: &GroundHooks,
    retain_role_axioms: bool,
) -> (Vec<DLClause>, ChainInfo) {
    // The raw `R1∘R2⊑R` (and `R∘R⊑R` transitive) role axioms are ALWAYS
    // filtered from the clause stream (default behaviour): keeping them
    // bloats cb_to_ht's cardinality/disjunction expansion (14817: +434 clauses
    // → QoSat cascade).  Chain/transitivity info reaches cb_to_ht via rbox
    // `trans`/`chain` records (rbox.rs), which the frontend emits for
    // KM_KEEP_CHAIN_AXIOMS.  KM_ROLE_AUTOMATON still keeps them (the expensive
    // preprocessing closure needs the raw axioms in the tbox it scans).
    // Recognition clauses preserve class consumers, but do not materialize
    // chain edges between named individuals. The nominal clause stream must
    // retain the original chain implications so ground negative assertions
    // and other ABox consumers see every entailed edge. These are original
    // normalized axioms, not a new inference rule or an approximation.
    let keep_chains = retain_role_axioms || std::env::var_os("KM_ROLE_AUTOMATON").is_some()
        || (std::env::var_os("KM_NOMINALS").is_some() && !abox.is_empty());
    let endpoint_only = if keep_chains && !retain_role_axioms {
        endpoint_only_transitive_roles(&tbox, abox)
    } else { HashSet::default() };
    // Build every addition while raw chain axioms remain borrowable, then move
    // the retained normalized clauses into `base`. Cloning the whole TBox here
    // served only to keep the original alive for these derived passes.
    // Consolidate additions immediately. Keeping four independently grown
    // vectors alive at once retains all four spare capacities and can exceed
    // the clone this path removes on transitivity-heavy ontologies.
    // One chain/transitivity detection pass serves both derived families and
    // the returned `ChainInfo`; each used to rescan the whole clause set.
    let nominal_mode = std::env::var_os("KM_NOMINALS").is_some();
    let mut chain_info = detect_role_chains(&tbox);
    chain_info.ground_edges = nominal_mode && !abox.is_empty();
    // ABox role facts count in every mode: outside nominal clausification
    // `nominal_clauses` turns them into existentials on the proxies.
    chain_info.generated_roles = Some(generated_roles(tbox.iter().chain(abox.iter())));
    let mut derived = transitivity_clauses_with(&tbox, &chain_info);
    derived.extend(forall_transitivity_clauses(&tbox, &chain_info));
    derived.extend(chain_clauses_with(&tbox, &chain_info));
    derived.extend(regular_role_automaton_clauses(&tbox, &chain_info));
    let (chain_consumers, unencoded) =
        chain_consumer_automaton_clauses(&tbox, &chain_info, ChainConsumerPass::Tbox);
    derived.extend(chain_consumers);
    chain_info.unencoded_chain_consumers = unencoded;
    // Ground negative role assertions in the nominal clause stream.
    let (abox_rest, negative_guards, negative_defining) = if nominal_mode {
        guarded_negative_role_assertions(abox, hooks)
    } else {
        (Vec::new(), Vec::new(), Vec::new())
    };
    if !negative_guards.is_empty() {
        let (guard_consumers, unencoded) =
            chain_consumer_automaton_clauses(&negative_guards, &chain_info, ChainConsumerPass::Abox);
        derived.extend(guard_consumers);
        chain_info.unencoded_chain_consumers += unencoded;
    }
    derived.extend(transitive_chain_compose_clauses(&tbox));
    derived.extend(role_automaton_reachability_clauses(&tbox));
    // Do not use `filter().collect()` here. `Vec`'s in-place collection may
    // retain the normaliser's substantially over-allocated source buffer even
    // after most of the parse-time working set is dead. Move the clauses into
    // a right-sized allocation instead: this copies only the small DLClause
    // headers while every atom/string allocation remains owned and is moved.
    let mut base = Vec::with_capacity(tbox.len());
    base.extend(
        tbox.into_iter()
            .filter(|c| {
                let endpoint_transitivity = binary_role_composition(c).is_some_and(|(a,b,h)| {
                    let (r,_,_) = role_parts(a);
                    r == role_parts(b).0 && r == role_parts(h).0 && endpoint_only.contains(r)
                        && is_chain_axiom(c)
                });
                !endpoint_transitivity && (keep_chains || !is_chain_axiom(c) || is_canonical_long_chain_axiom(c))
            }),
    );
    base.extend(nominal_clauses(abox, hooks));
    if nominal_mode {
        if negative_guards.is_empty() {
            base.extend(abox.iter().cloned());
        } else {
            base.extend(abox_rest);
        }
        base.extend(nominal_defining_clauses(hooks));
        base.extend(negative_defining);
        base.extend(negative_guards);
    }
    base.extend(derived);
    (base, chain_info)
}

/// Three-clause transitivity recognition for `R(x,y) ∧ ⋀filler(y) → ⋀head(x)`
/// with transitive `R` (mirrors [`transitivity_clauses`]'s body): the `P`
/// reachability concept, its up-propagation, and the consumer. `filler` may be
/// empty (a pure `∃R.⊤ ⊑ head` / domain consumer).
fn trans_recognition(r: &str, filler: &[String], head: &[Atom]) -> Vec<DLClause> {
    let x = var_x();
    let y = var_y();
    let p = format!("__trans__{}__{}", r, filler.join("_"));
    let mut out = Vec::new();
    // R(x,y) ∧ ⋀filler(y) → P(x)
    let mut body1 = vec![Atom::Role(r.to_string(), x.clone(), y.clone())];
    for f in filler {
        body1.push(Atom::Concept(f.clone(), y.clone()));
    }
    out.push(clause(body1, [Atom::Concept(p.clone(), x.clone())]));
    // R(x,y) ∧ P(y) → P(x)
    out.push(clause(
        [
            Atom::Role(r.to_string(), x.clone(), y.clone()),
            Atom::Concept(p.clone(), y.clone()),
        ],
        [Atom::Concept(p.clone(), x.clone())],
    ));
    // P(x) → ⋀head(x)
    out.push(clause([Atom::Concept(p, x.clone())], head.to_vec()));
    out
}

/// Chain / transitivity recognition for PURE-DOMAIN consumers of chain targets
/// and transitive roles: the `T(x,y) → D(x)` clauses produced by
/// `domain_range_clauses`, which `augment`'s pass-1 `chain_clauses` /
/// `transitivity_clauses` cannot see (domain/range records are parsed later).
/// Closes `R∘S⊑T, domain(T)=D ⊢ ∃R.∃S.⊤ ⊑ D` and its transitive-`R` variant
/// (e.g. ore_ont_11745's missed unsatisfiability). Additive and sound: emits
/// only fresh `__chain__` / `__trans__` recognition clauses. Gated by
/// `KM_CHAIN_DOMAIN` while it is validated corpus-wide.
pub fn domain_consumer_chain_clauses(info: &ChainInfo, domain_range: &[DLClause]) -> Vec<DLClause> {
    let x = var_x();
    let y = var_y();
    let trans: HashSet<&str> = info.trans.iter().map(|s| s.as_str()).collect();
    let mut by_t: HashMap<&str, Vec<(&str, &str)>> = HashMap::default();
    for (r, s, t) in &info.chains {
        by_t.entry(t.as_str())
            .or_default()
            .push((r.as_str(), s.as_str()));
    }
    let mut extra = Vec::new();
    let mut seen_s: HashSet<String> = HashSet::default();
    for c in domain_range {
        // domain shape: body = [Role(T, x, y)], head = concept(s) on x only.
        if c.body.len() != 1 || c.head.is_empty() {
            continue;
        }
        let (trole, tsource, ttarget) = match &c.body[0] {
            Atom::Role(r, s, t) => (r.as_str(), s, t),
            _ => continue,
        };
        if *tsource != x || *ttarget != y {
            continue; // range axioms (head on y) are not chain-target consumers
        }
        if !c
            .head
            .iter()
            .all(|h| matches!(h, Atom::Concept(_, t) if *t == x))
        {
            continue;
        }
        let head: Vec<Atom> = c.head.clone();
        // Chain: T = R∘S, consumer has empty filler on y.
        if let Some(pairs) = by_t.get(trole) {
            for (r, s) in pairs {
                let q = format!("__chain__{}__", s);
                if seen_s.insert(q.clone()) {
                    // S(x,y) → Q(x)
                    extra.push(clause(
                        [Atom::Role(s.to_string(), x.clone(), y.clone())],
                        [Atom::Concept(q.clone(), x.clone())],
                    ));
                }
                if trans.contains(r) {
                    // Transitive R: the recognition covers the 1-hop case too
                    // (R(x,y)∧Q(y)→P(x)→head), so emit only that.
                    extra.extend(trans_recognition(r, std::slice::from_ref(&q), &head));
                } else {
                    // R(x,y) ∧ Q(y) → head(x)
                    extra.push(clause(
                        [
                            Atom::Role(r.to_string(), x.clone(), y.clone()),
                            Atom::Concept(q.clone(), y.clone()),
                        ],
                        head.clone(),
                    ));
                }
            }
        }
        // Transitive T with a pure-domain consumer: ∃T.⊤ ⊑ D up T-chains.
        if trans.contains(trole) {
            extra.extend(trans_recognition(trole, &[], &head));
        }
    }
    extra
}

/// Roles that some derivation over `clauses` can create an edge for: the
/// least set closed under clauses whose head has a role atom and whose body
/// roles are all in the set (existentials and ground facts have none). The
/// raw chain compositions count too, which only enlarges the set.
fn generated_roles<'c>(clauses: impl Iterator<Item = &'c DLClause> + Clone) -> HashSet<String> {
    let mut generated: HashSet<String> = HashSet::default();
    loop {
        let before = generated.len();
        for c in clauses.clone() {
            let ready = c.body.iter().all(|atom| match atom {
                Atom::Role(role, _, _) => generated.contains(role),
                _ => true,
            });
            if !ready {
                continue;
            }
            for atom in &c.head {
                if let Atom::Role(role, _, _) = atom {
                    if !generated.contains(role) {
                        generated.insert(role.clone());
                    }
                }
            }
        }
        if generated.len() == before {
            return generated;
        }
    }
}

/// Rewrite each ground negative role assertion `R(a,b) → ⊥` of the nominal
/// clause stream into the guarded clash clause
/// `{a}(x) ∧ R(x,y) ∧ {b}(y) → ⊥` over the individuals' nominal proxies, the
/// form the native bridge already uses (`cb_to_ht::install_nominal_abox`).
///
/// The CB worker read the ground form as `R(x,b) → x ≉ a` and its Hyper rule
/// binds the non-central individual `b` like a variable, so `R(a,c)` together
/// with `¬R(a,b)` was refuted: `{r(a,b), ¬r(a,c)}` was reported inconsistent.
/// The guarded form has only variables in the body, applies to derived edges
/// (sub-roles, inverses, chains, transitivity) like every other consumer, and
/// is exact: each proxy is made the singleton by its defining clauses, which
/// are returned for proxies that ordinary nominal preprocessing does not
/// define. Returns the other ABox clauses, the guards, and those definitions.
fn guarded_negative_role_assertions(
    abox: &[DLClause],
    hooks: &GroundHooks,
) -> (Vec<DLClause>, Vec<DLClause>, Vec<DLClause>) {
    let x = var_x();
    let y = var_y();
    let mut rest = Vec::new();
    let mut guards = Vec::new();
    let mut proxies: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();
    for c in abox {
        if let ([Atom::Role(role, Term::Ind(a), Term::Ind(b))], []) = (c.body.as_slice(), c.head.as_slice()) {
            let pa = format!("__nom__{a}");
            let pb = format!("__nom__{b}");
            guards.push(clause(
                [
                    Atom::Concept(pa.clone(), x.clone()),
                    Atom::Role(role.clone(), x.clone(), y.clone()),
                    Atom::Concept(pb.clone(), y.clone()),
                ],
                [],
            ));
            for (proxy, individual) in [(pa, a), (pb, b)] {
                if !hooks.nominal_to_individual.contains_key(&proxy) {
                    proxies.insert(proxy, individual.clone());
                }
            }
        } else {
            rest.push(c.clone());
        }
    }
    let mut defining = Vec::new();
    for (proxy, individual) in proxies {
        defining.push(clause([], [Atom::Concept(proxy.clone(), Term::Ind(individual.clone()))]));
        defining.push(clause([Atom::Concept(proxy, x.clone())], [Atom::Eq(x.clone(), Term::Ind(individual))]));
    }
    (rest, guards, defining)
}

/// DL7/DL8 defining clauses that make each nominal proxy concept exact
/// instead of an over-approximation: `⊤ → __nom__o(o)` ({o} ⊑ __nom__o) and
/// `__nom__o(x) → x ≈ o` (__nom__o ⊑ {o}). Together with the ground ABox
/// clauses these give the engine the full nominal semantics (Phase 0 of
/// docs/NOMINALS-CB.md); only emitted under KM_NOMINALS. Sorted by proxy
/// name so the output is deterministic.
pub fn nominal_defining_clauses(hooks: &GroundHooks) -> Vec<DLClause> {
    let mut pairs: Vec<(&String, &String)> = hooks.nominal_to_individual.iter().collect();
    pairs.sort();
    let x = var_x();
    let mut out = Vec::new();
    for (nom, ind) in pairs {
        out.push(clause(
            [],
            [Atom::Concept(nom.clone(), Term::Ind(ind.clone()))],
        ));
        out.push(clause(
            [Atom::Concept(nom.clone(), x.clone())],
            [Atom::Eq(x.clone(), Term::Ind(ind.clone()))],
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::super::clauses::constraint;
    use super::*;

    fn role(r: &str, s: Term, t: Term) -> Atom {
        Atom::Role(r.to_string(), s, t)
    }

    fn bridge(r: &str, s: &str) -> DLClause {
        clause([role(r, var_x(), var_y())], [role(s, var_y(), var_x())])
    }

    fn pair(r: &str, s: &str) -> (String, String) {
        (r.to_string(), s.to_string())
    }

    #[test]
    fn trans_chain_compose_feeds_reachability() {
        let _test_env = crate::test_env::read();
        // T transitive, R∘S⊑U, U⊑T, consumer T(x,y)∧H(y)→D(x) (so D ⊒ ∃T.H,
        // reachability P=__trans__T__H). The composition must let a node reach H
        // via the chain R∘S: emit R(x,y)∧__cmpp__S__P(y)→P(x) and the __cmpp def
        // S(y,z)∧P(z)→__cmpp__S__P(y), plus the __cmpc seeding S(y,z)∧H(z)→…→P.
        let x = var_x();
        let y = var_y();
        let z = Term::Var("z".to_string());
        let con = |n: &str, t: &Term| Atom::Concept(n.to_string(), t.clone());
        let tbox = vec![
            clause(
                [
                    role("T", x.clone(), y.clone()),
                    role("T", y.clone(), z.clone()),
                ],
                [role("T", x.clone(), z.clone())],
            ),
            clause(
                [
                    role("R", x.clone(), y.clone()),
                    role("S", y.clone(), z.clone()),
                ],
                [role("U", x.clone(), z.clone())],
            ),
            clause(
                [role("U", x.clone(), y.clone())],
                [role("T", x.clone(), y.clone())],
            ),
            clause(
                [role("T", x.clone(), y.clone()), con("H", &y)],
                [con("D", &x)],
            ),
        ];
        let out = transitive_chain_compose_impl(&tbox);
        let p = "__trans__T__H";
        let midp = "__cmpp__S____trans__T__H";
        // P rides the chain: R(x,y) ∧ __cmpp__S__P(y) → P(x)
        let has_ride = out.iter().any(|c| {
            c.head == vec![con(p, &x)]
                && c.body.contains(&role("R", x.clone(), y.clone()))
                && c.body.contains(&con(midp, &y))
        });
        assert!(has_ride, "missing chain-ride clause into {p}; got {out:?}");
        // __cmpp def: S(y,z) ∧ P(z) → __cmpp__S__P(y)
        let has_def = out.iter().any(|c| {
            c.head == vec![con(midp, &y)]
                && c.body.contains(&role("S", y.clone(), z.clone()))
                && c.body.contains(&con(p, &z))
        });
        assert!(has_def, "missing __cmpp definition; got {out:?}");
        // a non-transitive / no-chain tbox yields nothing.
        assert!(transitive_chain_compose_impl(&tbox[1..2]).is_empty());
    }

    #[test]
    fn domain_consumer_chain_recognition() {
        let _test_env = crate::test_env::read();
        // chain r∘s⊑t with a pure-domain consumer t(x,y)→D(x): expect a
        // recognition __chain__s__ (any s-edge) and a consumer
        // r(x,y) ∧ __chain__s__(y) → D(x).
        let info = ChainInfo {
            trans: vec![],
            chains: vec![("r".into(), "s".into(), "t".into())],
            sub_same: vec![],
            sub_inv: vec![],
            unencoded_chain_consumers: 0,
            ground_edges: false,
            generated_roles: None,
        };
        let dr = vec![clause(
            [Atom::Role("t".into(), var_x(), var_y())],
            [Atom::Concept("D".into(), var_x())],
        )];
        let out = domain_consumer_chain_clauses(&info, &dr);
        let has_recog = out.iter().any(|c| {
            c.body == vec![Atom::Role("s".into(), var_x(), var_y())]
                && c.head == vec![Atom::Concept("__chain__s__".into(), var_x())]
        });
        let has_consumer = out.iter().any(|c| {
            c.head == vec![Atom::Concept("D".into(), var_x())]
                && c.body
                    .iter()
                    .any(|a| matches!(a, Atom::Role(r, ..) if r == "r"))
                && c.body
                    .iter()
                    .any(|a| matches!(a, Atom::Concept(q, _) if q == "__chain__s__"))
        });
        assert!(has_recog, "missing __chain__s__ recognition: {out:?}");
        assert!(has_consumer, "missing r∧__chain__s__→D consumer: {out:?}");
    }

    #[test]
    fn domain_consumer_transitive_chain_recognition() {
        let _test_env = crate::test_env::read();
        // transitive r, chain r∘s⊑t, domain(t)=D: the consumer must be the
        // transitive recognition (P-concept up-propagation), not a plain edge.
        let info = ChainInfo {
            trans: vec!["r".into()],
            chains: vec![("r".into(), "s".into(), "t".into())],
            sub_same: vec![],
            sub_inv: vec![],
            unencoded_chain_consumers: 0,
            ground_edges: false,
            generated_roles: None,
        };
        let dr = vec![clause(
            [Atom::Role("t".into(), var_x(), var_y())],
            [Atom::Concept("D".into(), var_x())],
        )];
        let out = domain_consumer_chain_clauses(&info, &dr);
        // up-propagation clause r(x,y) ∧ P(y) → P(x) for P = __trans__r____chain__s__
        let p = "__trans__r____chain__s__";
        let has_prop = out.iter().any(|c| {
            c.body
                .iter()
                .any(|a| matches!(a, Atom::Concept(q, t) if q == p && *t == var_y()))
                && c.head == vec![Atom::Concept(p.into(), var_x())]
        });
        assert!(has_prop, "missing transitive up-propagation: {out:?}");
    }

    #[test]
    fn nominal_defining_clauses_dl7_dl8() {
        let _test_env = crate::test_env::read();
        let mut hooks = GroundHooks::default();
        hooks
            .nominal_to_individual
            .insert("__nom__o".to_string(), "o".to_string());
        let out = nominal_defining_clauses(&hooks);
        assert_eq!(out.len(), 2);
        // DL7: ⊤ → __nom__o(o)
        assert_eq!(
            out[0],
            clause(
                [],
                [Atom::Concept(
                    "__nom__o".to_string(),
                    Term::Ind("o".to_string())
                )]
            )
        );
        // DL8: __nom__o(x) → x ≈ o
        assert_eq!(
            out[1],
            clause(
                [Atom::Concept("__nom__o".to_string(), var_x())],
                [Atom::Eq(var_x(), Term::Ind("o".to_string()))]
            )
        );
    }

    #[test]
    fn prunes_both_directions_when_pair_unconsumed() {
        let _test_env = crate::test_env::read();
        // A ⊑ ∃R.B yields only a head occurrence of R; nothing consumes R or S.
        let producer = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [role(
                "R",
                var_x(),
                Term::Fun("f".to_string(), Box::new(var_x())),
            )],
        );
        let mut tbox = vec![producer.clone(), bridge("R", "S"), bridge("S", "R")];
        prune_dead_inverse_bridges(&mut tbox, &[pair("R", "S")]);
        assert_eq!(tbox, vec![producer]);
    }

    #[test]
    fn keeps_only_consumed_direction() {
        let _test_env = crate::test_env::read();
        // S(x,y) ∧ B(y) → Q(x): S is consumed, R is not.
        let consumer = clause(
            [
                role("S", var_x(), var_y()),
                Atom::Concept("B".to_string(), var_y()),
            ],
            [Atom::Concept("Q".to_string(), var_x())],
        );
        let r_to_s = bridge("R", "S");
        let mut tbox = vec![consumer.clone(), r_to_s.clone(), bridge("S", "R")];
        prune_dead_inverse_bridges(&mut tbox, &[pair("R", "S")]);
        assert_eq!(tbox, vec![consumer, r_to_s]);
    }

    #[test]
    fn keeps_bridge_with_onward_partner() {
        let _test_env = crate::test_env::read();
        // Pairs (R,S) and (S,T); only T is consumed. R→S must survive because
        // S bridges onward to T; S→R is the pure round trip and goes away.
        let consumer = clause(
            [role("T", var_x(), var_y())],
            [Atom::Concept("C".to_string(), var_x())],
        );
        let mut tbox = vec![
            consumer.clone(),
            bridge("R", "S"),
            bridge("S", "R"),
            bridge("S", "T"),
            bridge("T", "S"),
        ];
        prune_dead_inverse_bridges(&mut tbox, &[pair("R", "S"), pair("S", "T")]);
        assert_eq!(
            tbox,
            vec![
                consumer,
                bridge("R", "S"),
                bridge("S", "T"),
                bridge("T", "S")
            ]
        );
    }

    #[test]
    fn same_orientation_subrole_clause_is_not_a_bridge() {
        let _test_env = crate::test_env::read();
        // R(x,y) → S(x,y) is a role-hierarchy clause: never pruned, and its
        // body occurrence of R keeps nothing alive for the R→S bridge (S is
        // still unconsumed).
        let sub = clause([role("R", var_x(), var_y())], [role("S", var_x(), var_y())]);
        let mut tbox = vec![sub.clone(), bridge("R", "S"), bridge("S", "R")];
        prune_dead_inverse_bridges(&mut tbox, &[pair("R", "S")]);
        // S→R survives: the hierarchy clause consumes R. R→S dies.
        assert_eq!(tbox, vec![sub, bridge("S", "R")]);
    }

    #[test]
    fn noop_without_pairs() {
        let _test_env = crate::test_env::read();
        let sub = clause([role("R", var_x(), var_y())], [role("S", var_y(), var_x())]);
        let mut tbox = vec![sub.clone()];
        prune_dead_inverse_bridges(&mut tbox, &[]);
        assert_eq!(tbox, vec![sub]);
    }

    fn relevant_set(items: &[&str]) -> HashSet<String> {
        items.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn relevance_skips_existential_only_role() {
        let _test_env = crate::test_env::read();
        // A ⊑ ∃R.B (head occurrence of R + concept B on the successor) and the
        // transitivity/self-bridge of R. R never sits in a body that yields a
        // concept, so it is inert.
        let producer = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [role(
                "R",
                var_x(),
                Term::Fun("f".to_string(), Box::new(var_x())),
            )],
        );
        let succ = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [Atom::Concept(
                "B".to_string(),
                Term::Fun("f".to_string(), Box::new(var_x())),
            )],
        );
        let trans = clause(
            [
                role("R", var_x(), var_y()),
                role("R", var_y(), Term::Var("z".to_string())),
            ],
            [role("R", var_x(), Term::Var("z".to_string()))],
        );
        let tbox = vec![producer, succ, trans, bridge("R", "R")];
        assert!(concept_relevant_roles(&tbox).is_empty());
    }

    #[test]
    fn relevance_excludes_role_feeding_only_a_synthetic_definer() {
        let _test_env = crate::test_env::read();
        // The ORE-giant pattern: `A ⊑ ∃R.C` names the existential as a synthetic
        // definer Q_0, emitting the recognizer `R(x,y) ∧ C(y) → Q_0(x)` and
        // `A(x) → Q_0(x)`. Q_0 is never consumed to derive a NAMED concept, so R
        // is inert — a forward "feeds any concept head" test would wrongly flag R.
        let recognizer = clause(
            [
                role("R", var_x(), var_y()),
                Atom::Concept("C".to_string(), var_y()),
            ],
            [Atom::Concept("Q_0".to_string(), var_x())],
        );
        let sub = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [Atom::Concept("Q_0".to_string(), var_x())],
        );
        assert!(concept_relevant_roles(&[recognizer, sub]).is_empty());
    }

    #[test]
    fn relevance_includes_role_when_definer_reaches_a_named_concept() {
        let _test_env = crate::test_env::read();
        // Same recognizer, but now Q_0 ⊑ D (named): Q_0 becomes a goal, the
        // recognizer activates, and R is needed.
        let recognizer = clause(
            [
                role("R", var_x(), var_y()),
                Atom::Concept("C".to_string(), var_y()),
            ],
            [Atom::Concept("Q_0".to_string(), var_x())],
        );
        let q_named = clause(
            [Atom::Concept("Q_0".to_string(), var_x())],
            [Atom::Concept("D".to_string(), var_x())],
        );
        assert!(concept_relevant_roles(&[recognizer, q_named]).contains("R"));
    }

    #[test]
    fn indexed_relevance_matches_the_large_clause_shape() {
        let _test_env = crate::test_env::read();
        let recognizer = clause(
            [
                role("R", var_x(), var_y()),
                Atom::Concept("C".to_string(), var_y()),
            ],
            [Atom::Concept("Q_0".to_string(), var_x())],
        );
        let q_named = clause(
            [Atom::Concept("Q_0".to_string(), var_x())],
            [Atom::Concept("D".to_string(), var_x())],
        );
        let inert = clause(
            [Atom::Concept("I".to_string(), var_x())],
            [Atom::Concept("Q_inert".to_string(), var_x())],
        );
        let mut tbox = vec![inert; 10_000];
        tbox.extend([recognizer, q_named]);
        assert_eq!(concept_relevant_roles(&tbox), relevant_set(&["R"]));
    }

    #[test]
    fn relevance_marks_role_feeding_a_constraint() {
        let _test_env = crate::test_env::read();
        // P(x,y) → ⊥ (empty head, e.g. the 7901 empty-data-range constraint) is a
        // goal: P is needed (it matters for unsatisfiability).
        let constraint_cl = constraint([role("P", var_x(), var_y())]);
        assert!(concept_relevant_roles(&[constraint_cl]).contains("P"));
    }

    #[test]
    fn relevance_marks_domain_and_propagates_through_subrole() {
        let _test_env = crate::test_env::read();
        // S(x,y) → D(x) is a domain clause: S is relevant. R ⊑ S makes R relevant.
        let domain = clause(
            [role("S", var_x(), var_y())],
            [Atom::Concept("D".to_string(), var_x())],
        );
        let subrole = clause([role("R", var_x(), var_y())], [role("S", var_x(), var_y())]);
        let rel = concept_relevant_roles(&[domain, subrole]);
        assert_eq!(rel, relevant_set(&["S", "R"]));
    }

    #[test]
    fn relevance_propagates_back_through_inverse_bridge() {
        let _test_env = crate::test_env::read();
        // Range on S (S(x,y) → D(y)) makes S relevant; the inverse bridge
        // R(x,y) → S(y,x) then makes R relevant — the SWEET inverse-feeds-range
        // case that must stay on the CB engine.
        let range = clause(
            [role("S", var_x(), var_y())],
            [Atom::Concept("D".to_string(), var_y())],
        );
        let rel = concept_relevant_roles(&[range, bridge("R", "S"), bridge("S", "R")]);
        assert!(rel.contains("R") && rel.contains("S"));
    }

    #[test]
    fn prunes_inert_symmetric_self_bridge() {
        let _test_env = crate::test_env::read();
        let producer = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [role(
                "R",
                var_x(),
                Term::Fun("f".to_string(), Box::new(var_x())),
            )],
        );
        let mut tbox = vec![producer.clone(), bridge("R", "R")];
        let relevant = HashSet::default();
        prune_inert_role_bridges(&mut tbox, &["R".to_string()], &[], &relevant);
        assert_eq!(tbox, vec![producer]);
    }

    #[test]
    fn keeps_relevant_symmetric_self_bridge() {
        let _test_env = crate::test_env::read();
        let consumer = clause(
            [role("R", var_x(), var_y())],
            [Atom::Concept("D".to_string(), var_x())],
        );
        let sym = bridge("R", "R");
        let mut tbox = vec![consumer.clone(), sym.clone()];
        let relevant = relevant_set(&["R"]);
        prune_inert_role_bridges(&mut tbox, &["R".to_string()], &[], &relevant);
        assert_eq!(tbox, vec![consumer, sym]);
    }

    #[test]
    fn prunes_inert_inverse_pair_both_directions() {
        let _test_env = crate::test_env::read();
        let producer = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [role(
                "R",
                var_x(),
                Term::Fun("f".to_string(), Box::new(var_x())),
            )],
        );
        let mut tbox = vec![producer.clone(), bridge("R", "S"), bridge("S", "R")];
        let relevant = HashSet::default();
        prune_inert_role_bridges(&mut tbox, &[], &[pair("R", "S")], &relevant);
        assert_eq!(tbox, vec![producer]);
    }
}

#[cfg(test)]
mod chain_detection_tests {
    use super::super::clauses::{constraint, fact};
    use super::*;

    /// The pre-optimisation detector: per-clause atom vectors, rescanned by
    /// every derived family. Kept as the oracle for the shared detection.
    fn detect_role_chains_reference(tbox: &[DLClause]) -> ChainInfo {
        let mut trans: Vec<String> = Vec::new();
        let mut chains: Vec<(String, String, String)> = Vec::new();
        for c in tbox {
            let roles: Vec<&Atom> = c.body.iter().filter(|a| is_role(a)).collect();
            let heads: Vec<&Atom> = c.head.iter().collect();
            if roles.len() == 2 && c.body.len() == 2 && heads.len() == 1 && is_role(heads[0]) {
                let (r0, r1, h) = (roles[0], roles[1], heads[0]);
                let (r0r, r0s, r0t) = role_parts(r0);
                let (r1r, r1s, r1t) = role_parts(r1);
                let (hr, hs, ht) = role_parts(h);
                let pair: Option<((&str, &Term, &Term), (&str, &Term, &Term))> = if r0t == r1s {
                    Some(((r0r, r0s, r0t), (r1r, r1s, r1t)))
                } else if r1t == r0s {
                    Some(((r1r, r1s, r1t), (r0r, r0s, r0t)))
                } else {
                    None
                };
                if let Some(((fr, fs, _ft), (sr, _ss, st))) = pair {
                    if hs == fs && ht == st && fs != st {
                        if fr == sr && sr == hr {
                            if !trans.iter().any(|t| t == hr) {
                                trans.push(hr.to_string());
                            }
                        } else {
                            chains.push((fr.to_string(), sr.to_string(), hr.to_string()));
                        }
                    }
                }
            }
        }
        ChainInfo { trans, chains, sub_same: vec![], sub_inv: vec![], unencoded_chain_consumers: 0, ground_edges: false, generated_roles: None }
    }

    fn is_chain_axiom_reference(c: &DLClause) -> bool {
        let roles: Vec<&Atom> = c.body.iter().filter(|a| is_role(a)).collect();
        let heads: Vec<&Atom> = c.head.iter().collect();
        if roles.len() == 2 && c.body.len() == 2 && heads.len() == 1 && is_role(heads[0]) {
            let (_r0r, r0s, r0t) = role_parts(roles[0]);
            let (_r1r, r1s, r1t) = role_parts(roles[1]);
            let (_hr, hs, ht) = role_parts(heads[0]);
            let pair: Option<((&Term, &Term), (&Term, &Term))> = if r0t == r1s {
                Some(((r0s, r0t), (r1s, r1t)))
            } else if r1t == r0s {
                Some(((r1s, r1t), (r0s, r0t)))
            } else {
                None
            };
            if let Some(((fs, _ft), (_ss, st))) = pair {
                if hs == fs && ht == st && fs != st {
                    return true;
                }
            }
        }
        false
    }

    fn v(n: &str) -> Term {
        Term::Var(n.to_string())
    }
    fn r(name: &str, s: Term, t: Term) -> Atom {
        Atom::Role(name.to_string(), s, t)
    }
    fn c(name: &str, t: Term) -> Atom {
        Atom::Concept(name.to_string(), t)
    }

    /// Every body/head shape the detector distinguishes, in both orientations.
    fn shapes() -> Vec<DLClause> {
        vec![
            // transitivity R(x,y) ∧ R(y,z) → R(x,z), both atom orders
            clause(
                [r("R", v("x"), v("y")), r("R", v("y"), v("z"))],
                [r("R", v("x"), v("z"))],
            ),
            clause(
                [r("R", v("y"), v("z")), r("R", v("x"), v("y"))],
                [r("R", v("x"), v("z"))],
            ),
            // chains R∘S ⊑ T, S∘R ⊑ T, and a repeated transitivity
            clause(
                [r("R", v("x"), v("y")), r("S", v("y"), v("z"))],
                [r("T", v("x"), v("z"))],
            ),
            clause(
                [r("S", v("x"), v("y")), r("R", v("y"), v("z"))],
                [r("T", v("x"), v("z"))],
            ),
            clause(
                [r("R", v("x"), v("y")), r("R", v("y"), v("z"))],
                [r("R", v("x"), v("z"))],
            ),
            // wrong wiring: head on the middle variable, or reflexive endpoints
            clause(
                [r("R", v("x"), v("y")), r("S", v("y"), v("z"))],
                [r("T", v("x"), v("y"))],
            ),
            clause(
                [r("R", v("x"), v("x")), r("S", v("x"), v("z"))],
                [r("T", v("x"), v("z"))],
            ),
            clause(
                [r("R", v("x"), v("y")), r("S", v("y"), v("x"))],
                [r("T", v("x"), v("x"))],
            ),
            // not a composition: a concept in the body, a concept head, a
            // disjunctive head, three body atoms, one body atom
            clause(
                [r("R", v("x"), v("y")), c("A", v("y"))],
                [r("T", v("x"), v("y"))],
            ),
            clause(
                [r("R", v("x"), v("y")), r("S", v("y"), v("z"))],
                [c("A", v("x"))],
            ),
            clause(
                [r("R", v("x"), v("y")), r("S", v("y"), v("z"))],
                [r("T", v("x"), v("z")), r("U", v("x"), v("z"))],
            ),
            clause(
                [
                    r("R", v("x"), v("y")),
                    r("S", v("y"), v("z")),
                    r("U", v("z"), v("w")),
                ],
                [r("T", v("x"), v("w"))],
            ),
            clause([r("R", v("x"), v("y"))], [r("T", v("x"), v("y"))]),
            clause([c("A", v("x"))], [c("B", v("x"))]),
            constraint([r("R", v("x"), v("y")), r("S", v("y"), v("z"))]),
            fact([r("R", v("x"), v("y"))]),
            // an equality atom in the head is not a role head
            clause(
                [r("R", v("x"), v("y")), r("R", v("x"), v("z"))],
                [Atom::Eq(v("y"), v("z"))],
            ),
        ]
    }

    #[test]
    fn allocation_free_detection_matches_the_reference() {
        let _test_env = crate::test_env::read();
        let tbox = shapes();
        let detected = detect_role_chains(&tbox);
        let reference = detect_role_chains_reference(&tbox);
        assert_eq!(detected.trans, reference.trans);
        assert_eq!(detected.chains, reference.chains);
        assert_eq!(detected.trans, vec!["R".to_string()]);
        // Both orientations of `R∘S ⊑ T`, plus the reflexive-first-edge
        // composition, which the wiring check admits (it only requires the
        // head to span from the first source to the second target).
        let chain = |a: &str, b: &str, c: &str| (a.to_string(), b.to_string(), c.to_string());
        assert_eq!(
            detected.chains,
            vec![
                chain("R", "S", "T"),
                chain("S", "R", "T"),
                chain("R", "S", "T")
            ]
        );
        for clause in &tbox {
            assert_eq!(
                is_chain_axiom(clause),
                is_chain_axiom_reference(clause),
                "{clause:?}"
            );
        }
        assert_eq!(tbox.iter().filter(|c| is_chain_axiom(c)).count(), 6);
        // Every shape appears once in each orientation of the body.
        let mut flipped: Vec<DLClause> = tbox
            .iter()
            .map(|c| {
                let mut body = c.body.clone();
                body.reverse();
                DLClause {
                    body,
                    head: c.head.clone(),
                }
            })
            .collect();
        flipped.extend(tbox.iter().cloned());
        let detected = detect_role_chains(&flipped);
        let reference = detect_role_chains_reference(&flipped);
        assert_eq!(detected.trans, reference.trans);
        assert_eq!(detected.chains, reference.chains);
    }

    #[test]
    fn shared_detection_reproduces_the_independent_derivations() {
        let _test_env = crate::test_env::read();
        let mut tbox = shapes();
        // Consumers that the transitivity/chain recognitions rewrite.
        tbox.push(clause(
            [r("R", v("x"), v("y")), c("A", v("y"))],
            [c("B", v("x"))],
        ));
        tbox.push(clause(
            [r("T", v("x"), v("y")), c("A", v("y"))],
            [c("C", v("x"))],
        ));
        tbox.push(clause([r("T", v("x"), v("y"))], [c("D", v("x"))]));
        let info = detect_role_chains(&tbox);
        assert_eq!(
            transitivity_clauses_with(&tbox, &info),
            transitivity_clauses(&tbox)
        );
        assert_eq!(chain_clauses_with(&tbox, &info), chain_clauses(&tbox));
        assert!(!transitivity_clauses(&tbox).is_empty());
        assert!(!chain_clauses(&tbox).is_empty());
    }
}

#[cfg(test)]
mod endpoint_transitivity_tests {
    use super::*;
    fn fixture() -> Vec<DLClause> {
        vec![
            clause([Atom::Role("r".into(), Term::Var("x".into()), Term::Var("y".into())),
                    Atom::Role("r".into(), Term::Var("y".into()), Term::Var("z".into()))],
                   [Atom::Role("r".into(), Term::Var("x".into()), Term::Var("z".into()))]),
            clause([Atom::Role("r".into(), var_x(), var_y())], [Atom::Concept("Domain".into(), var_x())]),
            clause([Atom::Role("r".into(), var_x(), var_y())], [Atom::Concept("Range".into(), var_y())]),
            clause([Atom::Role("s".into(), var_x(), var_y())], [Atom::Role("r".into(), var_x(), var_y())]),
        ]
    }
    #[test]
    fn endpoint_transitivity_accepts_only_model_extendible_consumers() {
        let _test_env = crate::test_env::read();
        let source = fixture();
        assert!(endpoint_only_transitive_roles(&source, &[]).contains("r"));
        let edge = Atom::Role("r".into(), var_x(), var_y());
        for obstruction in [
            clause([edge.clone()], []),
            clause([edge.clone()], [Atom::Concept("A".into(), var_x()), Atom::Concept("B".into(), var_y())]),
            clause([edge.clone(), Atom::Concept("A".into(), var_y())], []),
            clause([Atom::Role("r".into(), Term::Ind("a".into()), Term::Ind("b".into()))], []),
            clause([edge, Atom::Role("r".into(), var_x(), Term::Var("z".into()))],
                   [Atom::Eq(var_y(), Term::Var("z".into()))]),
        ] {
            assert!(!endpoint_only_transitive_roles(&source, &[obstruction]).contains("r"));
        }
        let recognized = clause([Atom::Role("r".into(), var_x(), var_y()),
            Atom::Concept("A".into(), var_y())], [Atom::Concept("B".into(), var_x())]);
        let mut augmented = source;
        augmented.push(recognized);
        assert!(endpoint_only_transitive_roles(&augmented, &[]).contains("r"));
    }

    #[test]
    fn endpoint_transitivity_closes_inclusion_cycles_and_propagates_obstructions() {
        let _test_env = crate::test_env::read();
        let mut source = fixture();
        source.push(clause([Atom::Role("r".into(), var_x(), var_y())],
            [Atom::Role("s".into(), var_y(), var_x())]));
        source.push(clause([Atom::Role("s".into(), var_x(), var_y())],
            [Atom::Role("t".into(), var_x(), var_y())]));
        assert!(endpoint_only_transitive_roles(&source, &[]).contains("r"));
        let negative = clause([Atom::Role("t".into(), Term::Ind("a".into()), Term::Ind("b".into()))], []);
        assert!(!endpoint_only_transitive_roles(&source, &[negative]).contains("r"));
        let guarded = clause([Atom::Role("t".into(), var_x(), var_y()),
            Atom::Concept("A".into(), var_y())], [Atom::Concept("B".into(), var_x())]);
        assert!(!endpoint_only_transitive_roles(&source, &[guarded]).contains("r"));
    }
}

#[cfg(test)]
mod inverse_transitivity_probe_tests {
    use super::*;
    fn role(r: &str, a: &str, b: &str) -> Atom {
        Atom::Role(r.into(), Term::Var(a.into()), Term::Var(b.into()))
    }
    fn transitive() -> DLClause {
        clause([role("R","x","y"),role("R","y","z")], [role("R","x","z")])
    }
    fn bridge(r: &str, s: &str) -> DLClause {
        clause([role(r,"x","y")], [role(s,"y","x")])
    }
    #[test]
    fn converse_transitivity_requires_equivalence_and_closes_aliases() {
        let _test_env = crate::test_env::read();
        let mut axioms=vec![transitive(),bridge("R","S")];
        assert_eq!(detect_role_chains(&axioms).trans,vec!["R"]);
        axioms.extend([bridge("S","R"),bridge("S","T"),bridge("T","S")]);
        assert_eq!(detect_role_chains(&axioms).trans,vec!["R","S","T"]);
    }
    #[test]
    fn guarded_and_ground_bridges_do_not_establish_converse_equivalence() {
        let _test_env = crate::test_env::read();
        let mut guarded=bridge("S","R");
        guarded.body.push(Atom::Concept("Guard".into(),var_x()));
        let axioms=vec![transitive(),bridge("R","S"),guarded];
        assert_eq!(detect_role_chains(&axioms).trans,vec!["R"]);
        let ground=|r: &str,s: &str| clause(
            [Atom::Role(r.into(),Term::Ind("a".into()),Term::Ind("b".into()))],
            [Atom::Role(s.into(),Term::Ind("b".into()),Term::Ind("a".into()))]);
        assert_eq!(detect_role_chains(&[transitive(),ground("R","S"),ground("S","R")]).trans,vec!["R"]);
    }
}

#[cfg(test)]
mod chain_consumer_automaton_tests {
    use super::*;

    fn v(name: &str) -> Term {
        Term::Var(name.to_string())
    }

    fn concept(name: &str, term: Term) -> Atom {
        Atom::Concept(name.to_string(), term)
    }

    fn role(name: &str, s: Term, t: Term) -> Atom {
        Atom::Role(name.to_string(), s, t)
    }

    /// `s ∘ t ⊑ r` (normalized composition) and `Q ⊑ ∀r.C`.
    fn forall_over_chain() -> Vec<DLClause> {
        vec![
            clause(
                [role("s", v("x"), v("y")), role("t", v("y"), v("z"))],
                [role("r", v("x"), v("z"))],
            ),
            clause([concept("Q", v("x")), role("r", v("x"), v("y"))], [concept("C", v("y"))]),
        ]
    }

    #[test]
    fn forall_consumer_of_a_chain_target_gets_forward_markers() {
        let _test_env = crate::test_env::read();
        let tbox = forall_over_chain();
        let info = detect_role_chains(&tbox);
        let (out, unencoded) =
            chain_consumer_automaton_clauses(&tbox, &info, ChainConsumerPass::Tbox);
        assert_eq!(unencoded, 0);
        let marker = |q: usize| format!("__riaf__r__c0__q{q}");
        assert!(out.contains(&clause([concept("Q", var_x())], [concept(&marker(0), var_x())])));
        assert!(out.iter().any(|c| matches!(c.body.as_slice(),
            [Atom::Concept(m, t)] if m.starts_with("__riaf__r__c0__q") && *t == var_x())
            && c.head == vec![concept("C", var_x())]));
        for letter in ["r", "s", "t"] {
            assert!(
                out.iter().any(|c| c.body.iter().any(
                    |a| matches!(a, Atom::Role(name, s, _) if name == letter && *s == var_x())
                ) && c.head.iter().all(|a| matches!(a, Atom::Concept(m, t)
                    if m.starts_with("__riaf__r__c0__") && *t == var_y()))),
                "no forward transition on {letter}: {out:?}"
            );
        }
    }

    #[test]
    fn no_chain_means_no_clauses() {
        let _test_env = crate::test_env::read();
        let tbox = vec![clause(
            [concept("Q", v("x")), role("r", v("x"), v("y"))],
            [concept("C", v("y"))],
        )];
        let info = detect_role_chains(&tbox);
        assert_eq!(
            chain_consumer_automaton_clauses(&tbox, &info, ChainConsumerPass::Tbox),
            (Vec::new(), 0)
        );
    }

    #[test]
    fn covered_existential_consumer_keeps_the_existing_encoding() {
        let _test_env = crate::test_env::read();
        // `∃r.D ⊑ E` over a one-level chain of simple roles: chain_clauses
        // already encodes it completely.
        let mut tbox = forall_over_chain();
        tbox.pop();
        tbox.push(clause([concept("D", v("y")), role("r", v("x"), v("y"))], [concept("E", v("x"))]));
        let info = detect_role_chains(&tbox);
        assert_eq!(
            chain_consumer_automaton_clauses(&tbox, &info, ChainConsumerPass::Tbox),
            (Vec::new(), 0)
        );
    }

    #[test]
    fn consumer_of_the_converse_of_a_chain_target_gets_backward_markers() {
        let _test_env = crate::test_env::read();
        // `r⁻` proxy `p` and `∃p.D ⊑ E`: the same-orientation encodings do
        // not see `p` as chain-derived.
        let mut tbox = forall_over_chain();
        tbox.pop();
        tbox.push(clause([role("r", v("x"), v("y"))], [role("p", v("y"), v("x"))]));
        tbox.push(clause([role("p", v("x"), v("y"))], [role("r", v("y"), v("x"))]));
        tbox.push(clause([concept("D", v("y")), role("p", v("x"), v("y"))], [concept("E", v("x"))]));
        let info = detect_role_chains(&tbox);
        let (out, unencoded) =
            chain_consumer_automaton_clauses(&tbox, &info, ChainConsumerPass::Tbox);
        assert_eq!(unencoded, 0);
        assert!(out.contains(&clause([concept("D", var_x())], [concept("__riab__p__c0__q0", var_x())])));
        assert!(out.iter().any(|c| matches!(c.body.as_slice(),
            [Atom::Concept(m, t)] if m.starts_with("__riab__p__c0__q") && *t == var_x())
            && c.head == vec![concept("E", var_x())]));
    }

    /// `part_of` and `has_part` inverse and transitive, `starts ⊑ part_of`
    /// with `starts` a chain target (`u ∘ w ⊑ starts`), `∃has_part.D ⊑ E`.
    fn partonomy(generated: &[&str]) -> (Vec<DLClause>, ChainInfo) {
        let trans = |r: &str| {
            clause([role(r, v("x"), v("y")), role(r, v("y"), v("z"))], [role(r, v("x"), v("z"))])
        };
        let tbox = vec![
            trans("part_of"),
            trans("has_part"),
            clause([role("part_of", v("x"), v("y"))], [role("has_part", v("y"), v("x"))]),
            clause([role("has_part", v("x"), v("y"))], [role("part_of", v("y"), v("x"))]),
            clause([role("starts", v("x"), v("y"))], [role("part_of", v("x"), v("y"))]),
            clause([role("u", v("x"), v("y")), role("w", v("y"), v("z"))], [role("starts", v("x"), v("z"))]),
            clause([concept("D", v("y")), role("has_part", v("x"), v("y"))], [concept("E", v("x"))]),
        ];
        let mut info = detect_role_chains(&tbox);
        info.generated_roles = Some(generated.iter().map(|r| r.to_string()).collect());
        (tbox, info)
    }

    #[test]
    fn a_reversed_sub_role_of_an_inverse_adds_no_path() {
        let _test_env = crate::test_env::read();
        // `w` never gets an edge, so `L(has_part)` over the stream's edges is
        // `(has_part | starts⁻)⁺`, and every `starts` edge is a `has_part`
        // edge read backwards (`starts ⊑ part_of`, `part_of ⊑ has_part⁻`):
        // the transitivity encoding already covers the consumer.
        let (tbox, info) = partonomy(&["part_of", "has_part", "starts", "u"]);
        assert_eq!(chain_consumer_automaton_clauses(&tbox, &info, ChainConsumerPass::Tbox), (Vec::new(), 0));
    }

    #[test]
    fn a_realizable_chain_below_an_inverse_keeps_its_markers() {
        let _test_env = crate::test_env::read();
        // With `w` edges, `w⁻ u⁻` is a word of `L(has_part)` that no
        // same-orientation encoding produces.
        let (tbox, info) = partonomy(&["part_of", "has_part", "starts", "u", "w"]);
        let (out, unencoded) = chain_consumer_automaton_clauses(&tbox, &info, ChainConsumerPass::Tbox);
        assert_eq!(unencoded, 0);
        assert!(out.contains(&clause([concept("D", var_x())], [concept("__riab__has_part__c0__q0", var_x())])));
    }
}
