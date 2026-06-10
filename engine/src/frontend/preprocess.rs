//! Sound nominal / transitivity / role-chain / domain-range preprocessing.
//!
//! Direct port of `engine/py/preprocess.py`: `nominal_clauses`,
//! `domain_range_clauses`, `detect_role_chains`, `transitivity_clauses`,
//! `chain_clauses`, `_is_chain_axiom`, and `augment`.

use std::collections::{HashMap, HashSet};

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
    let mut ind_to_nom: HashMap<&str, &str> = HashMap::new();
    for (nom, ind) in &hooks.nominal_to_individual {
        ind_to_nom.insert(ind.as_str(), nom.as_str());
    }
    let x = var_x();
    let mut extra = Vec::new();
    for c in abox {
        if !c.body.is_empty() {
            continue; // only unconditional ABox facts
        }
        for a in &c.head {
            if let Atom::Concept(concept, Term::Ind(name)) = a {
                if let Some(nom) = ind_to_nom.get(name.as_str()) {
                    extra.push(clause(
                        [Atom::Concept(nom.to_string(), x.clone())],
                        [Atom::Concept(concept.clone(), x.clone())],
                    ));
                }
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
struct ChainInfo {
    trans: Vec<String>,
    chains: Vec<(String, String, String)>,
}

/// Port of `detect_role_chains`.
fn detect_role_chains(tbox: &[DLClause]) -> ChainInfo {
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
    ChainInfo { trans, chains }
}

fn role_parts(a: &Atom) -> (&str, &Term, &Term) {
    match a {
        Atom::Role(r, s, t) => (r.as_str(), s, t),
        _ => unreachable!("role_parts on non-role atom"),
    }
}

/// Port of `transitivity_clauses`.
pub fn transitivity_clauses(tbox: &[DLClause]) -> Vec<DLClause> {
    let info = detect_role_chains(tbox);
    if info.trans.is_empty() {
        return Vec::new();
    }
    let trans: std::collections::HashSet<&str> = info.trans.iter().map(|s| s.as_str()).collect();
    let x = var_x();
    let mut extra = Vec::new();
    // seen: (role, sorted concepts-on-y) -> P name
    let mut seen: HashMap<(String, Vec<String>), String> = HashMap::new();
    for c in tbox {
        let roles: Vec<&Atom> = c.body.iter().filter(|a| is_role(a)).collect();
        if roles.len() != 1 {
            continue;
        }
        let (rrole, rsource, rtarget) = role_parts(roles[0]);
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

/// Port of `chain_clauses`.
pub fn chain_clauses(tbox: &[DLClause]) -> Vec<DLClause> {
    let info = detect_role_chains(tbox);
    if info.chains.is_empty() {
        return Vec::new();
    }
    // by_t: T -> [(R,S)]
    let mut by_t: HashMap<String, Vec<(String, String)>> = HashMap::new();
    for (r, s, t) in &info.chains {
        by_t.entry(t.clone()).or_default().push((r.clone(), s.clone()));
    }
    let x = var_x();
    let mut extra = Vec::new();
    // seen: (S, sorted concepts-on-y) -> Q name
    let mut seen: HashMap<(String, Vec<String>), String> = HashMap::new();
    for c in tbox {
        let roles: Vec<&Atom> = c.body.iter().filter(|a| is_role(a)).collect();
        if roles.len() != 1 {
            continue;
        }
        let (trole, tsource, ttarget) = role_parts(roles[0]);
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
    let mut bridge_edges: HashSet<(&str, &str)> = HashSet::new();
    let mut partners: HashMap<&str, Vec<&str>> = HashMap::new();
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
                rs == st
                    && rt == ss
                    && rs != rt
                    && bridge_edges.contains(&(r.as_str(), s.as_str()))
            }
            _ => false,
        }
    };
    let mut consumed: HashSet<String> = HashSet::new();
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
/// relevant"). A role `R` is concept-relevant if some clause has an `R`-atom in
/// its body and a concept or equality atom in its head (the body edge is read
/// to derive a concept membership or a merge), or if `R` feeds — through a
/// role-headed clause such as a subrole axiom, role chain, or transitivity —
/// another concept-relevant role. Domain (`R(x,y) -> D(x)`), range
/// (`R(x,y) -> D(y)`) and universal (`A(x), R(x,y) -> C(y)`) clauses all carry
/// a concept head, so they seed relevance directly.
///
/// Symmetric / inverse axioms only add *reverse* edges for their role. If that
/// role is not concept-relevant, no reverse edge it could produce is ever read
/// to derive a concept, so the symmetry / inverse is inert for classification:
/// dropping it changes no named-concept subsumption, and the ontology can take
/// the EL fast path. The over-approximation is conservative — a clause with a
/// mixed concept+role head marks its body roles relevant, so the analysis only
/// ever errs toward calling a role relevant (keeping it on the CB engine).
pub fn concept_relevant_roles(tbox: &[DLClause]) -> HashSet<String> {
    let mut relevant: HashSet<String> = HashSet::new();
    // Role-headed clauses: (head role, body roles). Only those with at least one
    // body role can propagate relevance backward; the millions of existential
    // `C(x) -> R(x,f)` clauses have an empty body-role list and are skipped.
    let mut role_edges: Vec<(String, Vec<String>)> = Vec::new();
    for c in tbox {
        let body_roles: Vec<&str> = c
            .body
            .iter()
            .filter_map(|a| match a {
                Atom::Role(r, _, _) => Some(r.as_str()),
                _ => None,
            })
            .collect();
        if body_roles.is_empty() {
            continue;
        }
        let head_has_concept = c
            .head
            .iter()
            .any(|a| matches!(a, Atom::Concept(..) | Atom::Eq(..)));
        if head_has_concept {
            for r in &body_roles {
                relevant.insert((*r).to_string());
            }
        }
        for a in &c.head {
            if let Atom::Role(s, _, _) = a {
                role_edges.push((s.clone(), body_roles.iter().map(|r| r.to_string()).collect()));
            }
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (head_role, body_roles) in &role_edges {
            if relevant.contains(head_role) {
                for r in body_roles {
                    if relevant.insert(r.clone()) {
                        changed = true;
                    }
                }
            }
        }
    }
    relevant
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
            (Atom::Role(r, rs, rt), Atom::Role(s, ss, st))
                if rs == st && rt == ss && rs != rt =>
            {
                let drop = (r == s && sym_inert.contains(r.as_str()))
                    || inv_inert.contains(&(r.as_str(), s.as_str()));
                !drop
            }
            _ => true,
        }
    });
}

/// Port of `_is_chain_axiom`.
fn is_chain_axiom(c: &DLClause) -> bool {
    let roles: Vec<&Atom> = c.body.iter().filter(|a| is_role(a)).collect();
    let heads: Vec<&Atom> = c.head.iter().collect();
    if roles.len() == 2 && c.body.len() == 2 && heads.len() == 1 && is_role(heads[0]) {
        let r0 = roles[0];
        let r1 = roles[1];
        let h = heads[0];
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

/// Port of `augment`: tbox minus raw chain axioms, plus nominal / transitivity /
/// chain encodings.
pub fn augment(tbox: Vec<DLClause>, abox: &[DLClause], hooks: &GroundHooks) -> Vec<DLClause> {
    let mut base: Vec<DLClause> = tbox.iter().filter(|c| !is_chain_axiom(c)).cloned().collect();
    base.extend(nominal_clauses(abox, hooks));
    base.extend(transitivity_clauses(&tbox));
    base.extend(chain_clauses(&tbox));
    base
}

#[cfg(test)]
mod tests {
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
    fn prunes_both_directions_when_pair_unconsumed() {
        // A ⊑ ∃R.B yields only a head occurrence of R; nothing consumes R or S.
        let producer = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [role("R", var_x(), Term::Fun("f".to_string(), Box::new(var_x())))],
        );
        let mut tbox = vec![producer.clone(), bridge("R", "S"), bridge("S", "R")];
        prune_dead_inverse_bridges(&mut tbox, &[pair("R", "S")]);
        assert_eq!(tbox, vec![producer]);
    }

    #[test]
    fn keeps_only_consumed_direction() {
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
            vec![consumer, bridge("R", "S"), bridge("S", "T"), bridge("T", "S")]
        );
    }

    #[test]
    fn same_orientation_subrole_clause_is_not_a_bridge() {
        // R(x,y) → S(x,y) is a role-hierarchy clause: never pruned, and its
        // body occurrence of R keeps nothing alive for the R→S bridge (S is
        // still unconsumed).
        let sub = clause(
            [role("R", var_x(), var_y())],
            [role("S", var_x(), var_y())],
        );
        let mut tbox = vec![sub.clone(), bridge("R", "S"), bridge("S", "R")];
        prune_dead_inverse_bridges(&mut tbox, &[pair("R", "S")]);
        // S→R survives: the hierarchy clause consumes R. R→S dies.
        assert_eq!(tbox, vec![sub, bridge("S", "R")]);
    }

    #[test]
    fn noop_without_pairs() {
        let sub = clause(
            [role("R", var_x(), var_y())],
            [role("S", var_y(), var_x())],
        );
        let mut tbox = vec![sub.clone()];
        prune_dead_inverse_bridges(&mut tbox, &[]);
        assert_eq!(tbox, vec![sub]);
    }

    fn relevant_set(items: &[&str]) -> HashSet<String> {
        items.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn relevance_skips_existential_only_role() {
        // A ⊑ ∃R.B (head occurrence of R + concept B on the successor) and the
        // transitivity/self-bridge of R. R never sits in a body that yields a
        // concept, so it is inert.
        let producer = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [role("R", var_x(), Term::Fun("f".to_string(), Box::new(var_x())))],
        );
        let succ = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [Atom::Concept(
                "B".to_string(),
                Term::Fun("f".to_string(), Box::new(var_x())),
            )],
        );
        let trans = clause(
            [role("R", var_x(), var_y()), role("R", var_y(), Term::Var("z".to_string()))],
            [role("R", var_x(), Term::Var("z".to_string()))],
        );
        let tbox = vec![producer, succ, trans, bridge("R", "R")];
        assert!(concept_relevant_roles(&tbox).is_empty());
    }

    #[test]
    fn relevance_marks_domain_and_propagates_through_subrole() {
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
        let producer = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [role("R", var_x(), Term::Fun("f".to_string(), Box::new(var_x())))],
        );
        let mut tbox = vec![producer.clone(), bridge("R", "R")];
        let relevant = HashSet::new();
        prune_inert_role_bridges(&mut tbox, &["R".to_string()], &[], &relevant);
        assert_eq!(tbox, vec![producer]);
    }

    #[test]
    fn keeps_relevant_symmetric_self_bridge() {
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
        let producer = clause(
            [Atom::Concept("A".to_string(), var_x())],
            [role("R", var_x(), Term::Fun("f".to_string(), Box::new(var_x())))],
        );
        let mut tbox = vec![producer.clone(), bridge("R", "S"), bridge("S", "R")];
        let relevant = HashSet::new();
        prune_inert_role_bridges(&mut tbox, &[], &[pair("R", "S")], &relevant);
        assert_eq!(tbox, vec![producer]);
    }
}
