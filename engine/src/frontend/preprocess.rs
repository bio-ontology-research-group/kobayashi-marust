//! Sound nominal / transitivity / role-chain / domain-range preprocessing.
//!
//! Direct port of `engine/py/preprocess.py`: `nominal_clauses`,
//! `domain_range_clauses`, `detect_role_chains`, `transitivity_clauses`,
//! `chain_clauses`, `_is_chain_axiom`, and `augment`.

use std::collections::HashMap;

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
