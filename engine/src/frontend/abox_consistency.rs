//! Sound ABox-inconsistency precheck.
//!
//! Detects when the asserted ABox forces an individual into two classes that
//! are asserted disjoint -- a real OWL entailment of global inconsistency. The
//! CB engine misses these because it drops individual/ABox clauses (the ALCHIQ
//! core maps `Ind`/`Aux` terms to `None` in `reasoner.rs`), so an ABox clash
//! never reaches saturation. Found on the ORE BioPAX / cocktail ontologies
//! (`6720`/`15288`/`443`/`7052`), where Konclude and ELK report every class
//! unsatisfiable (the ontology is inconsistent) but KM emitted the full
//! taxonomy of subsumptions.
//!
//! Conservative and sound: only NAMED classes participate. Complex operands of
//! `DisjointClasses`/`EquivalentClasses`/`SubClassOf` and complex assertion
//! concepts are skipped, so every detected clash is a genuine entailment
//! (`a : C`, `a : C'`, `C ⊑* D`, `C' ⊑* D'`, `DisjointClasses(D, D')`). It is
//! incomplete by design: existential-, datatype-, or complex-concept-driven
//! clashes are not detected here (the engine/tableau own those).
//!
//! Membership is closed under: the named subclass/equivalence hierarchy, object
//! property domain/range applied to role assertions, and `SameIndividual`.

use std::collections::{HashMap, HashSet};

use super::rbox::RboxRecord;
use super::syntax::{Axiom, Concept, Ontology};

/// Named-class data projected from the parsed ontology. Built only when the
/// ontology has at least one named-class disjointness pair, so ontologies
/// without relevant disjointness (including the large TBox-only giants) pay
/// only a single linear scan of the TBox axioms and allocate nothing.
pub struct AboxData {
    /// named subclass edges: class -> direct named superclasses
    sup: HashMap<String, Vec<String>>,
    /// named disjoint pairs
    disjoint: Vec<(String, String)>,
    /// individual -> directly asserted named classes
    mem: HashMap<String, HashSet<String>>,
    /// named object-property assertions `(prop, subject, object)`
    roles: Vec<(String, String, String)>,
    /// negative object-property assertions `(prop, subject, object)`:
    /// `¬p(a,b)` clashing with an asserted `p'(a,b)` for `p' ⊑* p` is a
    /// genuine global inconsistency.
    neg_roles: Vec<(String, String, String)>,
    /// `SameIndividual` pairs
    same: Vec<(String, String)>,
}

/// Project the named-class ABox-consistency data from `ont`. Returns `None`
/// (the common case) when there is no named-class disjointness, since then no
/// clash of this shape is possible and nothing further need be collected.
pub fn collect(ont: &Ontology) -> Option<AboxData> {
    let mut sup: HashMap<String, Vec<String>> = HashMap::new();
    let mut disjoint: Vec<(String, String)> = Vec::new();
    for ax in ont.tbox() {
        match ax {
            Axiom::SubClassOf(Concept::Name(a), Concept::Name(b)) => {
                sup.entry(a.clone()).or_default().push(b.clone());
            }
            Axiom::EquivalentClasses(Concept::Name(a), Concept::Name(b)) => {
                sup.entry(a.clone()).or_default().push(b.clone());
                sup.entry(b.clone()).or_default().push(a.clone());
            }
            Axiom::DisjointClasses(Concept::Name(a), Concept::Name(b)) if a != b => {
                disjoint.push((a.clone(), b.clone()));
            }
            _ => {}
        }
    }
    // Negative object-property assertions are a clash source independent of
    // class disjointness, so their presence also forces the ABox collection.
    let has_negative = ont
        .abox()
        .any(|ax| matches!(ax, Axiom::NegativeRoleAssertion(..)));
    if disjoint.is_empty() && !has_negative {
        return None;
    }
    let mut mem: HashMap<String, HashSet<String>> = HashMap::new();
    let mut roles: Vec<(String, String, String)> = Vec::new();
    let mut neg_roles: Vec<(String, String, String)> = Vec::new();
    let mut same: Vec<(String, String)> = Vec::new();
    for ax in ont.abox() {
        match ax {
            Axiom::ConceptAssertion(Concept::Name(c), i) => {
                mem.entry(i.clone()).or_default().insert(c.clone());
            }
            Axiom::RoleAssertion(p, a, b) => roles.push((p.clone(), a.clone(), b.clone())),
            Axiom::NegativeRoleAssertion(p, a, b) => {
                neg_roles.push((p.clone(), a.clone(), b.clone()))
            }
            Axiom::SameIndividual(a, b) => same.push((a.clone(), b.clone())),
            _ => {}
        }
    }
    Some(AboxData {
        sup,
        disjoint,
        mem,
        roles,
        neg_roles,
        same,
    })
}

/// Named classes directly asserted on some individual, plus the set of roles
/// with at least one assertion (their domain/range classes also provably
/// contain an individual; the caller adds those once the RBox is built).
/// Used for the asserted-member-of-unsat-class inconsistency rule.
pub fn asserted_profile(ont: &Ontology) -> (std::collections::BTreeSet<String>, HashSet<String>) {
    let mut classes = std::collections::BTreeSet::new();
    let mut roles = HashSet::new();
    for ax in ont.abox() {
        match ax {
            Axiom::ConceptAssertion(Concept::Name(c), _) => {
                classes.insert(c.clone());
            }
            Axiom::RoleAssertion(p, _, _) => {
                roles.insert(p.clone());
            }
            _ => {}
        }
    }
    (classes, roles)
}

fn uf_find(parent: &mut HashMap<String, String>, x: &str) -> String {
    if !parent.contains_key(x) {
        parent.insert(x.to_string(), x.to_string());
        return x.to_string();
    }
    let mut root = x.to_string();
    while parent[&root] != root {
        root = parent[&root].clone();
    }
    let mut cur = x.to_string();
    while parent[&cur] != root {
        let next = parent[&cur].clone();
        parent.insert(cur, root.clone());
        cur = next;
    }
    root
}

fn uf_union(parent: &mut HashMap<String, String>, a: &str, b: &str) {
    let ra = uf_find(parent, a);
    let rb = uf_find(parent, b);
    if ra != rb {
        parent.insert(ra, rb);
    }
}

/// All named ancestors of `start` (reflexive) under the subclass/equivalence
/// edges. Memoised in `cache`.
fn ancestors(
    sup: &HashMap<String, Vec<String>>,
    start: &str,
    cache: &mut HashMap<String, HashSet<String>>,
) -> HashSet<String> {
    if let Some(c) = cache.get(start) {
        return c.clone();
    }
    let mut seen: HashSet<String> = HashSet::new();
    seen.insert(start.to_string());
    let mut stack = vec![start.to_string()];
    while let Some(x) = stack.pop() {
        if let Some(ps) = sup.get(&x) {
            for p in ps {
                if seen.insert(p.clone()) {
                    stack.push(p.clone());
                }
            }
        }
    }
    cache.insert(start.to_string(), seen.clone());
    seen
}

impl AboxData {
    /// Finish the check using object-property domain/range from the RBox.
    /// Returns `true` iff some individual is provably a member of two disjoint
    /// named classes.
    pub fn is_inconsistent(mut self, rbox: &[RboxRecord]) -> bool {
        let mut dom: HashMap<&str, &str> = HashMap::new();
        let mut rng: HashMap<&str, &str> = HashMap::new();
        for r in rbox {
            match r {
                RboxRecord::Domain(p, d) => {
                    dom.insert(p.as_str(), d.as_str());
                }
                RboxRecord::Range(p, c) => {
                    rng.insert(p.as_str(), c.as_str());
                }
                _ => {}
            }
        }
        // role assertions contribute domain/range memberships
        for (p, a, b) in &self.roles {
            if let Some(d) = dom.get(p.as_str()) {
                self.mem
                    .entry(a.clone())
                    .or_default()
                    .insert((*d).to_string());
            }
            if let Some(c) = rng.get(p.as_str()) {
                self.mem
                    .entry(b.clone())
                    .or_default()
                    .insert((*c).to_string());
            }
        }
        // merge co-referent individuals (SameIndividual)
        let mut parent: HashMap<String, String> = HashMap::new();
        for (a, b) in &self.same {
            uf_union(&mut parent, a, b);
        }
        // NegativeObjectPropertyAssertion clash: `¬p(a,b)` together with an
        // asserted `p'(a',b')` where `p' ⊑* p` (named subrole closure) and
        // `a≈a'`, `b≈b'` (SameIndividual closure) is a genuine entailment of
        // global inconsistency. Sound: every step is an asserted axiom.
        if !self.neg_roles.is_empty() {
            let mut rsup: HashMap<&str, Vec<&str>> = HashMap::new();
            for r in rbox {
                if let RboxRecord::Subrole(s, p) = r {
                    rsup.entry(s.as_str()).or_default().push(p.as_str());
                }
            }
            // upward closure of a positive assertion's role under Subrole
            let role_ancestors = |start: &str| -> HashSet<String> {
                let mut seen: HashSet<String> = HashSet::new();
                seen.insert(start.to_string());
                let mut stack = vec![start.to_string()];
                while let Some(x) = stack.pop() {
                    if let Some(ps) = rsup.get(x.as_str()) {
                        for p in ps {
                            if seen.insert((*p).to_string()) {
                                stack.push((*p).to_string());
                            }
                        }
                    }
                }
                seen
            };
            let neg: Vec<(String, String, String)> = self
                .neg_roles
                .iter()
                .map(|(p, a, b)| (p.clone(), uf_find(&mut parent, a), uf_find(&mut parent, b)))
                .collect();
            for (p, a, b) in &self.roles {
                let ra = uf_find(&mut parent, a);
                let rb = uf_find(&mut parent, b);
                let sups = role_ancestors(p);
                if neg
                    .iter()
                    .any(|(np, na, nb)| *na == ra && *nb == rb && sups.contains(np))
                {
                    return true;
                }
            }
        }
        let mut merged: HashMap<String, HashSet<String>> = HashMap::new();
        for (ind, cs) in &self.mem {
            let r = uf_find(&mut parent, ind);
            merged.entry(r).or_default().extend(cs.iter().cloned());
        }
        // an individual whose closed class set contains both ends of a disjoint
        // pair witnesses global inconsistency
        let mut cache: HashMap<String, HashSet<String>> = HashMap::new();
        for cs in merged.values() {
            let mut all: HashSet<String> = HashSet::new();
            for c in cs {
                all.extend(ancestors(&self.sup, c, &mut cache));
            }
            for (a, b) in &self.disjoint {
                if all.contains(a) && all.contains(b) {
                    return true;
                }
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::syntax::Axiom;

    fn ont(axioms: Vec<Axiom>) -> Ontology {
        let mut o = Ontology::new();
        for ax in axioms {
            o.add(ax);
        }
        o
    }

    /// Regression: `R(a,b)` together with `¬R(a,b)` is a globally inconsistent
    /// ontology that was reported consistent with a full taxonomy (the negative
    /// assertion never reached any layer).
    #[test]
    fn negative_assertion_clash_is_detected() {
        let o = ont(vec![
            Axiom::RoleAssertion("r".into(), "a".into(), "b".into()),
            Axiom::NegativeRoleAssertion("r".into(), "a".into(), "b".into()),
        ]);
        let data = collect(&o).expect("negatives force collection");
        assert!(data.is_inconsistent(&[]));
    }

    /// The consistent direction: a negative assertion on a DIFFERENT pair must
    /// not fire (the precheck may only report provable clashes).
    #[test]
    fn negative_assertion_on_other_pair_is_consistent() {
        let o = ont(vec![
            Axiom::RoleAssertion("r".into(), "a".into(), "b".into()),
            Axiom::NegativeRoleAssertion("r".into(), "b".into(), "a".into()),
        ]);
        let data = collect(&o).expect("negatives force collection");
        assert!(!data.is_inconsistent(&[]));
    }

    /// Closure checks: the clash also fires through the named subrole
    /// hierarchy (`s(a,b)`, `s ⊑ r`, `¬r(a,b)`) and SameIndividual merging.
    #[test]
    fn negative_assertion_clash_closes_under_subroles_and_same_individual() {
        let o = ont(vec![
            Axiom::RoleAssertion("s".into(), "a".into(), "b".into()),
            Axiom::NegativeRoleAssertion("r".into(), "a2".into(), "b".into()),
            Axiom::SameIndividual("a".into(), "a2".into()),
        ]);
        let data = collect(&o).expect("negatives force collection");
        let rbox = vec![RboxRecord::Subrole("s".into(), "r".into())];
        assert!(data.is_inconsistent(&rbox));
    }

    /// The pre-existing early return must survive: no disjointness and no
    /// negative assertions ⇒ nothing to collect.
    #[test]
    fn collect_still_skips_without_disjointness_or_negatives() {
        let o = ont(vec![Axiom::RoleAssertion(
            "r".into(),
            "a".into(),
            "b".into(),
        )]);
        assert!(collect(&o).is_none());
    }

    /// This precheck is SOUND ONLY. It closes asserted memberships over named
    /// subclasses, domain/range and SameIndividual and fires on an ASSERTED
    /// disjoint pair, so a DERIVED contradiction escapes it. These are real
    /// inconsistent ontologies it reports nothing about, which is exactly why
    /// no automatic route may drop an ABox behind it: an inconsistent KB
    /// entails every subsumption, while a dropped ABox yields an ordinary
    /// taxonomy and hides that.
    #[test]
    fn derived_abox_contradictions_are_not_detected() {
        // `A ⊑ ⊥` with `ClassAssertion(A a)`: globally inconsistent, but ⊥ is
        // not an asserted disjoint pair, so the collection does not even start.
        let bottom = ont(vec![
            Axiom::SubClassOf(
                Concept::Name("A".into()),
                Concept::Name("owl:Nothing".into()),
            ),
            Axiom::ConceptAssertion(Concept::Name("A".into()), "a".into()),
        ]);
        assert!(
            collect(&bottom).is_none(),
            "an unsatisfiable asserted type is outside this precheck"
        );

        // A role-chain-derived range clash: `r(a,b)`, `s(b,c)`, `r∘s ⊑ t`,
        // `range(t) = D`, `DisjointClasses(D, E)`, `ClassAssertion(E c)`. The
        // KB is inconsistent, but the derivation needs the chain edge `t(a,c)`,
        // which no asserted axiom supplies.
        let chained = ont(vec![
            Axiom::DisjointClasses(Concept::Name("D".into()), Concept::Name("E".into())),
            Axiom::RoleAssertion("r".into(), "a".into(), "b".into()),
            Axiom::RoleAssertion("s".into(), "b".into(), "c".into()),
            Axiom::ConceptAssertion(Concept::Name("E".into()), "c".into()),
        ]);
        let data = collect(&chained).expect("the disjoint pair forces collection");
        assert!(
            !data.is_inconsistent(&[RboxRecord::Range("t".into(), "D".into())]),
            "a chain-derived clash is invisible to the asserted-only precheck"
        );
    }
}
