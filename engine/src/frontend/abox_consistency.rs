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
    if disjoint.is_empty() {
        return None;
    }
    let mut mem: HashMap<String, HashSet<String>> = HashMap::new();
    let mut roles: Vec<(String, String, String)> = Vec::new();
    let mut same: Vec<(String, String)> = Vec::new();
    for ax in ont.abox() {
        match ax {
            Axiom::ConceptAssertion(Concept::Name(c), i) => {
                mem.entry(i.clone()).or_default().insert(c.clone());
            }
            Axiom::RoleAssertion(p, a, b) => roles.push((p.clone(), a.clone(), b.clone())),
            Axiom::SameIndividual(a, b) => same.push((a.clone(), b.clone())),
            _ => {}
        }
    }
    Some(AboxData {
        sup,
        disjoint,
        mem,
        roles,
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
