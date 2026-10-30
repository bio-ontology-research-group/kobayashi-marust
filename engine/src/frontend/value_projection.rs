//! Exact object-level projection of data-property assertions.
//!
//! For a group of data properties (connected by `SubDataPropertyOf`) whose
//! every TBox use is functionality, `C ⊑ ≤ 1 p[.R]`, a domain, an atomic
//! range, or a sub-property axiom, an asserted value is observed only
//! through (a) the domain classes of its subject, (b) its membership in the
//! ranges, which is decided per literal, and (c) whether two values of one
//! counted property on one element are distinct. The projection replaces
//! every assertion `u(a, v)` of such a group by
//!
//! - `a : C` for every domain `C` of a super-property of `u`, and
//! - for every counted `(q, C, R)` with `u ⊑* q` and `v ∈ R`, the index
//!   digits of the identity class of `v` among the values of `(q, C, R)` as
//!   object classes on `a`, with `C ⊓ digit_k_0 ⊓ digit_k_1 ⊑ ⊥` per position,
//!
//! so no data successor is created for an asserted value. The exactness
//! argument is in docs/DATATYPES.md, "Object-level projection of data
//! assertions". A group with any other use, or with a literal whose range
//! membership or identity the oracle does not decide, is left to the data
//! value encoding.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::datatypes;
use super::syntax::{Axiom, Concept, Role};

/// A positive data assertion `role(individual, literal)` awaiting carriage.
pub struct DataAssertion<'a> {
    pub role: &'a str,
    pub individual: &'a str,
    pub literal: &'a str,
}

/// The result: the axioms to add, and which assertions they replace.
pub struct Projection {
    pub axioms: Vec<Axiom>,
    pub projected: Vec<bool>,
}

/// Prefix of the index classes (object-sorted, internal).
pub const PROJECTION_PREFIX: &str = "__dvp__";

fn roles_in(concept: &Concept, out: &mut Vec<(String, bool)>) {
    match concept {
        Concept::Not(inner) => roles_in(inner, out),
        Concept::And(items) | Concept::Or(items) => items.iter().for_each(|c| roles_in(c, out)),
        Concept::Exists(role, filler) | Concept::Forall(role, filler)
        | Concept::AtLeast(_, role, filler) | Concept::AtMost(_, role, filler) => {
            match role {
                Role::Name(name) => out.push((name.clone(), false)),
                Role::Inverse(name) => out.push((name.clone(), true)),
                Role::Universal => out.push((String::new(), true)),
            }
            roles_in(filler, out);
        }
        Concept::HasSelf(Role::Name(name) | Role::Inverse(name)) => out.push((name.clone(), true)),
        _ => {}
    }
}

fn mentions(concept: &Concept, roles: &BTreeSet<String>) -> bool {
    let mut found = Vec::new();
    roles_in(concept, &mut found);
    found.iter().any(|(name, _)| roles.contains(name) || name.is_empty())
}

fn is_range_name(concept: &Concept) -> Option<&str> {
    match concept {
        Concept::Name(name) if name.starts_with("__dt__") => Some(name),
        _ => None,
    }
}

/// Project the assertions of every admissible group. `blocked` disables the
/// projection (keys or rules compare values; negative assertions observe
/// a value's identity).
pub fn project(axioms: &[&Axiom], assertions: &[DataAssertion], blocked: bool) -> Projection {
    let mut projection = Projection { axioms: Vec::new(), projected: vec![false; assertions.len()] };
    if blocked || assertions.is_empty() {
        return projection;
    }
    // Data roles and their inclusion closure (both directions: a group).
    let mut parent: HashMap<String, String> = HashMap::new();
    fn find(parent: &mut HashMap<String, String>, x: &str) -> String {
        let mut root = x.to_string();
        while let Some(next) = parent.get(&root).cloned() {
            if next == root { break; }
            root = next;
        }
        root
    }
    let mut data: BTreeSet<String> = assertions.iter().map(|a| a.role.to_string()).collect();
    let mut supers: HashMap<String, Vec<String>> = HashMap::new();
    loop {
        let before = data.len();
        for axiom in axioms {
            if let Axiom::RoleInclusion(sub, sup) = axiom {
                if data.contains(sub) || data.contains(sup) {
                    data.insert(sub.clone());
                    data.insert(sup.clone());
                }
            }
        }
        if data.len() == before { break; }
    }
    for axiom in axioms {
        if let Axiom::RoleInclusion(sub, sup) = axiom {
            if data.contains(sub) {
                supers.entry(sub.clone()).or_default().push(sup.clone());
                let (a, b) = (find(&mut parent, sub), find(&mut parent, sup));
                if a != b { parent.insert(a, b); }
            }
        }
    }
    // Uses of the group roles.
    let mut blocked_groups: BTreeSet<String> = BTreeSet::new();
    let mut domains: BTreeMap<String, Vec<Concept>> = BTreeMap::new();
    let mut ranges: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // counted (role, guard, filler range or None)
    let mut counted: Vec<(String, Concept, Option<String>)> = Vec::new();
    let mut block = |role: &str, parent: &mut HashMap<String, String>, blocked: &mut BTreeSet<String>| {
        blocked.insert(find(parent, role));
    };
    for axiom in axioms {
        let mut used: Vec<(String, bool)> = Vec::new();
        match axiom {
            Axiom::SubClassOf(a, b) | Axiom::EquivalentClasses(a, b) | Axiom::DisjointClasses(a, b) => {
                roles_in(a, &mut used);
                roles_in(b, &mut used);
            }
            Axiom::ConceptAssertion(c, _) => roles_in(c, &mut used),
            Axiom::FunctionalRole(r) | Axiom::InverseFunctionalRole(r) | Axiom::TransitiveRole(r)
            | Axiom::SymmetricRole(r) | Axiom::AsymmetricRole(r) | Axiom::ReflexiveRole(r)
            | Axiom::IrreflexiveRole(r) => used.push((r.clone(), false)),
            Axiom::RoleAssertion(r, ..) | Axiom::NegativeRoleAssertion(r, ..) => used.push((r.clone(), true)),
            Axiom::InverseRoles(a, b) | Axiom::DisjointRoles(a, b) => {
                used.push((a.clone(), true));
                used.push((b.clone(), true));
            }
            Axiom::RoleChain(chain, head) => {
                used.extend(chain.iter().map(|r| (r.clone(), true)));
                used.push((head.clone(), true));
            }
            Axiom::RoleInclusion(..) => continue,
            Axiom::SameIndividual(..) | Axiom::DifferentIndividuals(..) => continue,
            Axiom::Rule(..) | Axiom::DataRule(..) => return projection,
        }
        let group_roles: Vec<&(String, bool)> = used.iter().filter(|(r, _)| data.contains(r)).collect();
        if group_roles.is_empty() {
            continue;
        }
        let shape_ok = match axiom {
            Axiom::FunctionalRole(r) => {
                counted.push((r.clone(), Concept::Top, None));
                true
            }
            Axiom::SubClassOf(Concept::Top, Concept::Forall(Role::Name(r), filler)) => match is_range_name(filler) {
                Some(range) => { ranges.entry(r.clone()).or_default().push(range.to_string()); true }
                None => false,
            },
            Axiom::SubClassOf(Concept::Exists(Role::Name(r), filler), class)
                if matches!(filler.as_ref(), Concept::Top) && !mentions(class, &data) =>
            {
                domains.entry(r.clone()).or_default().push(class.clone());
                true
            }
            Axiom::SubClassOf(guard, Concept::AtMost(1, Role::Name(r), filler)) if !mentions(guard, &data) => {
                match filler.as_ref() {
                    Concept::Top => { counted.push((r.clone(), guard.clone(), None)); true }
                    other => match is_range_name(other) {
                        Some(range) => { counted.push((r.clone(), guard.clone(), Some(range.to_string()))); true }
                        None => false,
                    },
                }
            }
            _ => false,
        };
        if !shape_ok || group_roles.iter().any(|(_, odd)| *odd) {
            for (r, _) in group_roles {
                block(r, &mut parent, &mut blocked_groups);
            }
        }
    }
    let closure = |role: &str| -> Vec<String> {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut stack = vec![role.to_string()];
        while let Some(r) = stack.pop() {
            if seen.insert(r.clone()) {
                if let Some(next) = supers.get(&r) {
                    stack.extend(next.iter().cloned());
                }
            }
        }
        seen.into_iter().collect()
    };
    // Decide every literal of a group; any undecided literal blocks it.
    let mut index: BTreeMap<usize, BTreeMap<String, usize>> = BTreeMap::new();
    let mut plans: Vec<Option<Vec<(usize, String)>>> = Vec::with_capacity(assertions.len());
    for assertion in assertions {
        let group = find(&mut parent, assertion.role);
        if blocked_groups.contains(&group) {
            plans.push(None);
            continue;
        }
        let up = closure(assertion.role);
        let mut ok = true;
        let mut slots: Vec<(usize, String)> = Vec::new();
        for q in &up {
            for range in ranges.get(q).map(Vec::as_slice).unwrap_or(&[]) {
                if datatypes::literal_in_range(assertion.literal, range) != Some(true) {
                    ok = false;
                }
            }
            for (slot, (role, _, filler)) in counted.iter().enumerate() {
                if role != q {
                    continue;
                }
                let member = match filler {
                    None => Some(true),
                    Some(range) => datatypes::literal_in_range(assertion.literal, range),
                };
                match (member, datatypes::literal_identity_key(assertion.literal)) {
                    (Some(true), Some(key)) => slots.push((slot, key)),
                    (Some(false), _) => {}
                    _ => ok = false,
                }
            }
        }
        if ok {
            plans.push(Some(slots));
        } else {
            blocked_groups.insert(group);
            plans.push(None);
        }
    }
    // A group blocked by a later literal blocks its earlier assertions too.
    for (assertion, plan) in assertions.iter().zip(plans.iter_mut()) {
        if blocked_groups.contains(&find(&mut parent, assertion.role)) {
            *plan = None;
        }
    }
    for plan in plans.iter().flatten() {
        for (slot, key) in plan {
            let classes = index.entry(*slot).or_default();
            let next = classes.len();
            classes.entry(key.clone()).or_insert(next);
        }
    }
    let positions = |slot: usize| -> usize {
        let classes = index.get(&slot).map_or(0, BTreeMap::len);
        if classes <= 1 { 0 } else { (usize::BITS - (classes - 1).leading_zeros()) as usize }
    };
    let digit = |slot: usize, position: usize, value: usize| {
        Concept::Name(format!("{PROJECTION_PREFIX}{slot}__{position}__{value}"))
    };
    for (slot, (_, guard, _)) in counted.iter().enumerate() {
        for position in 0..positions(slot) {
            let (zero, one) = (digit(slot, position, 0), digit(slot, position, 1));
            projection.axioms.push(match guard {
                Concept::Top => Axiom::DisjointClasses(zero, one),
                guard => Axiom::SubClassOf(
                    Concept::And([guard.clone(), zero, one].into_iter().collect()),
                    Concept::Bottom,
                ),
            });
        }
    }
    for (at, (assertion, plan)) in assertions.iter().zip(&plans).enumerate() {
        let Some(slots) = plan else { continue };
        projection.projected[at] = true;
        let individual = assertion.individual.to_string();
        for q in closure(assertion.role) {
            for class in domains.get(&q).map(Vec::as_slice).unwrap_or(&[]) {
                projection.axioms.push(Axiom::ConceptAssertion(class.clone(), individual.clone()));
            }
        }
        for (slot, key) in slots {
            let class = index[slot][key];
            for position in 0..positions(*slot) {
                projection.axioms.push(Axiom::ConceptAssertion(
                    digit(*slot, position, (class >> position) & 1),
                    individual.clone(),
                ));
            }
        }
    }
    projection
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(n: &str) -> Concept { Concept::Name(n.to_string()) }
    fn role(n: &str) -> Role { Role::Name(n.to_string()) }
    fn assertion<'a>(role: &'a str, individual: &'a str, literal: &'a str) -> DataAssertion<'a> {
        DataAssertion { role, individual, literal }
    }

    fn functional_tbox() -> Vec<Axiom> {
        vec![
            Axiom::FunctionalRole("u".into()),
            Axiom::SubClassOf(Concept::Top, Concept::Forall(role("u"), Box::new(name("__dt__xsd:integer")))),
            Axiom::SubClassOf(Concept::Exists(role("u"), Box::new(Concept::Top)), name("D")),
            Axiom::RoleInclusion("v".into(), "u".into()),
        ]
    }

    #[test]
    fn functional_values_become_disjoint_digits() {
        let tbox = functional_tbox();
        let axioms: Vec<&Axiom> = tbox.iter().collect();
        let data = [assertion("u", "a", "\"1\"^^xsd:integer"), assertion("v", "b", "\"2\"^^xsd:integer"),
            assertion("u", "c", "\"01\"^^xsd:integer")];
        let projection = project(&axioms, &data, false);
        assert_eq!(projection.projected, vec![true, true, true]);
        let classes_of = |individual: &str| -> BTreeSet<String> {
            projection.axioms.iter().filter_map(|axiom| match axiom {
                Axiom::ConceptAssertion(Concept::Name(n), i) if i == individual => Some(n.clone()),
                _ => None,
            }).collect()
        };
        // Domains are asserted; `1` and `01` share their digits, `2` differs.
        assert!(classes_of("a").contains("D") && classes_of("b").contains("D"));
        assert_eq!(classes_of("a"), classes_of("c"));
        assert_ne!(classes_of("a"), classes_of("b"));
        let differing: Vec<String> = classes_of("a").symmetric_difference(&classes_of("b")).cloned().collect();
        let disjoint = projection.axioms.iter().any(|axiom| matches!(axiom,
            Axiom::DisjointClasses(Concept::Name(x), Concept::Name(y))
                if differing.contains(x) && differing.contains(y)));
        assert!(disjoint, "{:?}", projection.axioms);
    }

    #[test]
    fn any_other_use_or_undecided_literal_keeps_the_group() {
        let mut tbox = functional_tbox();
        tbox.push(Axiom::SubClassOf(name("A"), Concept::Exists(role("u"), Box::new(name("__dt__xsd:integer")))));
        let axioms: Vec<&Axiom> = tbox.iter().collect();
        let data = [assertion("u", "a", "\"1\"^^xsd:integer"), assertion("w", "a", "\"x\"")];
        let projection = project(&axioms, &data, false);
        // `u` (and its sub-property group) is used existentially; `w` is free.
        assert_eq!(projection.projected, vec![false, true]);
        let tbox = functional_tbox();
        let axioms: Vec<&Axiom> = tbox.iter().collect();
        // A string under the integer range is not in the range: not projected.
        let projection = project(&axioms, &[assertion("u", "a", "\"x\"^^xsd:string")], false);
        assert_eq!(projection.projected, vec![false]);
        // Keys, rules or negative assertions block the projection.
        let projection = project(&axioms, &[assertion("u", "a", "\"1\"^^xsd:integer")], true);
        assert_eq!(projection.projected, vec![false]);
    }

    #[test]
    fn class_conditional_bounds_guard_their_clash() {
        let tbox = vec![Axiom::SubClassOf(name("C"), Concept::AtMost(1, role("u"), Box::new(Concept::Top)))];
        let axioms: Vec<&Axiom> = tbox.iter().collect();
        let data = [assertion("u", "a", "\"p\""), assertion("u", "a", "\"q\"")];
        let projection = project(&axioms, &data, false);
        assert_eq!(projection.projected, vec![true, true]);
        assert!(projection.axioms.iter().any(|axiom| matches!(axiom,
            Axiom::SubClassOf(Concept::And(items), Concept::Bottom) if items.contains(&name("C")))));
    }
}
