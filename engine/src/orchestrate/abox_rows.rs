//! Entailed object property values and different individuals between named
//! individuals (W5b, `km classify --values`, `--different`).
//!
//! # Semantics
//!
//! For a consistent ontology `O`, named individuals `a`, `b` and a named
//! object property `r` of the source (not `owl:topObjectProperty` or
//! `owl:bottomObjectProperty`):
//!
//! * `VALUE r a b` iff `O ⊨ r(a, b)`;
//! * `DIFFERENT a b` iff `O ⊨ a ≠ b`, once per pair with `a < b`.
//!
//! # Mechanism
//!
//! The realization run's probes `P_a ≡ {a}` plus, for every property `r` and
//! individual `b`, a fresh class `V_rb ≡ ∃r.{b}` (`--values`) and, for every
//! individual `b`, `N_b ≡ ¬{b}` (`--different`). The extension only defines
//! fresh names, so it is conservative, and `O ⊨ r(a, b)` iff `{a} ⊑ ∃r.{b}`
//! iff `P_a ⊑ V_rb`, and `O ⊨ a ≠ b` iff `{a} ⊑ ¬{b}` iff `P_a ⊑ N_b`. All
//! pairs come from the one classification of the extended ontology that the
//! realization already needs, instead of one consistency test per pair.

use std::collections::{BTreeMap, BTreeSet};

use super::realize::{fresh_namespace_for, public_name};
use super::{Classification, OrchestrateError};

/// The rows of `--values` and `--different`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AboxRows {
    /// `[r, a, b]` rows, sorted; present iff `--values`.
    pub values: Option<Vec<[String; 3]>>,
    /// `[a, b]` rows with `a < b`, sorted; present iff `--different`.
    pub different: Option<Vec<[String; 2]>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Probe {
    Value(usize, usize),
    Not(usize),
}

/// The probe classes of one extension.
#[derive(Clone, Debug)]
pub struct AboxProbes {
    probes: BTreeMap<String, Probe>,
    roles: Vec<String>,
    individuals: Vec<String>,
    values: bool,
    different: bool,
}

impl AboxProbes {
    pub(super) fn is_probe(&self, name: &str) -> bool {
        self.probes.contains_key(name)
    }
}

/// The probe axioms for `roles` and `individuals` (source spellings).
pub(super) fn extension(
    text: &str,
    roles: &[String],
    individuals: &[String],
    values: bool,
    different: bool,
) -> (String, AboxProbes) {
    let ns = fresh_namespace_for(text, "aboxrows");
    let mut out = String::new();
    let mut probes = BTreeMap::new();
    if values {
        let role_bound = (roles.len().saturating_mul(individuals.len()) >= 256)
            .then(|| crate::frontend::named_role_bound::NamedRoleBound::compute(text))
            .flatten();
        for (r, role) in roles.iter().enumerate() {
            let pub_role = public_name(role);
            if let Some(bound) = &role_bound {
                let has_self = bound.role_has_self_by_full_iri(&pub_role);
                if !has_self {
                    let targets = bound.reachable_targets_by_full_iri(&pub_role);
                    for (b, individual) in individuals.iter().enumerate() {
                        if !targets.contains(&public_name(individual)) {
                            continue;
                        }
                        let probe = format!("{ns}value{r}_{b}");
                        out.push_str(&format!(
                            "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({role} ObjectOneOf({individual})))\n"
                        ));
                        probes.insert(probe, Probe::Value(r, b));
                    }
                    continue;
                }
            }
            for (b, individual) in individuals.iter().enumerate() {
                let probe = format!("{ns}value{r}_{b}");
                out.push_str(&format!(
                    "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({role} ObjectOneOf({individual})))\n"
                ));
                probes.insert(probe, Probe::Value(r, b));
            }
        }
    }
    if different {
        for (b, individual) in individuals.iter().enumerate() {
            let probe = format!("{ns}not{b}");
            out.push_str(&format!(
                "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectComplementOf(ObjectOneOf({individual})))\n"
            ));
            probes.insert(probe, Probe::Not(b));
        }
    }
    let probes = AboxProbes {
        probes,
        roles: roles.iter().map(|r| public_name(r)).collect(),
        individuals: individuals.iter().map(|a| public_name(a)).collect(),
        values,
        different,
    };
    (out, probes)
}

/// Remove the probes from the classification and read the rows off the
/// subsumptions `P_a ⊑ probe`. `individual_of` maps the realization probe
/// class of each individual to its public name.
pub(super) fn split(
    extended: &mut Classification,
    probes: &AboxProbes,
    individual_of: &BTreeMap<String, String>,
) -> Result<AboxRows, OrchestrateError> {
    let probe = |name: &str| probes.probes.get(name).copied();
    let unsatisfiable: Vec<Probe> = extended.unsatisfiable.iter().filter_map(|n| probe(n)).collect();
    extended.unsatisfiable.retain(|name| probe(name).is_none());
    let mut values = BTreeSet::new();
    let mut different = BTreeSet::new();
    extended.subsumptions.retain(|[low, high]| {
        let (low_probe, high_probe) = (probe(low), probe(high));
        if low_probe.is_none() && high_probe.is_none() {
            return true;
        }
        if let (Some(a), Some(p)) = (individual_of.get(low), high_probe) {
            match p {
                Probe::Value(r, b) => {
                    values.insert([probes.roles[r].clone(), a.clone(), probes.individuals[b].clone()]);
                }
                Probe::Not(b) => {
                    let b = &probes.individuals[b];
                    if a != b {
                        let (x, y) = if a < b { (a, b) } else { (b, a) };
                        different.insert([x.clone(), y.clone()]);
                    }
                }
            }
        }
        false
    });
    if extended.consistent && unsatisfiable.iter().any(|p| matches!(p, Probe::Not(_))) {
        // `¬{b}` is unsatisfiable only when the domain is `{b}`; then no
        // other individual is different from `b`, and the rows above are
        // already right. Nothing to report.
    }
    Ok(AboxRows {
        values: probes.values.then(|| values.into_iter().collect()),
        different: probes.different.then(|| different.into_iter().collect()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abox_rows_extension_retains_merged_targets_on_adv_ofn() {
        let _test_env = crate::test_env::read();
        let adv = std::fs::read_to_string(
            "/mnt/data1/leechuck/km-work/v170/scratch/review/e9/adv.ofn",
        )
        .unwrap_or_else(|_| {
            include_str!("../../src/frontend/named_role_bound.rs")
                .split("const ADV_OFN: &str = r#\"")
                .nth(1)
                .unwrap()
                .split("\"#;")
                .next()
                .unwrap()
                .to_owned()
        });
        let (canon, individuals) = super::super::realize::canonical_individuals(&adv).unwrap();
        let roles = super::super::properties::canonical_properties(&canon).unwrap();
        let (_ext, abox_probes) = extension(&canon, &roles, &individuals, true, false);
        let has_probe_for = |role_iri: &str, ind_iri: &str| -> bool {
            let r_idx = abox_probes.roles.iter().position(|r| r == role_iri).unwrap();
            let b_idx = abox_probes
                .individuals
                .iter()
                .position(|i| i == ind_iri)
                .unwrap();
            abox_probes
                .probes
                .values()
                .any(|&p| p == Probe::Value(r_idx, b_idx))
        };
        assert!(has_probe_for(":s6", ":c6"));
        assert!(has_probe_for(":s12", ":c12"));
        assert!(has_probe_for(":t14", ":b14"));
        assert!(has_probe_for(":r10", ":a10"));
        assert!(!has_probe_for(":s6", ":z0"));
    }

    #[test]
    fn abox_rows_extension_retains_targets_across_16_adversarial_cases() {
        let _test_env = crate::test_env::read();
        let mut pad = String::new();
        for i in 0..8 {
            pad.push_str(&format!("Declaration(ObjectProperty(:pad{i}))\n"));
        }
        for i in 0..40 {
            pad.push_str(&format!("Declaration(NamedIndividual(:z{i}))\n"));
        }
        let cases: &[(&str, &str, &[&str])] = &[
            (
                "functional_role_chain_merge",
                r#"Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2))
                   Declaration(ObjectProperty(:f3)) Declaration(ObjectProperty(:other))
                   FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2) FunctionalObjectProperty(:f3)
                   ObjectPropertyAssertion(:f1 :a :b1) ObjectPropertyAssertion(:f1 :a :b2)
                   ObjectPropertyAssertion(:f2 :b1 :c1) ObjectPropertyAssertion(:f2 :b2 :c2)
                   ObjectPropertyAssertion(:f3 :c1 :d1) ObjectPropertyAssertion(:f3 :c2 :d2)
                   ObjectPropertyAssertion(:other :x :d1)"#,
                &[":d1", ":d2"],
            ),
            (
                "functional_chain_with_has_value_merge",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2)) Declaration(ObjectProperty(:other))
                   FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2)
                   ObjectPropertyAssertion(:f1 :a :b1)
                   SubClassOf(:A ObjectHasValue(:f1 :b2)) ClassAssertion(:A :a)
                   ObjectPropertyAssertion(:f2 :b1 :c1) ObjectPropertyAssertion(:f2 :b2 :c2)
                   ObjectPropertyAssertion(:other :x :c1)"#,
                &[":c1", ":c2"],
            ),
            (
                "asserted_target_with_has_value_under_inverse",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                   ObjectPropertyAssertion(:s :b :a)
                   SubClassOf(:A ObjectHasValue(:r :c)) ClassAssertion(:A :a)
                   ObjectPropertyAssertion(:other :d :b)"#,
                &[":b", ":c"],
            ),
            (
                "asserted_target_with_inverse_of_has_value",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                   ObjectPropertyAssertion(:r :a :b)
                   SubClassOf(:A ObjectHasValue(ObjectInverseOf(:s) :c)) ClassAssertion(:A :a)
                   ObjectPropertyAssertion(:other :d :b)"#,
                &[":b", ":c"],
            ),
            (
                "inverse_has_value_source_merge",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:d))
                   InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                   ObjectPropertyAssertion(:r :a :b)
                   SubClassOf(:A ObjectHasValue(:s :a)) ClassAssertion(:A :c)
                   ObjectPropertyAssertion(:other :d :b)"#,
                &[":b", ":c"],
            ),
            (
                "max_cardinality_1_on_inverse_role",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   SubClassOf(:A ObjectMaxCardinality(1 ObjectInverseOf(:r)))
                   ClassAssertion(:A :x)
                   ObjectPropertyAssertion(:r :a :x) ObjectPropertyAssertion(:r :b :x)
                   ObjectPropertyAssertion(:other :d :a)"#,
                &[":a", ":b"],
            ),
            (
                "exact_cardinality_1_on_inverse_role_with_has_value",
                r#"Declaration(Class(:A)) Declaration(Class(:B))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:x))
                   SubClassOf(:A ObjectExactCardinality(1 ObjectInverseOf(:r)))
                   ClassAssertion(:A :x)
                   ObjectPropertyAssertion(:r :a :x)
                   SubClassOf(:B ObjectHasValue(:r :x)) ClassAssertion(:B :b)
                   ObjectPropertyAssertion(:other :d :a)"#,
                &[":a", ":b"],
            ),
            (
                "merge_feeding_property_chain",
                r#"Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:r1))
                   Declaration(ObjectProperty(:r2)) Declaration(ObjectProperty(:other))
                   FunctionalObjectProperty(:f)
                   ObjectPropertyAssertion(:f :x :b1) ObjectPropertyAssertion(:f :x :b2)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   ObjectPropertyAssertion(:r1 :a :b1) ObjectPropertyAssertion(:r2 :b2 :c)"#,
                &[":c"],
            ),
            (
                "two_merges_feeding_property_chain",
                r#"Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2))
                   Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:other))
                   FunctionalObjectProperty(:f1) InverseFunctionalObjectProperty(:f2)
                   ObjectPropertyAssertion(:f1 :u :b1) ObjectPropertyAssertion(:f1 :u :b2)
                   ObjectPropertyAssertion(:f2 :c1 :v) ObjectPropertyAssertion(:f2 :c2 :v)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   ObjectPropertyAssertion(:r1 :a :b1)
                   ObjectPropertyAssertion(:r2 :b2 :c1)"#,
                &[":c1", ":c2"],
            ),
            (
                "reflexive_and_has_self_in_chain_and_merge",
                r#"Declaration(Class(:B))
                   Declaration(ObjectProperty(:refl)) Declaration(ObjectProperty(:s))
                   Declaration(ObjectProperty(:fself)) Declaration(ObjectProperty(:other))
                   ReflexiveObjectProperty(:refl)
                   SubObjectPropertyOf(ObjectPropertyChain(:refl :s) :other)
                   ObjectPropertyAssertion(:s :a :b)
                   FunctionalObjectProperty(:fself)
                   SubClassOf(:B ObjectHasSelf(:fself)) ClassAssertion(:B :m1)
                   ObjectPropertyAssertion(:fself :m1 :m2)
                   ObjectPropertyAssertion(:other :d :m1)"#,
                &[":b", ":m1", ":m2"],
            ),
            (
                "symmetric_and_transitive_with_merge",
                r#"Declaration(ObjectProperty(:sym)) Declaration(ObjectProperty(:other))
                   Declaration(ObjectProperty(:f))
                   SymmetricObjectProperty(:sym) TransitiveObjectProperty(:other)
                   SubObjectPropertyOf(:sym :other) FunctionalObjectProperty(:f)
                   ObjectPropertyAssertion(:sym :b1 :a)
                   ObjectPropertyAssertion(:f :x :b1) ObjectPropertyAssertion(:f :x :b2)
                   ObjectPropertyAssertion(:other :b2 :c)"#,
                &[":a", ":b1", ":b2", ":c"],
            ),
            (
                "symmetric_with_has_value",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   SymmetricObjectProperty(:other)
                   SubClassOf(:A ObjectHasValue(:other :b)) ClassAssertion(:A :a)"#,
                &[":a", ":b"],
            ),
            (
                "equivalent_properties_with_inverses_and_merge",
                r#"Declaration(ObjectProperty(:p1)) Declaration(ObjectProperty(:p2))
                   Declaration(ObjectProperty(:p3)) Declaration(ObjectProperty(:other))
                   EquivalentObjectProperties(:p1 :p2)
                   InverseObjectProperties(:p2 :p3)
                   FunctionalObjectProperty(:p2)
                   ObjectPropertyAssertion(:p1 :a :b1)
                   ObjectPropertyAssertion(:p3 :b2 :a)
                   ObjectPropertyAssertion(:other :d :b1)"#,
                &[":b1", ":b2"],
            ),
            (
                "role_hierarchy_with_inverses_and_has_value",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))
                   Declaration(ObjectProperty(:t)) Declaration(ObjectProperty(:other))
                   SubObjectPropertyOf(:r ObjectInverseOf(:s))
                   SubObjectPropertyOf(ObjectInverseOf(:s) :t)
                   SubClassOf(:A ObjectHasValue(:r :b)) ClassAssertion(:A :a)
                   FunctionalObjectProperty(:t)
                   ObjectPropertyAssertion(:t :a :c)
                   ObjectPropertyAssertion(:other :d :b)"#,
                &[":b", ":c"],
            ),
            (
                "same_individual_chain_of_length_4",
                r#"Declaration(ObjectProperty(:other))
                   SameIndividual(:i1 :i2)
                   SameIndividual(:i2 :i3)
                   SameIndividual(:i3 :i4)
                   SameIndividual(:i4 :i5)
                   ObjectPropertyAssertion(:other :src :i1)"#,
                &[":i1", ":i2", ":i3", ":i4", ":i5"],
            ),
            (
                "nary_chain_with_has_value_and_same_individual",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:r3)) Declaration(ObjectProperty(:f))
                   Declaration(ObjectProperty(:other))
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2 :r3) :other)
                   SubClassOf(:A ObjectHasValue(:r1 :b1)) ClassAssertion(:A :a)
                   SameIndividual(:b1 :b2)
                   ObjectPropertyAssertion(:r2 :b2 :c1)
                   FunctionalObjectProperty(:f)
                   ObjectPropertyAssertion(:f :u :c1) ObjectPropertyAssertion(:f :u :c2)
                   ObjectPropertyAssertion(:r3 :c2 :d)"#,
                &[":d"],
            ),
            (
                "subproperty_of_functional_feeding_chain",
                r#"Declaration(ObjectProperty(:subf)) Declaration(ObjectProperty(:f))
                   Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:other))
                   SubObjectPropertyOf(:subf :f)
                   FunctionalObjectProperty(:f)
                   ObjectPropertyAssertion(:subf :u :b1) ObjectPropertyAssertion(:subf :u :b2)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   ObjectPropertyAssertion(:r1 :a :b1) ObjectPropertyAssertion(:r2 :b2 :c)"#,
                &[":c"],
            ),
        ];

        for (name, body, expected) in cases {
            let doc = format!("Prefix(:=<http://ex.org/>)\nOntology(<http://ex.org/{name}>\n{pad}{body}\n)");
            let (canon, individuals) = super::super::realize::canonical_individuals(&doc).unwrap();
            let roles = super::super::properties::canonical_properties(&canon).unwrap();
            assert!(roles.len() * individuals.len() >= 256);
            let (_ext, abox_probes) = extension(&canon, &roles, &individuals, true, false);
            let r_idx = abox_probes.roles.iter().position(|r| r == ":other").unwrap();
            for &exp in *expected {
                let b_idx = abox_probes.individuals.iter().position(|i| i == exp).unwrap();
                assert!(
                    abox_probes.probes.values().any(|&p| p == Probe::Value(r_idx, b_idx)),
                    "case {name}: missing probe for (:other, {exp})"
                );
            }
        }
    }
}
