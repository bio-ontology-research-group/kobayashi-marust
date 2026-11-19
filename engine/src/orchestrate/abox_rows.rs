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

    #[test]
    fn abox_rows_extension_retains_targets_on_c4_c6_and_20_anonymous_routing_cases() {
        let _test_env = crate::test_env::read();
        let mut pad = String::new();
        for i in 0..10 {
            pad.push_str(&format!("Declaration(ObjectProperty(:pad{i}))\n"));
        }
        for i in 0..30 {
            pad.push_str(&format!("Declaration(NamedIndividual(:z{i}))\n"));
        }
        let cases: &[(&str, &str, &str, &[&str])] = &[
            (
                "c4_inv_func_anon_succ_inv_has_value",
                r#"Declaration(Class(:X4))
                   Declaration(ObjectProperty(:r4)) Declaration(ObjectProperty(:t4)) Declaration(ObjectProperty(:u4))
                   Declaration(NamedIndividual(:d4)) Declaration(NamedIndividual(:e4))
                   Declaration(NamedIndividual(:k4)) Declaration(NamedIndividual(:m4))
                   InverseFunctionalObjectProperty(:r4)
                   ClassAssertion(ObjectSomeValuesFrom(:r4 :X4) :d4)
                   SubClassOf(:X4 ObjectHasValue(ObjectInverseOf(:r4) :e4))
                   ObjectPropertyAssertion(:t4 :k4 :d4)
                   ObjectPropertyAssertion(:u4 :e4 :m4)"#,
                ":t4",
                &[":d4", ":e4"],
            ),
            (
                "c6_complement_min_cardinality_2_merge",
                r#"Declaration(ObjectProperty(:r6)) Declaration(ObjectProperty(:t6))
                   Declaration(NamedIndividual(:a6)) Declaration(NamedIndividual(:b6))
                   Declaration(NamedIndividual(:c6)) Declaration(NamedIndividual(:k6))
                   ClassAssertion(ObjectComplementOf(ObjectMinCardinality(2 :r6)) :a6)
                   ObjectPropertyAssertion(:r6 :a6 :b6)
                   ObjectPropertyAssertion(:r6 :a6 :c6)
                   ObjectPropertyAssertion(:t6 :k6 :b6)"#,
                ":t6",
                &[":b6", ":c6"],
            ),
            (
                "m01_inv_func_subrole_anon_succ_inv_has_value",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:sub_r)) Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   SubObjectPropertyOf(:sub_r :r)
                   InverseFunctionalObjectProperty(:r)
                   ClassAssertion(ObjectSomeValuesFrom(:sub_r :X) :d)
                   SubClassOf(:X ObjectHasValue(ObjectInverseOf(:r) :e))
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            (
                "m02_func_inv_existential_has_value",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f)
                   ClassAssertion(ObjectSomeValuesFrom(ObjectInverseOf(:f) :X) :d)
                   SubClassOf(:X ObjectHasValue(:f :e))
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            (
                "m03_named_inv_prop_existential_func_has_value",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:inv_f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f)
                   InverseObjectProperties(:f :inv_f)
                   ClassAssertion(ObjectSomeValuesFrom(:inv_f :X) :d)
                   SubClassOf(:X ObjectHasValue(:f :e))
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            (
                "m04_min_card_anon_succ_max_card_inv_merge",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   SubClassOf(:A ObjectMaxCardinality(1 ObjectInverseOf(:r)))
                   ClassAssertion(ObjectMinCardinality(1 :r ObjectIntersectionOf(:A ObjectHasValue(ObjectInverseOf(:r) :e))) :d)
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            (
                "m05_neg_min_card_2_inv_anon_merge",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   SubClassOf(:X ObjectComplementOf(ObjectMinCardinality(2 ObjectInverseOf(:r))))
                   SubClassOf(:X ObjectHasValue(ObjectInverseOf(:r) :e))
                   ClassAssertion(ObjectSomeValuesFrom(:r :X) :d)
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            (
                "m06_subrole_anon_merge_with_asserted_superrole_target",
                r#"Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   FunctionalObjectProperty(:f)
                   SubObjectPropertyOf(:other :f)
                   ObjectPropertyAssertion(:f :a :b)
                   ClassAssertion(ObjectSomeValuesFrom(:other owl:Thing) :a)"#,
                ":other",
                &[":b"],
            ),
            (
                "m07_subrole_anon_merge_cascading_to_inv_func",
                r#"Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f)
                   SubObjectPropertyOf(:r :f)
                   InverseFunctionalObjectProperty(:r)
                   ObjectPropertyAssertion(:f :b :c)
                   ObjectPropertyAssertion(:r :a :c)
                   ClassAssertion(ObjectSomeValuesFrom(:r owl:Thing) :b)
                   ObjectPropertyAssertion(:other :k :a)"#,
                ":other",
                &[":a", ":b"],
            ),
            (
                "m08_cascade_two_functional_roles_over_anon_witness",
                r#"Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:c1)) Declaration(NamedIndividual(:c2)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2)
                   ObjectPropertyAssertion(:f1 :a :b)
                   ClassAssertion(ObjectSomeValuesFrom(:f1 ObjectHasValue(:f2 :c1)) :a)
                   ObjectPropertyAssertion(:f2 :b :c2)
                   ObjectPropertyAssertion(:other :k :c1)"#,
                ":other",
                &[":c1", ":c2"],
            ),
            (
                "m09_cascade_three_level_anon_functional_chain",
                r#"Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2))
                   Declaration(ObjectProperty(:f3)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))
                   Declaration(NamedIndividual(:d1)) Declaration(NamedIndividual(:d2)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2) FunctionalObjectProperty(:f3)
                   ObjectPropertyAssertion(:f1 :a :b)
                   ObjectPropertyAssertion(:f2 :b :c)
                   ObjectPropertyAssertion(:f3 :c :d2)
                   ClassAssertion(ObjectSomeValuesFrom(:f1 ObjectSomeValuesFrom(:f2 ObjectHasValue(:f3 :d1))) :a)
                   ObjectPropertyAssertion(:other :k :d1)"#,
                ":other",
                &[":d1", ":d2"],
            ),
            (
                "m10_chain_over_two_anon_middle_elements_with_nested_has_value",
                r#"Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:r3)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:c))
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2 :r3) :other)
                   ClassAssertion(ObjectSomeValuesFrom(:r1 ObjectSomeValuesFrom(:r2 ObjectHasValue(:r3 :c))) :a)"#,
                ":other",
                &[":c"],
            ),
            (
                "m11_chain_over_anon_middle_via_named_inverse_existential",
                r#"Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   InverseObjectProperties(:r2 :s)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   ClassAssertion(ObjectSomeValuesFrom(:s ObjectHasValue(ObjectInverseOf(:r1) :a)) :b)"#,
                ":other",
                &[":b"],
            ),
            (
                "m12_chain_into_functional_merging_anon_leaf_with_named",
                r#"Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   SubObjectPropertyOf(:r2 :f)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   FunctionalObjectProperty(:f)
                   ClassAssertion(ObjectSomeValuesFrom(:r1 ObjectIntersectionOf(ObjectSomeValuesFrom(:r2 owl:Thing) ObjectHasValue(:f :b))) :a)"#,
                ":other",
                &[":b"],
            ),
            (
                "m13_chain_into_functional_cascading_to_inv_func_merge",
                r#"Declaration(Class(:X1)) Declaration(Class(:X2))
                   Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:f_sub1))
                   Declaration(ObjectProperty(:f_sub2)) Declaration(ObjectProperty(:g)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:k)) Declaration(NamedIndividual(:m))
                   FunctionalObjectProperty(:f)
                   SubObjectPropertyOf(:f_sub1 :f)
                   SubObjectPropertyOf(:f_sub2 :f)
                   InverseFunctionalObjectProperty(:g)
                   SubClassOf(:X1 ObjectHasValue(ObjectInverseOf(:f_sub1) :k))
                   SubClassOf(:X2 ObjectHasValue(ObjectInverseOf(:f_sub2) :k))
                   ClassAssertion(ObjectSomeValuesFrom(:g :X1) :a)
                   ClassAssertion(ObjectSomeValuesFrom(:g :X2) :b)
                   ObjectPropertyAssertion(:other :m :a)"#,
                ":other",
                &[":a", ":b"],
            ),
            (
                "m14_anon_witness_merged_by_inv_func_feeds_chain_middle",
                r#"Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:r3)) Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:c))
                   Declaration(NamedIndividual(:k)) Declaration(NamedIndividual(:m))
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2 :r3) :other)
                   InverseFunctionalObjectProperty(:f)
                   ClassAssertion(ObjectSomeValuesFrom(:r1 ObjectSomeValuesFrom(:r2 ObjectHasValue(:f :k))) :a)
                   ObjectPropertyAssertion(:f :m :k)
                   ObjectPropertyAssertion(:r3 :m :c)"#,
                ":other",
                &[":c"],
            ),
            (
                "m15_tree_folding_across_two_functional_subroles",
                r#"Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:r1))
                   Declaration(ObjectProperty(:r2)) Declaration(ObjectProperty(:inv_r2)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a))
                   FunctionalObjectProperty(:f)
                   SubObjectPropertyOf(:r1 :f)
                   SubObjectPropertyOf(:r2 :f)
                   InverseObjectProperties(:r2 :inv_r2)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :inv_r2) :other)
                   ClassAssertion(ObjectIntersectionOf(ObjectSomeValuesFrom(:r1 owl:Thing) ObjectSomeValuesFrom(:r2 owl:Thing)) :a)"#,
                ":other",
                &[":a"],
            ),
            (
                "m16_inv_func_parent_merge_in_anon_tree_self_loop",
                r#"Declaration(ObjectProperty(:g)) Declaration(ObjectProperty(:f1))
                   Declaration(ObjectProperty(:f2)) Declaration(ObjectProperty(:inv_f2)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a))
                   InverseFunctionalObjectProperty(:g)
                   SubObjectPropertyOf(:f1 :g)
                   SubObjectPropertyOf(:f2 :g)
                   InverseObjectProperties(:f2 :inv_f2)
                   SubObjectPropertyOf(ObjectPropertyChain(:f1 :inv_f2) :other)
                   ClassAssertion(ObjectSomeValuesFrom(:f1 ObjectSomeValuesFrom(:inv_f2 owl:Thing)) :a)"#,
                ":other",
                &[":a"],
            ),
            (
                "m17_symmetric_func_anon_succ_has_value_merge",
                r#"Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   SymmetricObjectProperty(:r)
                   FunctionalObjectProperty(:r)
                   ClassAssertion(ObjectSomeValuesFrom(:r ObjectHasValue(:r :e)) :d)
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            (
                "m18_transitive_role_over_two_anon_steps_and_func_merge",
                r#"Declaration(ObjectProperty(:other)) Declaration(ObjectProperty(:f))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:k))
                   TransitiveObjectProperty(:other)
                   FunctionalObjectProperty(:f)
                   ClassAssertion(ObjectSomeValuesFrom(:other ObjectSomeValuesFrom(:other ObjectHasValue(ObjectInverseOf(:f) :k))) :a)
                   ObjectPropertyAssertion(:f :k :b)
                   ObjectPropertyAssertion(:other :b :c)"#,
                ":other",
                &[":b", ":c"],
            ),
            (
                "m19_anon_has_self_on_inv_func_subrole_self_loop_and_merge",
                r#"Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:k))
                   InverseFunctionalObjectProperty(:r)
                   SubObjectPropertyOf(:s :r)
                   ClassAssertion(ObjectSomeValuesFrom(:r ObjectHasSelf(:s)) :a)
                   ObjectPropertyAssertion(:r :b :a)
                   ObjectPropertyAssertion(:other :k :a)"#,
                ":other",
                &[":a", ":b"],
            ),
            (
                "m20_neg_all_values_anon_witness_with_nested_has_value_merge",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   InverseFunctionalObjectProperty(:r)
                   SubClassOf(:X ObjectHasValue(ObjectInverseOf(:r) :e))
                   ClassAssertion(ObjectComplementOf(ObjectAllValuesFrom(:r ObjectComplementOf(:X))) :d)
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
        ];

        for (name, body, role, expected) in cases {
            let doc = format!("Prefix(:=<http://ex.org/>)\nOntology(<http://ex.org/{name}>\n{pad}{body}\n)");
            let (canon, individuals) = super::super::realize::canonical_individuals(&doc).unwrap();
            let roles = super::super::properties::canonical_properties(&canon).unwrap();
            assert!(roles.len() * individuals.len() >= 256);
            let (_ext, abox_probes) = extension(&canon, &roles, &individuals, true, false);
            let r_idx = abox_probes.roles.iter().position(|r| r == role).unwrap();
            for &exp in *expected {
                let b_idx = abox_probes.individuals.iter().position(|i| i == exp).unwrap();
                assert!(
                    abox_probes.probes.values().any(|&p| p == Probe::Value(r_idx, b_idx)),
                    "case {name}: missing probe for ({role}, {exp})"
                );
            }
        }
    }
}
