//! Schedule exact source reductions before the nominal CB fallback.
use std::path::Path;
use super::OrchestrateError;

pub(super) fn automatic_candidate(path: &Path) -> Result<Option<&'static str>, OrchestrateError> {
    if std::fs::metadata(path)?.len() > 4 * 1024 * 1024 { return Ok(None); }
    let text = std::fs::read_to_string(path)?;
    Ok(plan(&text))
}

fn plan(text: &str) -> Option<&'static str> {
    // This is a cost bound, not semantic admission. The reducers below and
    // native bridge independently check complete source coverage.
    let mut builder = crate::frontend::profile::SourceProfileBuilder::new();
    crate::frontend::parse::for_each_ontology_child(text, |node| {
        builder.observe(node); Ok(())
    }).ok()?;
    let source = builder.finish(text.len() as u64).source;
    let count = |kind: &str| source.axiom_types.get(kind).copied().unwrap_or(0);
    let bounded = source.distinct_classes <= 512 && source.distinct_individuals <= 512
        && source.logical_axioms <= 4_000 && source.imports == 0;
    // Equality now has a native nominal representation. Finite data ranges
    // still require complete cover/value evidence in the converted-input gate.
    let finite_identity = source.rule_axioms == 0 && count("SameIndividual") > 0
        && count("DataPropertyAssertion") == 0 && count("NegativeDataPropertyAssertion") == 0
        && count("DataPropertyRange") > 0
        && crate::frontend::sexpr::tokens(text).any(|token| token == "DataOneOf");
    // The frontend must independently certify an empty DL-safe named domain.
    // Raw profiling may flag datatype rule atoms; only the frontend can prove
    // their vacuity. This hint neither removes rules nor authorizes publication.
    let empty_named_rules = source.rule_axioms > 0 && source.distinct_individuals == 0
        && source.abox_axioms == 0 && source.role_chain_axioms > 0
        && source.distinct_data_properties > 0;
    if bounded && (finite_identity || empty_named_rules) { return Some("native"); }
    if source.rule_axioms > 0 {
        // Exact compilation verifies every source rule and retains non-rule
        // axioms. This hint only schedules an attempt: the native bridge must
        // independently accept the complete transformed source before output.
        // Raw profile support is conservative (for example, an empty-head
        // constraint). The compiler's source/parsed coverage check is the
        // authoritative admission test for this reduction.
        return (source.imports == 0
            && crate::frontend::ground_rule_source::compile(text, 100_000).is_ok())
            .then_some("KM_GROUND_RULE_SOURCE");
    }
    // Functional numeric profiles need the exact source path even without
    // inverse-functional object roles. A successful bounded compiler is only
    // a scheduling hint; native admission still validates its complete output.
    if bounded && (count("DataPropertyAssertion") > 0
        || count("NegativeDataPropertyAssertion") > 0)
        && crate::frontend::numeric_source::normalize(text, 256).ok().flatten().is_some()
        && crate::frontend::ground_rule_source::compile(text, 100_000).is_ok() {
        return Some("KM_GROUND_RULE_SOURCE");
    }
    if !(1..=256).contains(&count("DataPropertyAssertion"))
        || count("FunctionalDataProperty") == 0
        || source.inverse_functional_role_axioms == 0
        || source.distinct_classes > 512 || source.distinct_individuals > 512
        || source.logical_axioms > 4_000 || source.imports != 0
        || source.rule_axioms != 0 || source.unsupported_rule_axioms != 0 {
        return None;
    }
    if crate::frontend::data_abox_projection::project(text).is_ok() {
        Some("KM_DATA_ABOX_PROJECT")
    } else if crate::frontend::ground_rule_source::compile(text, 100_000).is_ok() {
        Some("KM_GROUND_RULE_SOURCE")
    } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;
    const SOURCE: &str = r#"Ontology(Declaration(Class(<urn:C>))
        InverseFunctionalObjectProperty(<urn:r>) FunctionalDataProperty(<urn:p>)
        DataPropertyAssertion(<urn:p> <urn:a> "red"^^xsd:string))"#;
    #[test]
    fn scheduling_requires_complete_reduction_and_preserves_rule_fences() {
        assert_eq!(plan(SOURCE), Some("KM_DATA_ABOX_PROJECT"));
        let coupled = SOURCE.replacen("Ontology(",
            "Ontology(SubClassOf(<urn:C> DataSomeValuesFrom(<urn:p> xsd:string)) ", 1);
        assert_eq!(plan(&coupled), Some("KM_GROUND_RULE_SOURCE"));
        for extra in ["Import(<urn:missing>)", "DLSafeRule(Body(UnknownAtom()) Head())"] {
            assert_eq!(plan(&SOURCE.replacen("Ontology(", &format!("Ontology({extra} "), 1)), None);
        }
        assert_eq!(plan(&SOURCE.replace("xsd:string", "<urn:unknown>")), None);
        assert_eq!(plan(&SOURCE.replace("InverseFunctionalObjectProperty(<urn:r>)", "")), None);
    }
    #[test]
    fn automatic_rules_require_exact_complete_source_compilation() {
        let source = r#"Ontology(Declaration(NamedIndividual(<urn:a>))
            DLSafeRule(Body(ClassAtom(<urn:A> Variable(<urn:x>)))
                Head(ClassAtom(<urn:B> Variable(<urn:x>)))))"#;
        assert_eq!(plan(source), Some("KM_GROUND_RULE_SOURCE"));
        assert_eq!(plan(&source.replace("Ontology(","Ontology(Import(<urn:missing>)")), None);
        assert_eq!(plan(&source.replace("ClassAtom(<urn:A>","UnknownAtom(<urn:A>")), None);
        assert_eq!(plan("Ontology(DLSafeRule(Body() Head()))"), Some("KM_GROUND_RULE_SOURCE"));
    }

    #[test]
    fn numeric_profiles_schedule_without_inverse_functional_object_roles() {
        let source = r#"Prefix(:=<urn:test:>) Ontology(
            FunctionalDataProperty(:p)
            EquivalentClasses(:A DataSomeValuesFrom(:p
                DatatypeRestriction(xsd:integer xsd:minExclusive "3"^^xsd:integer)))
            DataPropertyAssertion(:p :a "3"^^xsd:integer)
            ClassAssertion(:A :a))"#;
        assert_eq!(plan(source), Some("KM_GROUND_RULE_SOURCE"));
        assert_eq!(plan(&source.replace("FunctionalDataProperty(:p)", "")), None);
        assert_eq!(plan(&source.replace("Ontology(",
            "Ontology(SubDataPropertyOf(:p :q) ")), None);
    }

}
