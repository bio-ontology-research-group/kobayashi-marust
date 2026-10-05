//! Checked symbolic bounds are consumed only by the native source bridge.
//! Ordinary CB/EL workers never receive this representation.
use super::{Classification, ClassificationEvidence, OrchestrateError};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::Path;

/// A scheduling hint only: semantic admission still uses the complete typed
/// source handoff. Bound the extra source read on the ordinary fast paths.
pub(super) fn automatic_candidate(path: &Path) -> Result<Option<String>, OrchestrateError> {
    if std::fs::metadata(path)?.len() > 64 * 1024 * 1024 { return Ok(None); }
    let text = std::fs::read_to_string(path)?;
    if high_object_cardinality_without_rules(&text) { Ok(Some(text)) } else { Ok(None) }
}

fn high_object_cardinality_without_rules(text: &str) -> bool {
    let mut tokens = crate::frontend::sexpr::tokens(text).peekable();
    let mut high = false;
    while let Some(token) = tokens.next() {
        if token == "DLSafeRule" && tokens.peek() == Some(&"(") { return false; }
        if matches!(token, "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality")
            && tokens.peek() == Some(&"(") {
            tokens.next();
            if let Some(bound) = tokens.next() {
                high |= bound.parse::<u64>().map_or(false, |n| n >= 128);
            }
        }
    }
    high
}

pub(super) fn classify(path: &Path) -> Result<ClassificationEvidence, OrchestrateError> {
    classify_text(std::fs::read_to_string(path)?)
}

pub(super) fn classify_text(text: String) -> Result<ClassificationEvidence, OrchestrateError> {
    if crate::tableau::ht_lean_certification_requested() {
        return Err(OrchestrateError::OutOfFragment(
            "symbolic source bridge cannot bypass requested HT runtime certification".into()));
    }
    if std::env::var_os("KM_TRIGGER_ABSORB").is_none() {
        std::env::set_var("KM_TRIGGER_ABSORB", "1");
    }
    let frontend = crate::frontend::ofn_to_symbolic_frontend(&text)
        .map_err(|error| OrchestrateError::OutOfFragment(error.0))?;
    drop(text);
    let input = frontend.source_bridge_input().map_err(OrchestrateError::OutOfFragment)?;
    let source = frontend.evidence();
    let names: HashSet<String> = source.named.iter().cloned().collect();
    let iris = source.iri_map.clone();
    let asserted = source.asserted_classes.clone();
    let inconsistent = source.abox_inconsistent;
    if names.iter().any(|name| !iris.contains_key(name)) {
        return Err(OrchestrateError::OutOfFragment("symbolic source lacks a public class IRI".into()));
    }
    // The native input owns the complete source evidence now. Do not retain
    // the large frontend clause representation beside the completion graph.
    drop(frontend);
    crate::mem::release_transient_heap();
    let output = crate::tableau::run_bridge_producer_input_typed(input)
        .map_err(|error| OrchestrateError::OutOfFragment(format!("symbolic source bridge deferred ({error})")))?;
    Ok(ClassificationEvidence {
        classification: map_output(output, &names, &iris, &asserted, inconsistent),
        grouped_subsumptions: None,
        consistency_certified: true,
    })
}

fn map_output(output: crate::tableau::TOutput, names: &HashSet<String>,
    iris: &BTreeMap<String, String>, asserted: &[String], frontend_inconsistent: bool) -> Classification {
    let full = |name: &str| iris.get(name).cloned().unwrap_or_else(|| name.to_owned());
    let mut unsatisfiable: BTreeSet<String> = output.unsatisfiable.iter().map(|name| full(name)).collect();
    let mut pairs = BTreeSet::new();
    for [left, right] in output.subsumptions {
        if super::is_bottom(&full(&right)) { unsatisfiable.insert(full(&left)); }
        else if names.contains(&left) && names.contains(&right) && left != right {
            pairs.insert([full(&left), full(&right)]);
        }
    }
    let consistent = output.consistent && !frontend_inconsistent
        && !asserted.iter().any(|name| unsatisfiable.contains(&full(name)));
    if !consistent {
        return Classification { consistent: false, subsumptions: vec![], unsatisfiable: vec![], dropped: 0 };
    }
    let public: HashSet<String> = names.iter().map(|name| full(name)).collect();
    Classification { consistent, subsumptions: pairs.into_iter().collect(),
        unsatisfiable: unsatisfiable.into_iter().filter(|name| public.contains(name)).collect(), dropped: 0 }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn automatic_hint_uses_constructor_tokens_and_excludes_rule_sources() {
        for construct in ["ObjectMinCardinality", "ObjectMaxCardinality", "ObjectExactCardinality"] {
            assert!(high_object_cardinality_without_rules(&format!("{construct} ( # bound\n128 :r :F)")));
            assert!(!high_object_cardinality_without_rules(&format!("{construct}(127 :r :F)")));
        }
        for text in [r#"Annotation(:p "ObjectMinCardinality(999 :r)")"#,
            "Declaration(Class(<urn:ObjectMinCardinality(999)>))",
            "# ObjectMinCardinality(999 :r)\nOntology()",
            "DataMinCardinality(999 :r)",
            "ObjectMinCardinality(128 :r) DLSafeRule(Body() Head())",
            "DLSafeRule(Body() Head()) ObjectMinCardinality(128 :r)"] {
            assert!(!high_object_cardinality_without_rules(text), "{text}");
        }
    }

    #[test]
    fn symbolic_publication_retains_public_iris_and_global_clashes() {
        let names = HashSet::from(["Q_public".into(), "B".into()]);
        let iris = BTreeMap::from([("Q_public".into(), "urn:A".into()), ("B".into(), "urn:B".into())]);
        let output = || crate::tableau::TOutput { consistent: true,
            subsumptions: vec![["Q_public".into(), "B".into()], ["Q_public".into(), "__aux".into()]],
            unsatisfiable: vec!["B".into(), "__aux".into()] };
        let result = map_output(output(), &names, &iris, &[], false);
        assert_eq!(result.subsumptions, vec![["urn:A".to_owned(), "urn:B".to_owned()]]);
        assert_eq!(result.unsatisfiable, vec!["urn:B"]);
        for result in [map_output(output(), &names, &iris, &["B".into()], false),
            map_output(output(), &names, &iris, &[], true)] {
            assert!(!result.consistent);
            assert!(result.subsumptions.is_empty() && result.unsatisfiable.is_empty());
        }
    }
}
