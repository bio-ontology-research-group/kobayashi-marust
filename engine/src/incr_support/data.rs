//! Small direct datatype-clash support proposals, never publication certificates.
//! The caller must independently classify the proposed original source subset.

use crate::frontend::data_abox::DataAbox;
use crate::frontend::sexpr::{tokens, Node, Parser};
use crate::fxhash::FxHashMap;
use crate::source_locality::Scan;

// At most this many representatives are compared per key. Overflow only loses
// proposals; it cannot authorize reuse. This avoids quadratic assertion pairs.
const REPRESENTATIVES: usize = 8;
const MAX_NODE_BYTES: usize = 32_768;
const MAX_LISTS: usize = 256;

struct Axiom<'a> {
    hash: u128,
    node: Node<'a>,
}

fn inconsistent<'a>(axioms: &[Axiom<'a>], selected: &[usize]) -> bool {
    let mut data = DataAbox::default();
    for &id in selected {
        data.observe(&axioms[id].node);
    }
    data.is_inconsistent()
}

fn support(axioms: &[Axiom<'_>], selected: &[usize]) -> Vec<u128> {
    let mut ids = selected.to_vec();
    ids.sort_unstable();
    ids.dedup();
    ids.into_iter().map(|id| axioms[id].hash).collect()
}

/// Propose one direct functionality or atomic-range clash using existing
/// `DataAbox` semantics. Exact token keys intentionally miss differently
/// spelled aliases, inherited constraints, equality merges and complex ranges.
/// Annotated or unsupported forms are skipped. No datatype semantics are
/// implemented here, and a proposal is not an inconsistency certificate.
pub(super) fn propose(text: &str, scan: &Scan) -> Option<Vec<u128>> {
    // DataAbox recognizes standard datatype prefixes lexically. Do not treat
    // a user-rebound standard prefix as its conventional datatype namespace.
    if scan.prefixes.iter().any(|(prefix, iri)| match prefix.as_str() {
        "xsd:" => iri != "http://www.w3.org/2001/XMLSchema#",
        "rdf:" => iri != "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
        "rdfs:" => iri != "http://www.w3.org/2000/01/rdf-schema#",
        _ => false,
    }) {
        return None;
    }
    let mut axioms = Vec::new();
    for statement in &scan.statements {
        let Some(slice) = text.get(statement.start..statement.end) else { continue };
        // Optional proposals must not expose the legacy byte tokenizer to
        // unsupported Unicode boundaries or recurse through oversized nodes.
        if !slice.is_ascii() || slice.len() > MAX_NODE_BYTES
            || slice.bytes().filter(|b| *b == b'(').count() > MAX_LISTS { continue; }
        if !matches!(tokens(slice).next(), Some("FunctionalDataProperty" | "DataPropertyRange" | "DataPropertyAssertion")) {
            continue;
        }
        let Ok(node) = Parser::new(slice).parse() else { continue };
        axioms.push(Axiom { hash: statement.hash, node });
    }
    let mut functional = FxHashMap::default();
    let mut ranges: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
    let mut assertions = Vec::new();
    for (id, axiom) in axioms.iter().enumerate() {
        match &axiom.node {
            Node::List("FunctionalDataProperty", args) => {
                if let [Node::Atom(property)] = args.as_slice() {
                    functional.entry(*property).or_insert(id);
                }
            }
            Node::List("DataPropertyRange", args) => {
                // Atomic ranges only; annotations and compound dataranges
                // deliberately stay on the ordinary witness/fallback path.
                if let [Node::Atom(property), Node::Atom(_datatype)] = args.as_slice() {
                    let group = ranges.entry(*property).or_default();
                    if group.len() < REPRESENTATIVES { group.push(id); }
                }
            }
            Node::List("DataPropertyAssertion", args) => {
                let [Node::Atom(property), Node::Atom(owner), Node::Atom(literal), rest @ ..] = args.as_slice() else { continue };
                if !literal.starts_with('"') || rest.len() > 1 { continue; }
                if let Some(suffix) = rest.first() {
                    if !suffix.as_atom().is_some_and(|s| s.starts_with('@') || s.starts_with("^^")) { continue; }
                }
                assertions.push((*property, *owner, id));
            }
            _ => {}
        }
    }
    let mut representatives: FxHashMap<(&str, &str), Vec<usize>> = FxHashMap::default();
    for (property, owner, assertion) in assertions {
        if let Some(constraints) = ranges.get(property) {
            for &range in constraints {
                let selected = [range, assertion];
                if inconsistent(&axioms, &selected) { return Some(support(&axioms, &selected)); }
            }
        }
        if let Some(&constraint) = functional.get(property) {
            let previous = representatives.entry((property, owner)).or_default();
            for &other in previous.iter() {
                let selected = [constraint, other, assertion];
                if inconsistent(&axioms, &selected) { return Some(support(&axioms, &selected)); }
            }
            if previous.len() < REPRESENTATIVES { previous.push(assertion); }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_locality::{fingerprint, scan};

    fn proposal(body: &str) -> Option<Vec<u128>> {
        let text = format!("Prefix(:=<urn:direct-data#>) Ontology({body})");
        propose(&text, &scan(&text).unwrap())
    }

    #[test]
    fn functional_clash_uses_existing_value_semantics_and_original_hashes() {
        let statements = ["FunctionalDataProperty(:p)", "DataPropertyAssertion(:p :a \"one\")",
            "DataPropertyAssertion(:p :a \"two\")"];
        let hashes = proposal(&statements.join(" ")).unwrap();
        assert_eq!(hashes, statements.iter().map(|s| fingerprint(s.as_bytes())).collect::<Vec<_>>());
        // A repeated value, a different owner, or equal numeric values are
        // not a functionality clash; do not invent lexical inequality.
        for body in [
            "FunctionalDataProperty(:p) DataPropertyAssertion(:p :a \"one\") DataPropertyAssertion(:p :a \"one\")",
            "FunctionalDataProperty(:p) DataPropertyAssertion(:p :a \"one\") DataPropertyAssertion(:p :b \"two\")",
            "FunctionalDataProperty(:p) DataPropertyAssertion(:p :a \"01\"^^xsd:integer) DataPropertyAssertion(:p :a \"1\"^^xsd:int)",
        ] { assert!(proposal(body).is_none()); }
    }

    #[test]
    fn range_clash_preserves_exact_source_support() {
        let statements = ["DataPropertyAssertion(:p :a \"mail\"@en)", "DataPropertyRange(:p xsd:string)"];
        assert_eq!(proposal(&statements.join(" ")).unwrap(), statements.iter().map(|s| fingerprint(s.as_bytes())).collect::<Vec<_>>());
        assert!(proposal("DataPropertyRange(:p xsd:string) DataPropertyAssertion(:p :a \"mail\")").is_none());
        assert!(proposal("DataPropertyRange(:p <urn:unknown>) DataPropertyAssertion(:p :a \"mail\"@en)").is_none());
        assert!(proposal("FunctionalDataProperty(:p) DataPropertyAssertion(:p :a \"x\"^^<urn:unknown>) DataPropertyAssertion(:p :a \"y\"^^<urn:unknown>)").is_none());
    }

    #[test]
    fn aliases_conservatively_miss_and_rebound_datatype_prefixes_decline() {
        let text = "Prefix(:=<urn:x#>) Ontology(DataPropertyRange(:p xsd:string) DataPropertyAssertion(<urn:x#p> :a \"x\"@en))";
        assert!(propose(text, &scan(text).unwrap()).is_none());
        let text = "Prefix(xsd:=<urn:custom#>) Ontology(DataPropertyRange(<urn:p> xsd:string) DataPropertyAssertion(<urn:p> <urn:a> \"x\"@en))";
        assert!(propose(text, &scan(text).unwrap()).is_none());
        let text = "Prefix(t:=<http://www.w3.org/2001/XMLSchema#>) Ontology(DataPropertyRange(<urn:p> t:string) DataPropertyAssertion(<urn:p> <urn:a> \"x\"@en))";
        assert!(propose(text, &scan(text).unwrap()).is_none());
    }

    #[test]
    fn unsupported_unicode_and_oversized_nested_nodes_decline_before_parsing() {
        assert!(proposal("FunctionalDataProperty(:p) DataPropertyAssertion(:p :a \"Ġ\") DataPropertyAssertion(:p :a \"other\")").is_none());
        let range = format!("DataPropertyRange(:p {}xsd:string{})", "DataComplementOf(".repeat(MAX_LISTS + 1), ")".repeat(MAX_LISTS + 1));
        assert!(proposal(&format!("{range} DataPropertyAssertion(:p :a \"x\"@en)")).is_none());
        assert!(proposal(&format!("FunctionalDataProperty(:p) DataPropertyAssertion(:p :a \"{}\") DataPropertyAssertion(:p :a \"other\")", "x".repeat(MAX_NODE_BYTES))).is_none());
    }

    #[test]
    fn unsupported_annotated_and_compound_forms_do_not_contribute_support() {
        assert!(proposal("FunctionalDataProperty(Annotation(<urn:note> \"n\") :p) DataPropertyAssertion(:p :a \"x\") DataPropertyAssertion(:p :a \"y\")").is_none());
        assert!(proposal("DataPropertyRange(:p DataOneOf(\"x\")) DataPropertyAssertion(:p :a \"y\")").is_none());
    }
}
