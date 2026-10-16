//! Standard OWL syntax input adapter.
//!
//! KM's trusted frontend consumes OWL functional syntax. Other concrete
//! syntaxes are parsed into Horned-OWL's structural model and serialized back
//! to functional syntax before clausification. This keeps one normalization,
//! profiling, routing, and reasoning path for every accepted syntax.

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

use horned_owl::io::ParserConfiguration;
use horned_owl::model::{RcAnnotatedComponent, RcStr};
use horned_owl::ontology::component_mapped::ComponentMappedOntology;
use horned_owl::ontology::set::SetOntology;

use super::tmpfile::TempPath;
use super::OrchestrateError;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InputFormat {
    Functional,
    OwlXml,
    RdfXml,
    Turtle,
}

impl InputFormat {
    pub fn parse(value: &str) -> Result<Self, OrchestrateError> {
        match value.to_ascii_lowercase().as_str() {
            "ofn" | "functional" | "functional-syntax" => Ok(Self::Functional),
            "owx" | "owlxml" | "owl-xml" => Ok(Self::OwlXml),
            "rdf" | "rdfxml" | "rdf-xml" | "xml" => Ok(Self::RdfXml),
            "ttl" | "turtle" => Ok(Self::Turtle),
            other => Err(OrchestrateError::OutOfFragment(format!(
                "unknown OWL input format '{other}'; expected auto, functional, owlxml, rdfxml, or turtle"
            ))),
        }
    }
}

pub struct PreparedInput<'a> {
    original: &'a Path,
    converted: Option<TempPath>,
}

impl PreparedInput<'_> {
    pub fn path(&self) -> &Path {
        self.converted
            .as_ref()
            .map(TempPath::path)
            .unwrap_or(self.original)
    }
}

fn sniff(path: &Path) -> Result<InputFormat, OrchestrateError> {
    if let Ok(value) = std::env::var("KM_INPUT_FORMAT") {
        if !value.eq_ignore_ascii_case("auto") {
            return InputFormat::parse(&value);
        }
    }

    let mut reader = BufReader::new(File::open(path)?);
    let prefix = reader.fill_buf()?;
    let text = String::from_utf8_lossy(&prefix[..prefix.len().min(8192)]);
    let trimmed = text.trim_start_matches('\u{feff}').trim_start();

    if trimmed.starts_with("Prefix(") || trimmed.starts_with("Ontology(") {
        return Ok(InputFormat::Functional);
    }
    if trimmed.starts_with("@prefix")
        || trimmed.starts_with("@base")
        || trimmed.starts_with("PREFIX ")
        || trimmed.starts_with("BASE ")
    {
        return Ok(InputFormat::Turtle);
    }
    if trimmed.starts_with('<') {
        if trimmed.contains("http://www.w3.org/2002/07/owl#")
            && (trimmed.contains("<Ontology") || trimmed.contains(":Ontology"))
            && !trimmed.contains("rdf:RDF")
        {
            return Ok(InputFormat::OwlXml);
        }
        return Ok(InputFormat::RdfXml);
    }

    match path
        .extension()
        .and_then(|s| s.to_str())
        .unwrap_or_default()
    {
        "ofn" | "func" => Ok(InputFormat::Functional),
        "owx" => Ok(InputFormat::OwlXml),
        "ttl" => Ok(InputFormat::Turtle),
        "rdf" | "owl" | "xml" => Ok(InputFormat::RdfXml),
        _ => Err(OrchestrateError::OutOfFragment(
            "cannot detect OWL syntax; use --format functional|owlxml|rdfxml|turtle".into(),
        )),
    }
}

fn write_functional(
    ontology: &ComponentMappedOntology<RcStr, RcAnnotatedComponent>,
    mapping: Option<&horned_owl::curie::PrefixMapping>,
) -> Result<TempPath, OrchestrateError> {
    let output = TempPath::new(".input.ofn");
    let file = File::create(output.path())?;
    horned_owl::io::ofn::writer::write(file, ontology, mapping)
        .map_err(|error| OrchestrateError::OutOfFragment(format!("OWL serialization: {error}")))?;
    Ok(output)
}

fn prepare_with_format(
    path: &Path,
    format: InputFormat,
) -> Result<PreparedInput<'_>, OrchestrateError> {
    if format == InputFormat::Functional {
        return Ok(PreparedInput {
            original: path,
            converted: None,
        });
    }

    let file = File::open(path)?;
    let mut reader = BufReader::new(file);
    let converted = match format {
        InputFormat::OwlXml => {
            let (ontology, prefixes): (SetOntology<RcStr>, _) =
                horned_owl::io::owx::reader::read(&mut reader, ParserConfiguration::default())
                    .map_err(|error| {
                        OrchestrateError::OutOfFragment(format!("OWL/XML parse: {error}"))
                    })?;
            let mapped: ComponentMappedOntology<RcStr, RcAnnotatedComponent> = ontology.into();
            write_functional(&mapped, Some(&prefixes))?
        }
        InputFormat::RdfXml | InputFormat::Turtle => {
            let rdf_format = match format {
                InputFormat::RdfXml => oxrdfio::RdfFormat::RdfXml,
                InputFormat::Turtle => oxrdfio::RdfFormat::Turtle,
                _ => unreachable!(),
            };
            let config = ParserConfiguration {
                rdf: horned_owl::io::RDFParserConfiguration {
                    lax: false,
                    format: Some(rdf_format),
                },
                ..ParserConfiguration::default()
            };
            let (ontology, incomplete) = horned_owl::io::rdf::reader::read(&mut reader, config)
                .map_err(|error| {
                    OrchestrateError::OutOfFragment(format!("OWL/RDF parse: {error}"))
                })?;
            if !incomplete.is_complete() {
                return Err(OrchestrateError::OutOfFragment(format!(
                    "OWL/RDF mapping was incomplete: {} simple triples, {} blank-node triples, {} lists, {} class expressions, {} property expressions, {} data ranges, {} atoms, {} annotations remained",
                    incomplete.simple.len(),
                    incomplete.bnode.len(),
                    incomplete.bnode_seq.len(),
                    incomplete.class_expression.len(),
                    incomplete.object_property_expression.len(),
                    incomplete.data_range.len(),
                    incomplete.atom.len(),
                    incomplete.ann_map.len(),
                )));
            }
            let mapped: ComponentMappedOntology<RcStr, RcAnnotatedComponent> = ontology.into();
            write_functional(&mapped, None)?
        }
        InputFormat::Functional => unreachable!(),
    };

    Ok(PreparedInput {
        original: path,
        converted: Some(converted),
    })
}

pub fn prepare(path: &Path) -> Result<PreparedInput<'_>, OrchestrateError> {
    prepare_with_format(path, sniff(path)?)
}

/// Internal reasoning paths may receive a registered generated OFN document.
/// Its format is established by the producer, independently of whether source
/// re-validation is enabled. Public input format selection remains in prepare.
pub(crate) fn prepare_for_reasoning(path: &Path) -> Result<PreparedInput<'_>, OrchestrateError> {
    if super::is_registered_functional_rewrite(path) {
        prepare_with_format(path, InputFormat::Functional)
    } else {
        prepare(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn convert(source: &str, suffix: &str, format: &str) -> crate::frontend::FrontendResult {
        let path = TempPath::new(suffix);
        std::fs::write(path.path(), source).unwrap();
        let prepared =
            prepare_with_format(path.path(), InputFormat::parse(format).unwrap()).unwrap();
        let functional = std::fs::read_to_string(prepared.path()).unwrap();
        crate::frontend::ofn_to_clauses(&functional).unwrap()
    }

    #[test]
    fn registered_functional_input_keeps_format_when_validation_bypass_is_disabled() {
        const CHILD: &str = "KM_TEST_REGISTERED_FUNCTIONAL_INPUT_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let source = "Ontology(Declaration(Class(<urn:A>)) Declaration(Class(<urn:B>)) SubClassOf(<urn:A> <urn:B>))";
            crate::frontend::conformance::check_user_source(source).unwrap();
            let file = TempPath::new("-registered-functional.ofn");
            std::fs::write(file.path(), source).unwrap();
            let _registered = super::super::TrustedRewrite::register(file.path());
            assert!(super::super::is_registered_functional_rewrite(file.path()));
            assert_eq!(super::super::is_trusted_rewrite(file.path()),
                std::env::var_os("KM_NO_TRUSTED_REWRITES").is_none());
            let prepared = prepare_for_reasoning(file.path()).unwrap();
            assert_eq!(prepared.path(), file.path());
            assert_eq!(std::fs::read_to_string(prepared.path()).unwrap(), source);
            // Public format selection remains user-configured even for a
            // generated-looking OFN path; do not feed that deliberately wrong
            // syntax into the upstream RDF reader's unchecked error path.
            let configured = std::env::var("KM_INPUT_FORMAT").unwrap();
            assert_eq!(sniff(file.path()).unwrap(), InputFormat::parse(&configured).unwrap());
            let external_source = match configured.as_str() {
                "rdfxml" => r#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#" xmlns:owl="http://www.w3.org/2002/07/owl#"><owl:Class rdf:about="urn:A"><rdfs:subClassOf rdf:resource="urn:B"/></owl:Class><owl:Class rdf:about="urn:B"/></rdf:RDF>"#,
                "turtle" => "@prefix owl: <http://www.w3.org/2002/07/owl#> . @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . <urn:A> a owl:Class ; rdfs:subClassOf <urn:B> . <urn:B> a owl:Class .",
                other => panic!("unexpected child format {other}"),
            };
            let external = TempPath::new("-public-external-format.ofn");
            std::fs::write(external.path(), external_source).unwrap();
            let converted = prepare(external.path()).unwrap();
            assert_ne!(converted.path(), external.path());
            let functional = std::fs::read_to_string(converted.path()).unwrap();
            assert!(functional.contains("Ontology("));
            crate::frontend::ofn_to_clauses(&functional).unwrap();
            return;
        }
        for format in ["rdfxml", "turtle"] {
            for no_trust in [false, true] {
                let mut command = std::process::Command::new(std::env::current_exe().unwrap());
                command.args(["--exact", "orchestrate::input::tests::registered_functional_input_keeps_format_when_validation_bypass_is_disabled", "--nocapture", "--test-threads=1"]);
                for (key, _) in std::env::vars_os() {
                    if key.to_string_lossy().starts_with("KM_") { command.env_remove(key); }
                }
                command.env(CHILD, "1").env("KM_INPUT_FORMAT", format);
                if no_trust { command.env("KM_NO_TRUSTED_REWRITES", "1"); }
                let output = command.output().unwrap();
                assert!(output.status.success(), "{format}, no_trust={no_trust}: {} {}",
                    String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
                assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed"),
                    "child exact filter must execute its test, not pass zero tests");
            }
        }
    }

    #[test]
    fn format_aliases_are_explicit() {
        assert_eq!(InputFormat::parse("ofn").unwrap(), InputFormat::Functional);
        assert_eq!(InputFormat::parse("OWL-XML").unwrap(), InputFormat::OwlXml);
        assert_eq!(InputFormat::parse("rdfxml").unwrap(), InputFormat::RdfXml);
        assert_eq!(InputFormat::parse("ttl").unwrap(), InputFormat::Turtle);
        assert!(InputFormat::parse("manchester").is_err());
    }

    #[test]
    fn owlxml_rdfxml_and_turtle_share_the_functional_frontend() {
        let owlxml = r#"<?xml version="1.0"?>
<Ontology xmlns="http://www.w3.org/2002/07/owl#"
 ontologyIRI="http://example.org/test">
 <Declaration><Class IRI="http://example.org/A"/></Declaration>
 <Declaration><Class IRI="http://example.org/B"/></Declaration>
 <SubClassOf>
  <Class IRI="http://example.org/A"/>
  <Class IRI="http://example.org/B"/>
 </SubClassOf>
</Ontology>"#;
        let rdfxml = r#"<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
 xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
 xmlns:owl="http://www.w3.org/2002/07/owl#">
 <owl:Ontology rdf:about="http://example.org/test"/>
 <owl:Class rdf:about="http://example.org/A">
  <rdfs:subClassOf rdf:resource="http://example.org/B"/>
 </owl:Class>
 <owl:Class rdf:about="http://example.org/B"/>
</rdf:RDF>"#;
        let turtle = r#"@prefix ex: <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:test a owl:Ontology .
ex:A a owl:Class ; rdfs:subClassOf ex:B .
ex:B a owl:Class .
"#;

        for result in [
            convert(owlxml, ".owx", "owlxml"),
            convert(rdfxml, ".rdf", "rdfxml"),
            convert(turtle, ".ttl", "turtle"),
        ] {
            let a = result
                .iri_map
                .iter()
                .find_map(|(short, full)| (full == "http://example.org/A").then_some(short))
                .unwrap();
            let b = result
                .iri_map
                .iter()
                .find_map(|(short, full)| (full == "http://example.org/B").then_some(short))
                .unwrap();
            assert!(result.named.contains(a));
            assert!(result.named.contains(b));
            assert!(result.clauses.iter().any(|clause| {
                use crate::json_io::JAtom;
                matches!(
                    (clause.body.as_slice(), clause.head.as_slice()),
                    (
                        [JAtom::Concept { concept: body, .. }],
                        [JAtom::Concept { concept: head, .. }]
                    ) if body == a && head == b
                )
            }));
        }
    }
}
