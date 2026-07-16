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
