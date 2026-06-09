//! RBox extraction from the parsed functional-syntax tree.
//!
//! Direct port of `frontend.ofn_rbox`, `_plain_role`, `_plain_class`. Only the
//! `domain` / `range` records affect the emitted clause set (via
//! `preprocess.domain_range_clauses`); the other record kinds are produced for
//! parity with the Python list but are not consumed by `ofn_to_clauses`.

use super::iri::IriRegistry;
use super::sexpr::Node;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RboxRecord {
    Subrole(String, String),
    Domain(String, String),
    Range(String, String),
    Inverse(String, String),
    Fenced(String, String),
}

/// Port of `_plain_role`: named role -> Some(short); inverse/complex -> None.
fn plain_role(reg: &mut IriRegistry, node: &Node) -> Option<String> {
    match node {
        Node::Atom(s) => Some(reg.short(s)),
        _ => None,
    }
}

/// Port of `_plain_class`: named class -> Some(short); ⊤ -> Some(""); ⊥/complex
/// -> None.
fn plain_class(reg: &mut IriRegistry, node: &Node) -> Option<String> {
    match node {
        Node::Atom(s) => {
            let sh = reg.short(s);
            if sh == "owl:Thing" || sh == "Thing" {
                Some(String::new())
            } else if sh == "owl:Nothing" || sh == "Nothing" {
                None
            } else {
                Some(sh)
            }
        }
        _ => None,
    }
}

fn strip_annotations(args: &[Node]) -> Vec<&Node> {
    args.iter()
        .filter(|a| a.head() != Some("Annotation"))
        .collect()
}

/// Port of `ofn_rbox`. `nodes` are the arguments of the `Ontology(...)` node.
pub fn ofn_rbox(reg: &mut IriRegistry, nodes: &[Node]) -> Vec<RboxRecord> {
    let mut out = Vec::new();
    for node in nodes {
        let (head, args) = match node {
            Node::List(h, a) => (h.as_str(), a),
            _ => continue,
        };
        let args = strip_annotations(args);
        match head {
            "SubObjectPropertyOf" => {
                let sub = args[0];
                let sup = args[1];
                let ssup = plain_role(reg, sup);
                if sub.head() == Some("ObjectPropertyChain") {
                    out.push(RboxRecord::Fenced(
                        "role-chain".to_string(),
                        format!("{:?} ⊑ {:?}", sub, sup),
                    ));
                } else if let (Some(rsub), Some(rsup)) = (plain_role(reg, sub), ssup) {
                    out.push(RboxRecord::Subrole(rsub, rsup));
                } else {
                    out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("SubObjectPropertyOf {:?} ⊑ {:?}", sub, sup),
                    ));
                }
            }
            "ObjectPropertyDomain" => {
                let r = plain_role(reg, args[0]);
                let d = plain_class(reg, args[1]);
                match (r, d) {
                    (None, _) => out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("domain of {:?}", args[0]),
                    )),
                    (Some(_), None) => out.push(RboxRecord::Fenced(
                        "complex-domain".to_string(),
                        format!("domain({:?}) = {:?}", args[0], args[1]),
                    )),
                    (Some(r), Some(d)) => {
                        if !d.is_empty() {
                            out.push(RboxRecord::Domain(r, d));
                        }
                    }
                }
            }
            "ObjectPropertyRange" => {
                let r = plain_role(reg, args[0]);
                let c = plain_class(reg, args[1]);
                match (r, c) {
                    (None, _) => out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("range of {:?}", args[0]),
                    )),
                    (Some(_), None) => out.push(RboxRecord::Fenced(
                        "complex-range".to_string(),
                        format!("range({:?}) = {:?}", args[0], args[1]),
                    )),
                    (Some(r), Some(c)) => {
                        if !c.is_empty() {
                            out.push(RboxRecord::Range(r, c));
                        }
                    }
                }
            }
            "InverseObjectProperties" => {
                let a = plain_role(reg, args[0]);
                let b = plain_role(reg, args[1]);
                match (a, b) {
                    (Some(a), Some(b)) => out.push(RboxRecord::Inverse(a, b)),
                    _ => out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("InverseObjectProperties {:?}", args),
                    )),
                }
            }
            "TransitiveObjectProperty" => {
                // not fenced (handled by TBox normalisation)
            }
            "SymmetricObjectProperty" => {
                let r = plain_role(reg, args[0]).unwrap_or_else(|| format!("{:?}", args[0]));
                out.push(RboxRecord::Fenced("symmetric-role".to_string(), r));
            }
            "ReflexiveObjectProperty" | "IrreflexiveObjectProperty" => {
                let r = plain_role(reg, args[0]).unwrap_or_else(|| format!("{:?}", args[0]));
                out.push(RboxRecord::Fenced("reflexivity".to_string(), r));
            }
            "FunctionalObjectProperty" => {
                // in-fragment for SHQ, not fenced
            }
            "InverseFunctionalObjectProperty" => {
                let r = plain_role(reg, args[0]).unwrap_or_else(|| format!("{:?}", args[0]));
                out.push(RboxRecord::Fenced("inverse-functional".to_string(), r));
            }
            "AsymmetricObjectProperty" | "DisjointObjectProperties" => {
                out.push(RboxRecord::Fenced(
                    "role-constraint".to_string(),
                    head.to_string(),
                ));
            }
            _ => {}
        }
    }
    out
}
