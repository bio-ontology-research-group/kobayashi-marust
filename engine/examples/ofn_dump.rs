//! Dump what the Rust frontend parser makes of an OWL functional-syntax file,
//! in the JSON shape of the Lean `km-owl-parse` executable (v1.6.2
//! differential test of `lean/ContextCalculus/OWL/Parse.lean`).
//!
//! Usage: `ofn_dump <file>`. Prints one JSON object:
//! `{"status":"ok","classes":[..],"objectProperties":[..],"axiomCounts":{..},"rust":{..}}`
//! or `{"status":"rejected","reason":".."}`.
//!
//! What comes from the Rust parser and what the dump adds:
//! - `classes` / `objectProperties`: every source name (registry-owned, so
//!   generated proxies such as `__inv__r` are excluded) that occurs in a
//!   class or object-property position of the ontology built by
//!   `parse::parse_axioms`, of the RBox records of `rbox::rbox_node` (atomic
//!   domains and ranges are only recorded there), and of
//!   `Declaration(Class(..))` / `Declaration(ObjectProperty(..))` nodes.
//!   `owl:Thing` / `owl:Nothing` are excluded the way the registry
//!   recognises them.
//! - The Rust registry keys a name by its raw spelling and never expands a
//!   prefixed name. To compare with the Lean parser, which expands, the dump
//!   expands each raw spelling with the document's `Prefix` declarations and
//!   the four standard prefixes of `conformance.rs`. `rust.collisions` counts
//!   distinct Rust names that expand to one IRI (one entity that Rust splits
//!   in two); `rust.ambiguous` counts Rust names reached by both a full and a
//!   prefixed spelling (two entities Rust may merge).
//! - `axiomCounts`: the number of `Ontology(..)` children per axiom head as
//!   the Rust tokeniser and s-expression parser produce them (duplicates
//!   counted), keyed like the Lean `Axiom` constructors.
//! - `rust.iriPrefixCheck`: the result of `conformance::check_iri_prefixes`.
use std::collections::{BTreeMap, BTreeSet, HashMap};

use kobayashi_marust::frontend::iri::IriRegistry;
use kobayashi_marust::frontend::parse;
use kobayashi_marust::frontend::rbox::{rbox_node, RboxRecord};
use kobayashi_marust::frontend::sexpr::{tokens, Node, Parser};
use kobayashi_marust::frontend::syntax::{Axiom, Concept, Role};
use serde_json::json;

const KINDS: [&str; 12] = [
    "subClassOf",
    "equivalentClasses",
    "disjointClasses",
    "domain",
    "range",
    "subObjectPropertyOf",
    "equivalentObjectProperties",
    "inverseObjectProperties",
    "transitive",
    "symmetric",
    "declareClass",
    "declareObjectProperty",
];

const STANDARD_PREFIXES: [(&str, &str); 4] = [
    ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
    ("owl", "http://www.w3.org/2002/07/owl#"),
    ("xsd", "http://www.w3.org/2001/XMLSchema#"),
    ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
];

fn kind_of(node: &Node) -> Option<&'static str> {
    let Node::List(head, args) = node else { return None };
    Some(match *head {
        "SubClassOf" => "subClassOf",
        "EquivalentClasses" => "equivalentClasses",
        "DisjointClasses" => "disjointClasses",
        "ObjectPropertyDomain" => "domain",
        "ObjectPropertyRange" => "range",
        "SubObjectPropertyOf" => "subObjectPropertyOf",
        "EquivalentObjectProperties" => "equivalentObjectProperties",
        "InverseObjectProperties" => "inverseObjectProperties",
        "TransitiveObjectProperty" => "transitive",
        "SymmetricObjectProperty" => "symmetric",
        "Declaration" => match args.iter().find(|a| a.head() != Some("Annotation")) {
            Some(Node::List("Class", _)) => "declareClass",
            Some(Node::List("ObjectProperty", _)) => "declareObjectProperty",
            _ => return None,
        },
        _ => return None,
    })
}

/// The entity of `Declaration(Class(x))` / `Declaration(ObjectProperty(x))`.
fn declared<'a>(node: &Node<'a>, kind: &str) -> Option<&'a str> {
    let Node::List("Declaration", args) = node else { return None };
    match args.iter().find(|a| a.head() != Some("Annotation")) {
        Some(Node::List(k, inner)) if *k == kind => inner.first().and_then(Node::as_atom),
        _ => None,
    }
}

/// The same prefix map as `conformance::prefixes` (a private function).
fn prefixes(text: &str) -> BTreeMap<String, String> {
    let mut map: BTreeMap<String, String> = STANDARD_PREFIXES
        .iter()
        .map(|(n, i)| ((*n).to_owned(), (*i).to_owned()))
        .collect();
    let mut parser = Parser::new(text);
    while parser.peek() == Some("Prefix") {
        let Ok(Node::List(_, args)) = parser.parse() else { break };
        let parts: Option<Vec<_>> = args.iter().map(Node::as_atom).collect();
        if let Some(parts) = parts {
            let definition = parts.concat();
            if let Some((prefix, iri)) = definition.split_once(":=") {
                if let Some(iri) = iri.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
                    map.insert(prefix.to_owned(), iri.to_owned());
                }
            }
        }
    }
    map
}

#[derive(Default)]
struct Names {
    classes: BTreeSet<String>,
    roles: BTreeSet<String>,
}

impl Names {
    fn role(&mut self, r: &Role) {
        match r {
            Role::Name(n) | Role::Inverse(n) => {
                self.roles.insert(n.clone());
            }
            Role::Universal => {}
        }
    }
    fn concept(&mut self, c: &Concept) {
        match c {
            Concept::Name(n) => {
                self.classes.insert(n.clone());
            }
            Concept::Top | Concept::Bottom | Concept::Nominal(_) => {}
            Concept::Not(c) => self.concept(c),
            Concept::And(cs) | Concept::Or(cs) => cs.iter().for_each(|c| self.concept(c)),
            Concept::Exists(r, c) | Concept::Forall(r, c) => {
                self.role(r);
                self.concept(c)
            }
            Concept::AtLeast(_, r, c) | Concept::AtMost(_, r, c) => {
                self.role(r);
                self.concept(c)
            }
            Concept::HasSelf(r) => self.role(r),
        }
    }
    fn axiom(&mut self, a: &Axiom) {
        let mut role = |n: &String| {
            self.roles.insert(n.clone());
        };
        match a {
            Axiom::SubClassOf(c, d) | Axiom::EquivalentClasses(c, d) | Axiom::DisjointClasses(c, d) => {
                self.concept(c);
                self.concept(d)
            }
            Axiom::RoleInclusion(r, s) | Axiom::InverseRoles(r, s) | Axiom::DisjointRoles(r, s) => {
                role(r);
                role(s)
            }
            Axiom::RoleChain(rs, s) => {
                rs.iter().for_each(&mut role);
                role(s)
            }
            Axiom::TransitiveRole(r)
            | Axiom::SymmetricRole(r)
            | Axiom::AsymmetricRole(r)
            | Axiom::ReflexiveRole(r)
            | Axiom::IrreflexiveRole(r)
            | Axiom::FunctionalRole(r)
            | Axiom::InverseFunctionalRole(r) => role(r),
            Axiom::ConceptAssertion(c, _) => self.concept(c),
            Axiom::RoleAssertion(r, _, _) | Axiom::NegativeRoleAssertion(r, _, _) => role(r),
            _ => {}
        }
    }
}

fn dump(text: &str) -> serde_json::Value {
    let mut reg = IriRegistry::new();
    let ontology = match parse::parse_axioms(&mut reg, text) {
        Ok(o) => o,
        Err(e) => return json!({"status": "rejected", "reason": e.0}),
    };
    let mut names = Names::default();
    for a in ontology.axioms_iter() {
        names.axiom(a);
    }
    let mut records: Vec<RboxRecord> = Vec::new();
    let mut counts: BTreeMap<&str, u64> = KINDS.iter().map(|k| (*k, 0)).collect();
    let mut declared_classes = Vec::new();
    let mut declared_roles = Vec::new();
    let walk = parse::for_each_ontology_child(text, |node| {
        rbox_node(&mut reg, node, &mut records);
        if let Some(k) = kind_of(node) {
            *counts.get_mut(k).unwrap() += 1;
        }
        if let Some(c) = declared(node, "Class") {
            declared_classes.push(c);
        }
        if let Some(r) = declared(node, "ObjectProperty") {
            declared_roles.push(r);
        }
        Ok(())
    });
    if let Err(e) = walk {
        return json!({"status": "rejected", "reason": e.0});
    }
    for c in declared_classes {
        let s = reg.short(c);
        if s != "owl:Thing" && s != "owl:Nothing" {
            names.classes.insert(s);
        }
    }
    for r in declared_roles {
        names.roles.insert(reg.short(r));
    }
    for rec in &records {
        match rec {
            RboxRecord::Domain(r, c) | RboxRecord::Range(r, c) => {
                names.roles.insert(r.clone());
                names.classes.insert(c.clone());
            }
            RboxRecord::Subrole(r, s) | RboxRecord::Inverse(r, s) => {
                names.roles.insert(r.clone());
                names.roles.insert(s.clone());
            }
            RboxRecord::Transitive(r) => {
                names.roles.insert(r.clone());
            }
            RboxRecord::Chain(r, s, t) => {
                for n in [r, s, t] {
                    names.roles.insert(n.clone());
                }
            }
            RboxRecord::ChainN(rs, t) => {
                for n in rs.iter().chain(std::iter::once(t)) {
                    names.roles.insert(n.clone());
                }
            }
            RboxRecord::Fenced(..) => {}
        }
    }

    // Raw spellings per Rust name: is each reached by a full `<..>` or a
    // prefixed spelling (or both)?
    let mut spelled: HashMap<String, (bool, bool)> = HashMap::new();
    let mut seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for tok in tokens(text) {
        if tok == "(" || tok == ")" || tok.starts_with('"') || !seen.insert(tok) {
            continue;
        }
        if let Some(internal) = reg.assigned(tok) {
            let e = spelled.entry(internal.to_owned()).or_default();
            if tok.starts_with('<') {
                e.0 = true;
            } else {
                e.1 = true;
            }
        }
    }
    let pfx = prefixes(text);
    let mut undeclared = 0u64;
    let mut ambiguous = 0u64;
    let mut expand = |internal: &str| -> String {
        let raw = reg.full_iri(internal);
        let (full, prefixed) = spelled.get(internal).copied().unwrap_or((true, false));
        if full && prefixed {
            ambiguous += 1;
        }
        if full {
            return raw;
        }
        match raw.split_once(':') {
            Some((p, local)) => match pfx.get(p) {
                Some(ns) => format!("{ns}{local}"),
                None => {
                    undeclared += 1;
                    raw
                }
            },
            None => raw,
        }
    };
    let mut out_names = |set: &BTreeSet<String>| -> (Vec<String>, u64) {
        let named: Vec<&String> = set.iter().filter(|n| reg.is_named_iri(n)).collect();
        let expanded: BTreeSet<String> = named.iter().map(|n| expand(n)).collect();
        let collisions = (named.len() - expanded.len()) as u64;
        (expanded.into_iter().collect(), collisions)
    };
    let (classes, class_collisions) = out_names(&names.classes);
    let (roles, role_collisions) = out_names(&names.roles);
    let prefix_check = match kobayashi_marust::frontend::conformance::check_iri_prefixes(text) {
        Ok(()) => "ok".to_string(),
        Err(e) => e,
    };
    let rust_counts: BTreeMap<&str, usize> = [
        ("tbox", ontology.tbox().count()),
        ("rbox", ontology.rbox().count()),
        ("abox", ontology.abox().count()),
        ("rboxRecords", records.len()),
    ]
    .into_iter()
    .collect();
    json!({
        "status": "ok",
        "classes": classes,
        "objectProperties": roles,
        "axiomCounts": counts,
        "rust": {
            "collisions": class_collisions + role_collisions,
            "ambiguous": ambiguous,
            "undeclaredPrefix": undeclared,
            "iriPrefixCheck": prefix_check,
            "dropped": ontology.dropped_source_axioms(),
            "internal": rust_counts,
        }
    })
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: ofn_dump <file>");
    let value = match std::fs::read(&path) {
        Err(e) => json!({"status": "rejected", "reason": format!("cannot read file: {e}")}),
        Ok(bytes) => match String::from_utf8(bytes) {
            Err(_) => json!({"status": "rejected", "reason": "file is not valid UTF-8"}),
            Ok(text) => match std::panic::catch_unwind(|| dump(&text)) {
                Ok(v) => v,
                Err(p) => {
                    let msg = p
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_default();
                    json!({"status": "panic", "reason": msg})
                }
            },
        },
    };
    println!("{value}");
}
