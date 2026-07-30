//! Elimination of vacuous `R ⊑ owl:topObjectProperty` property inclusions.
//!
//! `(owl:topObjectProperty)^I = ΔI × ΔI` in every OWL 2 DL interpretation, so
//! `SubObjectPropertyOf(R owl:topObjectProperty)` — with a plain role or a role
//! chain on the left — holds in every interpretation. It is a tautology and
//! removing it yields a logically equivalent ontology. `owl:topDataProperty`
//! is the corresponding ΔI × Δ_D and gives `SubDataPropertyOf` the same
//! tautology; KM abstracts data properties as roles with `__dt__` fillers, so
//! both arrive here as `Axiom::RoleInclusion`.
//!
//! KM does not have a universal-role object: `parse.rs` maps the builtin to an
//! ordinary named role, and the clausifier compiles the inclusion into the
//! write-only clause `R(x,y) → U(x,y)`. That approximation is only harmless
//! while nothing reads `U`, so several downstream procedures (most visibly the
//! `konclude_ht` bridge, which has no universal-role object at all) fail closed
//! the moment the builtin appears among the roles. On `ore_ont_541` the three
//! tautological inclusions are the ontology's ONLY occurrences of the builtin,
//! and they cost it every bridge arm.
//!
//! This pass removes those inclusions, and only when the builtin occurs nowhere
//! else. Under that condition the argument is exact in both directions:
//!
//! * sound + complete — every removed axiom is a tautology, so the ontology's
//!   entailments are unchanged; and
//! * derivation-preserving for the CB calculus — after the pass the builtin has
//!   no occurrence at all, and before it the only clauses mentioning `U` had it
//!   in the HEAD, so no rule could ever read a `U` atom. The saturation fixpoint
//!   is therefore unchanged modulo the dropped write-only atoms, which no query
//!   inspects. No Lean re-certification is needed: the calculus is untouched.
//!
//! Any other occurrence of the builtin (sub-role position, a role chain
//! component, a domain/range/inverse/transitivity row, a class expression, an
//! assertion) leaves the whole ontology exactly as it was.

use super::iri::IriRegistry;
use super::rbox::RboxRecord;
use super::sexpr::Node;
use super::syntax::{Axiom, Ontology};

const TOP_OBJECT_PROPERTY_IRI: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";
const TOP_DATA_PROPERTY_IRI: &str = "http://www.w3.org/2002/07/owl#topDataProperty";

/// Does this source token spell one of the builtin top properties?
///
/// `owl:topDataProperty` is the ΔI × Δ_D of the data domain, so it carries the
/// same tautology for `SubDataPropertyOf`.
fn is_top_property_token(token: &str) -> bool {
    matches!(
        token.trim().trim_matches(['<', '>']),
        "owl:topObjectProperty"
            | "owl:topDataProperty"
            | TOP_OBJECT_PROPERTY_IRI
            | TOP_DATA_PROPERTY_IRI
    )
}

/// Does this internal role name denote one of the builtin top properties?
///
/// `IriRegistry::short` canonicalises only `owl:Thing` / `owl:Nothing`, so the
/// builtin's internal name is whatever the local-name and collision rules
/// produced (`owl:topObjectProperty`, `topObjectProperty`,
/// `topObjectProperty__owl`, ...). Mapping the internal name back through the
/// registry is exact where a spelling table would have to guess at suffixes.
pub fn is_builtin_top_role(reg: &IriRegistry, internal: &str) -> bool {
    is_top_property_token(&reg.full_iri(internal))
}

/// Whether every occurrence of a builtin top property in a document is the
/// super-property of a property inclusion.
///
/// Fed the same `Ontology(...)` children as the parser, during the parse itself.
/// Both builtins share one verdict: an ontology that really uses either one is
/// left alone entirely.
#[derive(Default)]
pub struct TopRoleScan {
    vacuous_super: usize,
    other_occurrence: bool,
}

impl TopRoleScan {
    /// Record one `Ontology(...)` child.
    pub fn observe(&mut self, node: &Node<'_>) {
        if self.other_occurrence {
            return;
        }
        // A `Declaration` carries no logical content, so declaring the builtin
        // is not a use of it.
        if node.head() == Some("Declaration") {
            return;
        }
        let (head, args) = match node {
            Node::List(head, args) => (*head, args),
            Node::Atom(token) => {
                self.other_occurrence |= is_top_property_token(token);
                return;
            }
        };
        if head == "SubObjectPropertyOf" || head == "SubDataPropertyOf" {
            let logical: Vec<&Node> = args
                .iter()
                .filter(|arg| arg.head() != Some("Annotation"))
                .collect();
            if logical.len() == 2 {
                // Index 1 is the super-role. A bare builtin atom there is the
                // vacuous shape; anything else (an `ObjectInverseOf`, a nested
                // list) is scanned like any other position.
                self.scan(logical[0]);
                match logical[1] {
                    Node::Atom(token) if is_top_property_token(token) => {
                        self.vacuous_super += 1;
                    }
                    other => self.scan(other),
                }
                for arg in args.iter().filter(|arg| arg.head() == Some("Annotation")) {
                    self.scan(arg);
                }
                return;
            }
        }
        self.scan(node);
    }

    fn scan(&mut self, node: &Node<'_>) {
        if self.other_occurrence {
            return;
        }
        match node {
            Node::Atom(token) => self.other_occurrence |= is_top_property_token(token),
            Node::List(_, args) => {
                for arg in args {
                    self.scan(arg);
                }
            }
        }
    }

    /// True when the document has at least one tautological inclusion to remove
    /// and no other occurrence of the builtin.
    pub fn eliminable(&self) -> bool {
        self.vacuous_super > 0 && !self.other_occurrence
    }
}

/// Remove every `R ⊑ owl:topObjectProperty` / `R1 ∘ R2 ⊑ owl:topObjectProperty`
/// axiom. Returns how many were removed.
///
/// Call only when [`TopRoleScan::eliminable`] holds.
pub fn elide_vacuous_inclusions(ontology: &mut Ontology, reg: &IriRegistry) -> usize {
    ontology.retain_axioms(|axiom| match axiom {
        Axiom::RoleInclusion(_, sup) | Axiom::RoleChain(_, sup) => {
            !is_builtin_top_role(reg, sup)
        }
        _ => true,
    })
}

/// The RBox side data is re-extracted from the source text after
/// clausification, so it carries the same tautological rows. Drop them too:
/// they are what puts the builtin into the `TInput` role table.
pub fn elide_vacuous_rbox_rows(rbox: &mut Vec<RboxRecord>, reg: &IriRegistry) {
    rbox.retain(|record| match record {
        RboxRecord::Subrole(_, sup) | RboxRecord::Chain(_, _, sup) => {
            !is_builtin_top_role(reg, sup)
        }
        _ => true,
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{ofn_to_clauses, parse};

    fn scan(text: &str) -> TopRoleScan {
        let mut reg = IriRegistry::new();
        let mut scan = TopRoleScan::default();
        parse::parse_axioms_observed(&mut reg, text, |node| scan.observe(node))
            .expect("parse test ontology");
        scan
    }

    #[test]
    fn only_super_role_occurrences_are_eliminable() {
        for text in [
            "Ontology(SubObjectPropertyOf(<http://e#r> owl:topObjectProperty))",
            "Ontology(SubObjectPropertyOf(<http://e#r> \
             <http://www.w3.org/2002/07/owl#topObjectProperty>))",
            // several inclusions, plus an unrelated axiom
            "Ontology(SubObjectPropertyOf(<http://e#r> owl:topObjectProperty) \
             SubObjectPropertyOf(<http://e#s> owl:topObjectProperty) \
             SubClassOf(<http://e#A> <http://e#B>))",
            // a declaration of the builtin carries no logical content
            "Ontology(Declaration(ObjectProperty(owl:topObjectProperty)) \
             SubObjectPropertyOf(<http://e#r> owl:topObjectProperty))",
            // the data-property mirror
            "Ontology(SubDataPropertyOf(<http://e#d> owl:topDataProperty))",
        ] {
            assert!(scan(text).eliminable(), "{text}");
        }
    }

    #[test]
    fn any_other_occurrence_blocks_elimination() {
        for text in [
            // sub-role position: a real universal-role axiom
            "Ontology(SubObjectPropertyOf(owl:topObjectProperty <http://e#r>) \
             SubObjectPropertyOf(<http://e#s> owl:topObjectProperty))",
            // class expression
            "Ontology(SubClassOf(<http://e#A> ObjectSomeValuesFrom(owl:topObjectProperty \
             <http://e#B>)) SubObjectPropertyOf(<http://e#r> owl:topObjectProperty))",
            // domain row (no parsed axiom at all in the named-class case)
            "Ontology(ObjectPropertyDomain(owl:topObjectProperty <http://e#C>) \
             SubObjectPropertyOf(<http://e#r> owl:topObjectProperty))",
            // transitivity row
            "Ontology(TransitiveObjectProperty(owl:topObjectProperty) \
             SubObjectPropertyOf(<http://e#r> owl:topObjectProperty))",
            // inverse row
            "Ontology(InverseObjectProperties(<http://e#r> owl:topObjectProperty) \
             SubObjectPropertyOf(<http://e#s> owl:topObjectProperty))",
            // chain component
            "Ontology(SubObjectPropertyOf(ObjectPropertyChain(<http://e#r> \
             owl:topObjectProperty) <http://e#s>) \
             SubObjectPropertyOf(<http://e#t> owl:topObjectProperty))",
            // a real use of either builtin blocks BOTH: one verdict per document
            "Ontology(DataPropertyDomain(owl:topDataProperty <http://e#C>) \
             SubObjectPropertyOf(<http://e#r> owl:topObjectProperty))",
        ] {
            assert!(!scan(text).eliminable(), "{text}");
        }
    }

    #[test]
    fn nothing_to_eliminate_without_the_builtin() {
        assert!(!scan("Ontology(SubObjectPropertyOf(<http://e#r> <http://e#s>))").eliminable());
    }

    #[test]
    fn vacuous_inclusion_leaves_no_builtin_role_behind() {
        let ontology = "Ontology(\
             Declaration(Class(<http://e#A>))\
             SubObjectPropertyOf(<http://e#r> owl:topObjectProperty)\
             SubObjectPropertyOf(<http://e#r> <http://e#s>)\
             SubClassOf(<http://e#A> ObjectSomeValuesFrom(<http://e#r> <http://e#B>))\
             SubClassOf(ObjectSomeValuesFrom(<http://e#s> <http://e#B>) <http://e#C>))";
        let result = ofn_to_clauses(ontology).expect("frontend");
        let mentions_top = |name: &str| name.contains("topObjectProperty");
        for clause in &result.clauses {
            let json = serde_json::to_string(clause).expect("clause json");
            assert!(!mentions_top(&json), "clause still mentions the builtin: {json}");
        }
        for row in &result.rbox {
            assert!(
                !row.iter().any(|cell| mentions_top(cell)),
                "rbox row still mentions the builtin: {row:?}"
            );
        }
        // The surviving `r ⊑ s` inclusion still carries A ⊑ C.
        assert!(result
            .rbox
            .iter()
            .any(|row| row == &vec!["subrole".to_string(), "r".to_string(), "s".to_string()]));
    }

    #[test]
    fn a_real_universal_role_use_keeps_the_inclusion() {
        let ontology = "Ontology(\
             SubObjectPropertyOf(<http://e#r> owl:topObjectProperty)\
             SubClassOf(<http://e#A> ObjectAllValuesFrom(owl:topObjectProperty <http://e#B>)))";
        let result = ofn_to_clauses(ontology).expect("frontend");
        let json = serde_json::to_string(&result.clauses).expect("clause json");
        assert!(
            json.contains("topObjectProperty"),
            "the inclusion must survive when the builtin is really used"
        );
    }
}
