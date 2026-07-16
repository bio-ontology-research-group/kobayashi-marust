//! Ontology expressivity and structural statistics.
//!
//! The expressivity code is a direct Rust rendering of Konclude's
//! `COntologyStructureSummary::calculateExpressiveness`: the source walker sets
//! the same occurrence flags and [`ExpressivityProfile::calculate_code`] applies
//! the same precedence (`Q > N > F`, complex role chains replace the base by
//! `SR`, and `ALC` plus transitivity contracts to `S`).  We inspect parsed OFN
//! nodes, not source text, so comments, IRIs containing constructor names, and
//! formatting cannot affect the result.

use std::collections::{BTreeMap, HashMap, HashSet};

use smallvec::SmallVec;

use super::sexpr::Node;

/// Konclude-compatible expressivity occurrence flags plus its DL code.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ExpressivityProfile {
    pub code: String,
    pub negation_disjunction: bool,
    pub existential: bool,
    pub cardinality: bool,
    pub qualified_cardinality: bool,
    pub functionality: bool,
    pub transitivity: bool,
    pub role_hierarchy: bool,
    pub complex_subrole: bool,
    pub universal_role: bool,
    pub inverse: bool,
    pub nominal_individual: bool,
    pub nominal: bool,
    pub grounding: bool,
    pub datatype: bool,
}

impl Default for ExpressivityProfile {
    fn default() -> Self {
        ExpressivityProfile {
            code: String::new(),
            negation_disjunction: false,
            existential: false,
            cardinality: false,
            qualified_cardinality: false,
            functionality: false,
            // Konclude's installed top-object-property structures contribute
            // I and + even to a class-only ontology (official-binary probe:
            // `SubClassOf(A B)` -> `ALI+`).  Start with those post-load flags,
            // then apply the source constructs below.
            transitivity: true,
            role_hierarchy: false,
            complex_subrole: false,
            universal_role: false,
            inverse: true,
            nominal_individual: false,
            nominal: false,
            grounding: false,
            datatype: false,
        }
    }
}

impl ExpressivityProfile {
    /// Exact port of Konclude
    /// `COntologyStructureSummary::calculateExpressiveness()`.
    pub fn calculate_code(&self) -> String {
        let mut code = if self.negation_disjunction {
            "ALC".to_string()
        } else if self.existential {
            "ALE".to_string()
        } else {
            "AL".to_string()
        };
        let mut trailing_plus = self.transitivity;
        if code == "ALC" && trailing_plus {
            code = "S".to_string();
            trailing_plus = false;
        }
        if self.complex_subrole {
            code = "SR".to_string();
        } else if self.role_hierarchy {
            code.push('H');
        }
        if self.nominal {
            code.push('O');
        }
        if self.inverse {
            code.push('I');
        }
        if self.qualified_cardinality {
            code.push('Q');
        } else if self.cardinality {
            code.push('N');
        } else if self.functionality {
            code.push('F');
        }
        if self.grounding {
            code.push('V');
        }
        if self.datatype {
            code.push_str("(D)");
        }
        if trailing_plus {
            code.push('+');
        }
        code
    }

    fn finish(&mut self) {
        self.code = self.calculate_code();
    }
}

/// Counts over the parsed OWL functional-syntax source.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SourceStatistics {
    pub file_bytes: u64,
    pub ontology_children: u64,
    pub logical_axioms: u64,
    pub tbox_axioms: u64,
    pub rbox_axioms: u64,
    pub abox_axioms: u64,
    pub rule_axioms: u64,
    /// DL-safe rules containing an atom/head shape outside the exact
    /// rule-consistency worker contract. Such an ontology must be declined,
    /// never classified after silently dropping the rule.
    pub unsupported_rule_axioms: u64,
    pub declarations: u64,
    pub annotation_axioms: u64,
    pub imports: u64,

    pub declared_classes: u64,
    pub declared_object_properties: u64,
    pub declared_data_properties: u64,
    pub declared_named_individuals: u64,
    pub distinct_classes: u64,
    pub distinct_object_properties: u64,
    pub distinct_data_properties: u64,
    pub distinct_individuals: u64,

    pub subclass_axioms: u64,
    pub equivalent_class_axioms: u64,
    pub disjoint_class_axioms: u64,
    pub role_inclusion_axioms: u64,
    pub role_chain_axioms: u64,
    pub transitive_role_axioms: u64,
    pub functional_role_axioms: u64,
    pub inverse_functional_role_axioms: u64,
    pub domain_axioms: u64,
    pub range_axioms: u64,
    pub class_assertions: u64,
    pub role_assertions: u64,

    pub concept_expressions: u64,
    pub intersections: u64,
    pub unions: u64,
    pub complements: u64,
    /// Occurrences of owl:Nothing in a class-expression position. This is
    /// separate from `complements`: a positive-looking axiom such as
    /// `A SubClassOf owl:Nothing` is still a negative constraint.
    #[serde(default)]
    pub bottom_occurrences: u64,
    /// Occurrences of owl:bottomObjectProperty or owl:bottomDataProperty in a
    /// logical-axiom operand. Positive assertions on a bottom role can be
    /// inconsistent even when no class complement occurs.
    #[serde(default)]
    pub bottom_role_occurrences: u64,
    pub existentials: u64,
    pub universals: u64,
    pub min_cardinalities: u64,
    pub max_cardinalities: u64,
    pub exact_cardinalities: u64,
    pub qualified_cardinalities: u64,
    pub unqualified_cardinalities: u64,
    pub nominals: u64,
    pub has_values: u64,
    pub has_self: u64,
    pub datatype_constructors: u64,
    pub max_concept_depth: u64,
    pub max_concept_arity: u64,
    pub max_role_chain_length: u64,
    pub max_cardinality: u64,

    /// Raw top-level constructor counts.  This preserves useful statistics for
    /// constructors that do not deserve a fixed routing feature.
    pub axiom_types: BTreeMap<String, u64>,
}

/// Counts over the normalized DL-clause set actually handed to a worker.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ClauseStatistics {
    pub clauses: u64,
    pub concept_symbols: u64,
    pub role_symbols: u64,
    pub body_atoms: u64,
    pub head_atoms: u64,
    pub max_body_atoms: u64,
    pub max_head_atoms: u64,
    pub horn_clauses: u64,
    pub disjunctive_clauses: u64,
    pub max_disjunction_width: u64,
    pub empty_body_clauses: u64,
    pub empty_head_clauses: u64,
    pub binary_top_disjunctions: u64,
    pub binary_bottom_clauses: u64,
    pub complementary_definers: u64,
    pub clauses_with_function_terms: u64,
    pub clauses_with_aux_terms: u64,
    pub equality_atoms: u64,
    pub role_chain_clauses: u64,
    pub transitivity_clauses: u64,
}

/// Versioned profile carried in `ofn --meta` and consumed by the router.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct OntologyProfile {
    pub schema_version: u32,
    /// Source-only proof that the positive ABox is consistent and cannot alter
    /// any named-class TBox subsumption. See
    /// `positive_abox_tbox_separable` for the fail-closed contract.
    #[serde(default)]
    pub positive_abox_tbox_separable: bool,
    pub expressivity: ExpressivityProfile,
    pub source: SourceStatistics,
    pub clauses: ClauseStatistics,
}

/// Streaming source profiler.  Entity sets borrow tokens from the ontology
/// text, so exact distinct counts require only pointer-sized set entries and no
/// duplicate strings, including on the ORE giants.
pub struct SourceProfileBuilder<'a> {
    stats: SourceStatistics,
    expr: ExpressivityProfile,
    classes: HashSet<&'a str>,
    object_properties: HashSet<&'a str>,
    data_properties: HashSet<&'a str>,
    individuals: HashSet<&'a str>,
    declared_classes: HashSet<&'a str>,
    declared_object_properties: HashSet<&'a str>,
    declared_data_properties: HashSet<&'a str>,
    declared_individuals: HashSet<&'a str>,
    transitive_roles: HashSet<&'a str>,
    restriction_roles: HashSet<&'a str>,
    subclass_lhs: HashSet<&'a str>,
    existential_definition_lhs: HashSet<&'a str>,
    inverse_partners: HashMap<&'a str, HashSet<&'a str>>,
    explicit_inverse_relation: bool,
    object_role_hierarchy: bool,
    nominal_unconditional: bool,
    nominal_from_abox: bool,
    nominal_from_concept: bool,
    conditional_nominal_roles: HashSet<&'a str>,
    conditional_nominal_role: Option<&'a str>,
    union_equivalence: bool,
    axiom_types: std::collections::HashMap<&'a str, u64>,
}

impl<'a> Default for SourceProfileBuilder<'a> {
    fn default() -> Self {
        SourceProfileBuilder {
            stats: SourceStatistics::default(),
            expr: ExpressivityProfile::default(),
            classes: HashSet::new(),
            object_properties: HashSet::new(),
            data_properties: HashSet::new(),
            individuals: HashSet::new(),
            declared_classes: HashSet::new(),
            declared_object_properties: HashSet::new(),
            declared_data_properties: HashSet::new(),
            declared_individuals: HashSet::new(),
            transitive_roles: HashSet::new(),
            restriction_roles: HashSet::new(),
            subclass_lhs: HashSet::new(),
            existential_definition_lhs: HashSet::new(),
            inverse_partners: HashMap::new(),
            explicit_inverse_relation: false,
            object_role_hierarchy: false,
            nominal_unconditional: false,
            nominal_from_abox: false,
            nominal_from_concept: false,
            conditional_nominal_roles: HashSet::new(),
            conditional_nominal_role: None,
            union_equivalence: false,
            axiom_types: std::collections::HashMap::new(),
        }
    }
}

impl<'a> SourceProfileBuilder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn observe(&mut self, node: &Node<'a>) {
        self.stats.ontology_children += 1;
        let (head, raw_args) = match node {
            Node::List(h, args) => (*h, args.as_slice()),
            Node::Atom(_) => return,
        };
        *self.axiom_types.entry(head).or_insert(0) += 1;
        if !matches!(
            head,
            "Annotation"
                | "AnnotationAssertion"
                | "SubAnnotationPropertyOf"
                | "AnnotationPropertyDomain"
                | "AnnotationPropertyRange"
        ) {
            self.stats.bottom_role_occurrences +=
                raw_args.iter().map(bottom_role_occurrences).sum::<u64>();
        }
        // Almost every OFN axiom/expression has <=4 operands. SmallVec keeps
        // annotation filtering on the stack instead of allocating once per
        // axiom (millions of allocations on the ORE giants).
        let args: SmallVec<[&Node<'a>; 4]> = raw_args
            .iter()
            .filter(|n| n.head() != Some("Annotation"))
            .collect();

        match head {
            "Declaration" => self.declaration(&args),
            "Import" => self.stats.imports += 1,
            "Annotation"
            | "AnnotationAssertion"
            | "SubAnnotationPropertyOf"
            | "AnnotationPropertyDomain"
            | "AnnotationPropertyRange" => self.stats.annotation_axioms += 1,
            "SubClassOf" => {
                self.logical_tbox(head);
                self.stats.subclass_axioms += 1;
                if let Some(lhs) = args.first().and_then(|arg| arg.as_atom()) {
                    self.subclass_lhs.insert(lhs);
                }
                // Konclude internalizes a complex antecedent as a negated
                // concept operand. Atomic antecedents are implication triggers
                // and are explicitly excluded by COntologyInspector.
                if args
                    .first()
                    .is_some_and(|lhs| matches!(lhs, Node::List(..)))
                {
                    self.expr.negation_disjunction = true;
                }
                self.concepts(&args);
            }
            "EquivalentClasses" => {
                self.logical_tbox(head);
                self.stats.equivalent_class_axioms += 1;
                if args.len() == 2 {
                    for (named, definition) in [(args[0], args[1]), (args[1], args[0])] {
                        if definition.head() == Some("ObjectSomeValuesFrom") {
                            if let Some(named) = named.as_atom() {
                                self.existential_definition_lhs.insert(named);
                            }
                        }
                    }
                }
                if args.iter().any(|arg| arg.head() == Some("ObjectUnionOf")) {
                    self.union_equivalence = true;
                }
                // Konclude's preprocessing absorbs a named-only equivalence
                // without leaving a CCEQ occurrence (official probe: ALI+).
                // An intersection definition retains CCEQ (official probe:
                // SI), whereas a restriction definition is primitive and
                // retains only that restriction's occurrence flags.
                if args
                    .iter()
                    .any(|arg| arg.head() == Some("ObjectIntersectionOf"))
                {
                    self.expr.negation_disjunction = true;
                }
                self.concepts(&args);
            }
            "DisjointClasses" => {
                self.logical_tbox(head);
                self.stats.disjoint_class_axioms += 1;
                self.expr.negation_disjunction = true;
                self.concepts(&args);
            }
            "DisjointUnion" => {
                self.logical_tbox(head);
                self.stats.disjoint_class_axioms += 1;
                self.stats.unions += 1;
                self.expr.negation_disjunction = true;
                self.concepts(&args);
            }

            "SubObjectPropertyOf" => {
                self.logical_rbox(head);
                self.stats.role_inclusion_axioms += 1;
                if let Some(Node::List(ch, rs)) = args.first().copied() {
                    if *ch == "ObjectPropertyChain" {
                        self.stats.role_chain_axioms += 1;
                        self.stats.max_role_chain_length =
                            self.stats.max_role_chain_length.max(rs.len() as u64);
                        let super_role = args.get(1).and_then(|n| n.as_atom());
                        let all_transitive = super_role.is_some()
                            && !rs.is_empty()
                            && rs.iter().all(|r| r.as_atom() == super_role);
                        if all_transitive {
                            self.expr.transitivity = true;
                            if let Some(role) = super_role {
                                self.transitive_roles.insert(role);
                            }
                        } else {
                            self.expr.complex_subrole = true;
                        }
                        for r in rs {
                            self.object_role(r);
                        }
                        if let Some(r) = args.get(1) {
                            self.object_role(r);
                        }
                        return;
                    }
                }
                // Subroles of owl:topObjectProperty are installed as universal
                // connections, not as an H occurrence.
                if !args
                    .get(1)
                    .and_then(|n| n.as_atom())
                    .is_some_and(is_universal_role)
                {
                    self.expr.role_hierarchy = true;
                    self.object_role_hierarchy = true;
                }
                for r in &args {
                    self.object_role(r);
                }
            }
            "EquivalentObjectProperties" => {
                self.logical_rbox(head);
                self.expr.role_hierarchy = true;
                self.object_role_hierarchy = true;
                for r in &args {
                    self.object_role(r);
                }
            }
            "InverseObjectProperties" => {
                self.logical_rbox(head);
                self.expr.inverse = true;
                self.explicit_inverse_relation = true;
                if let (Some(left), Some(right)) = (
                    args.first().and_then(|arg| arg.as_atom()),
                    args.get(1).and_then(|arg| arg.as_atom()),
                ) {
                    self.inverse_partners.entry(left).or_default().insert(right);
                    self.inverse_partners.entry(right).or_default().insert(left);
                }
                for r in &args {
                    self.object_role(r);
                }
            }
            "DisjointObjectProperties" => {
                self.logical_rbox(head);
                for r in &args {
                    self.object_role(r);
                }
            }
            "TransitiveObjectProperty" => {
                self.logical_rbox(head);
                self.stats.transitive_role_axioms += 1;
                self.expr.transitivity = true;
                if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                    self.transitive_roles.insert(r);
                }
                self.object_roles(&args);
            }
            "SymmetricObjectProperty" => {
                self.logical_rbox(head);
                // Konclude represents symmetry through an inverse-equivalent
                // role link, which sets the I occurrence flag.
                self.expr.inverse = true;
                self.object_roles(&args);
            }
            "FunctionalObjectProperty" => {
                self.logical_rbox(head);
                self.stats.functional_role_axioms += 1;
                self.expr.functionality = true;
                // Konclude internalizes a functional role axiom through a
                // negated at-most concept (official probe: SIF), unlike a
                // source ObjectMaxCardinality(1 ...) expression (ALIF+).
                self.expr.negation_disjunction = true;
                self.object_roles(&args);
            }
            "InverseFunctionalObjectProperty" => {
                self.logical_rbox(head);
                self.stats.inverse_functional_role_axioms += 1;
                self.expr.functionality = true;
                self.expr.inverse = true;
                self.object_roles(&args);
            }
            "AsymmetricObjectProperty" | "ReflexiveObjectProperty" => {
                self.logical_rbox(head);
                self.object_roles(&args);
            }
            "IrreflexiveObjectProperty" => {
                self.logical_rbox(head);
                self.expr.negation_disjunction = true;
                self.object_roles(&args);
            }
            "ObjectPropertyDomain" => {
                self.logical_rbox(head);
                self.stats.domain_axioms += 1;
                let domain_role = args.first().and_then(|arg| arg.as_atom());
                if let Some(r) = args.first() {
                    self.object_role(r);
                }
                if let Some(c) = args.get(1) {
                    let previous_role = self.conditional_nominal_role;
                    self.conditional_nominal_role = domain_role;
                    self.concept(c, 1);
                    self.conditional_nominal_role = previous_role;
                }
            }
            "ObjectPropertyRange" => {
                self.logical_rbox(head);
                self.stats.range_axioms += 1;
                let range_role = args.first().and_then(|arg| arg.as_atom());
                if let Some(r) = args.first() {
                    self.object_role(r);
                }
                if let Some(c) = args.get(1) {
                    let previous_role = self.conditional_nominal_role;
                    self.conditional_nominal_role = range_role;
                    self.concept(c, 1);
                    self.conditional_nominal_role = previous_role;
                }
            }

            "SubDataPropertyOf" | "EquivalentDataProperties" => {
                self.logical_rbox(head);
                self.stats.role_inclusion_axioms += 1;
                self.expr.role_hierarchy = true;
                self.data_roles(&args);
            }
            "DisjointDataProperties" => {
                self.logical_rbox(head);
                self.data_roles(&args);
            }
            "FunctionalDataProperty" => {
                self.logical_rbox(head);
                self.stats.functional_role_axioms += 1;
                self.expr.functionality = true;
                self.expr.datatype = true;
                self.data_roles(&args);
            }
            "DataPropertyDomain" => {
                self.logical_rbox(head);
                self.stats.domain_axioms += 1;
                if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                    self.data_properties.insert(r);
                }
                if let Some(c) = args.get(1) {
                    self.concept(c, 1);
                }
            }
            "DataPropertyRange" => {
                self.logical_rbox(head);
                self.stats.range_axioms += 1;
                if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                    self.data_properties.insert(r);
                }
            }
            "DatatypeDefinition" => {
                self.logical_tbox(head);
                // A standalone datatype definition is internalized as a
                // nondeterministic concept but does not attach a data role, so
                // Konclude reports SI rather than a `(D)` suffix.
                self.expr.negation_disjunction = true;
            }
            "HasKey" => {
                self.logical_tbox(head);
                if let Some(c) = args.first() {
                    self.concept(c, 1);
                }
                // Property lists are nested nodes; recursively classify their
                // entries without treating annotation operands as entities.
                for n in args.iter().skip(1) {
                    self.key_properties(n);
                }
            }

            "ClassAssertion" => {
                self.logical_abox(head);
                self.stats.class_assertions += 1;
                if let Some(c) = args.first() {
                    self.concept(c, 1);
                }
                self.individual_arg(args.get(1).copied());
            }
            "ObjectPropertyAssertion" => {
                self.logical_abox(head);
                self.stats.role_assertions += 1;
                if let Some(r) = args.first() {
                    self.object_role(r);
                }
                self.individual_arg(args.get(1).copied());
                self.individual_arg(args.get(2).copied());
            }
            "NegativeObjectPropertyAssertion" => {
                self.logical_abox(head);
                self.stats.role_assertions += 1;
                // Konclude rewrites a negative role assertion through nominal
                // value concepts (official probe: ALOI+).
                self.expr.nominal_individual = true;
                self.nominal_unconditional = true;
                self.nominal_from_abox = true;
                if let Some(r) = args.first() {
                    self.object_role(r);
                }
                self.individual_arg(args.get(1).copied());
                self.individual_arg(args.get(2).copied());
            }
            "DataPropertyAssertion" => {
                self.logical_abox(head);
                self.stats.role_assertions += 1;
                if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                    self.data_properties.insert(r);
                }
                self.individual_arg(args.get(1).copied());
            }
            "NegativeDataPropertyAssertion" => {
                self.logical_abox(head);
                self.stats.role_assertions += 1;
                self.expr.datatype = true;
                self.expr.negation_disjunction = true;
                if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                    self.data_properties.insert(r);
                }
                self.individual_arg(args.get(1).copied());
            }
            "SameIndividual" | "DifferentIndividuals" => {
                self.logical_abox(head);
                self.expr.nominal_individual = true;
                self.nominal_unconditional = true;
                self.nominal_from_abox = true;
                self.expr.negation_disjunction = true;
                for n in &args {
                    self.individual_arg(Some(*n));
                }
            }
            "DLSafeRule" => {
                self.stats.logical_axioms += 1;
                self.stats.rule_axioms += 1;
                // `V` is Konclude's variable-binding grounding occurrence, not
                // the mere presence of a DL-safe rule. A simple class rule is
                // preprocessed away for this summary (official probe: ALI+).
                if !self.rule_atoms(&args) {
                    self.stats.unsupported_rule_axioms += 1;
                }
            }
            _ => {}
        }
    }

    pub fn finish(mut self, file_bytes: u64) -> OntologyProfile {
        self.stats.file_bytes = file_bytes;
        self.stats.declared_classes = self.declared_classes.len() as u64;
        self.stats.declared_object_properties = self.declared_object_properties.len() as u64;
        self.stats.declared_data_properties = self.declared_data_properties.len() as u64;
        self.stats.declared_named_individuals = self.declared_individuals.len() as u64;
        self.stats.distinct_classes = self.classes.len() as u64;
        self.stats.distinct_object_properties = self.object_properties.len() as u64;
        self.stats.distinct_data_properties = self.data_properties.len() as u64;
        self.stats.distinct_individuals = self.individuals.len() as u64;
        self.stats.axiom_types = self
            .axiom_types
            .into_iter()
            .map(|(kind, count)| (kind.to_string(), count))
            .collect();
        // An absorbable `A = exists r.B` is represented as an ALE primitive
        // definition only while A has no separate primitive inclusion.  Once
        // both forms occur, Konclude retains a CCEQ operand (official witness:
        // `EquivalentClasses(A Some(r,B)); SubClassOf(A B)` -> SI).
        if self
            .existential_definition_lhs
            .iter()
            .any(|name| self.subclass_lhs.contains(name))
        {
            self.expr.negation_disjunction = true;
        }
        // Sharing one inverse role between two distinct partners induces an
        // ordinary role equivalence in Konclude's role linker, which also
        // contributes H even though the source has no explicit subrole axiom.
        if self
            .inverse_partners
            .values()
            .any(|partners| partners.len() > 1)
        {
            self.expr.role_hierarchy = true;
            self.object_role_hierarchy = true;
        }
        // With an explicit inverse pair, an ordinary role inclusion causes
        // Konclude's RBox preprocessing to materialize a non-trigger negative
        // automata operand as soon as an existential is live. The three-axiom
        // corpus witness is retained in the benchmark artifacts (7417).
        if self.explicit_inverse_relation && self.object_role_hierarchy && self.expr.existential {
            self.expr.negation_disjunction = true;
        }
        // Konclude's transitivity preprocessing contributes a negative concept
        // only when that exact role occurs in a live class restriction. An
        // unused transitive declaration still contributes `+`, and using only
        // a proper subrole does not activate the negative operand.
        if self
            .transitive_roles
            .iter()
            .any(|r| self.restriction_roles.contains(r))
        {
            self.expr.negation_disjunction = true;
        }
        // A non-trivial chain makes `hasRoleChainSuperSharing()` take the
        // complex-chain branch. Konclude then reports SR without `+`, even if
        // a different role has an explicit transitivity declaration.
        if self.expr.complex_subrole {
            self.expr.transitivity = false;
        }
        // Domain/range concepts are reached from the active concept graph only
        // when their role occurs in a live restriction. Preserve the raw
        // nominal-individual occurrence separately, but add O only for a
        // reachable nominal (COntologyInspector::analyseConceptStructureFlags).
        let conditional_nominal_reached = self
            .conditional_nominal_roles
            .iter()
            .any(|role| self.restriction_roles.contains(role));
        self.expr.nominal = self.nominal_unconditional || conditional_nominal_reached;
        // Structure inspection deliberately replaces the raw nominal flag by
        // an active-concept traversal result. DL-safe rule preprocessing makes
        // that traversal stop before all nominal concepts. An unabsorbed union
        // equivalence does the same for nominals introduced only by ABox
        // equality/difference assertions. Both behaviors are direct official
        // Konclude witnesses, not a source-language approximation.
        if self.stats.rule_axioms > 0
            || (self.union_equivalence
                && self.nominal_from_abox
                && !self.nominal_from_concept
                && !conditional_nominal_reached)
        {
            self.expr.nominal = false;
        }
        if conditional_nominal_reached {
            // A reached nominal-valued role domain is internalized through a
            // non-trigger negative operand (official witness: SOI).
            self.expr.negation_disjunction = true;
        }
        self.expr.finish();
        let positive_abox_tbox_separable = positive_abox_tbox_separable(&self.stats, &self.expr);
        OntologyProfile {
            schema_version: 2,
            positive_abox_tbox_separable,
            expressivity: self.expr,
            source: self.stats,
            clauses: ClauseStatistics::default(),
        }
    }

    fn declaration(&mut self, args: &[&Node<'a>]) {
        self.stats.declarations += 1;
        let Some(Node::List(kind, values)) = args.first().copied() else {
            return;
        };
        let Some(name) = values.first().and_then(Node::as_atom) else {
            return;
        };
        match *kind {
            "Class" | "Datatype" => {
                if *kind == "Class" {
                    self.declared_classes.insert(name);
                    self.classes.insert(name);
                }
            }
            "ObjectProperty" => {
                self.declared_object_properties.insert(name);
                self.object_properties.insert(name);
            }
            "DataProperty" => {
                self.declared_data_properties.insert(name);
                self.data_properties.insert(name);
            }
            "NamedIndividual" => {
                self.declared_individuals.insert(name);
                self.individuals.insert(name);
            }
            _ => {}
        }
    }

    fn logical_tbox(&mut self, _head: &str) {
        self.stats.logical_axioms += 1;
        self.stats.tbox_axioms += 1;
    }
    fn logical_rbox(&mut self, _head: &str) {
        self.stats.logical_axioms += 1;
        self.stats.rbox_axioms += 1;
    }
    fn logical_abox(&mut self, _head: &str) {
        self.stats.logical_axioms += 1;
        self.stats.abox_axioms += 1;
    }

    fn concepts(&mut self, args: &[&Node<'a>]) {
        for c in args {
            self.concept(c, 1);
        }
    }

    fn concept(&mut self, node: &Node<'a>, depth: u64) {
        self.stats.concept_expressions += 1;
        self.stats.max_concept_depth = self.stats.max_concept_depth.max(depth);
        match node {
            Node::Atom(name) => {
                if is_bottom(name) {
                    self.stats.bottom_occurrences += 1;
                } else if !is_top(name) {
                    self.classes.insert(name);
                }
            }
            Node::List(head, raw_args) => {
                let args: SmallVec<[&Node<'a>; 4]> = raw_args
                    .iter()
                    .filter(|n| n.head() != Some("Annotation"))
                    .collect();
                self.stats.max_concept_arity = self.stats.max_concept_arity.max(args.len() as u64);
                match *head {
                    "ObjectIntersectionOf" => {
                        self.stats.intersections += 1;
                        self.concepts_at(&args, depth + 1);
                    }
                    "ObjectUnionOf" => {
                        self.stats.unions += 1;
                        self.expr.negation_disjunction = true;
                        self.concepts_at(&args, depth + 1);
                    }
                    "ObjectComplementOf" => {
                        self.stats.complements += 1;
                        self.expr.negation_disjunction = true;
                        self.concepts_at(&args, depth + 1);
                    }
                    "ObjectSomeValuesFrom" => {
                        self.stats.existentials += 1;
                        let universal = args.first().is_some_and(|r| role_is_universal(r));
                        if universal {
                            // Konclude's top-role connection is represented by
                            // a nondeterministic universal-connection concept,
                            // not a CCSOME occurrence (official probe: SI).
                            self.expr.negation_disjunction = true;
                        } else {
                            self.expr.existential = true;
                        }
                        if let Some(r) = args.first() {
                            self.concept_object_role(r);
                        }
                        if let Some(c) = args.get(1) {
                            self.concept(c, depth + 1);
                        }
                    }
                    "ObjectAllValuesFrom" => {
                        self.stats.universals += 1;
                        let universal = args.first().is_some_and(|r| role_is_universal(r));
                        if universal {
                            self.expr.negation_disjunction = true;
                        } else {
                            // Konclude names this flag `ExistensialOccurrence`
                            // but sets it for CCALL as well as CCSOME.
                            self.expr.existential = true;
                        }
                        if let Some(r) = args.first() {
                            self.concept_object_role(r);
                        }
                        if let Some(c) = args.get(1) {
                            self.concept(c, depth + 1);
                        }
                    }
                    "ObjectMinCardinality" => self.cardinality(&args, depth, CardKind::Min, false),
                    "ObjectMaxCardinality" => self.cardinality(&args, depth, CardKind::Max, false),
                    "ObjectExactCardinality" => {
                        self.cardinality(&args, depth, CardKind::Exact, false)
                    }
                    "ObjectOneOf" => {
                        self.stats.nominals += args.len() as u64;
                        self.expr.nominal_individual = true;
                        self.record_nominal_origin();
                        self.expr.negation_disjunction = true;
                        for n in args {
                            self.individual_arg(Some(n));
                        }
                    }
                    "ObjectHasValue" => {
                        self.stats.has_values += 1;
                        self.expr.nominal_individual = true;
                        self.record_nominal_origin();
                        if let Some(r) = args.first() {
                            self.concept_object_role(r);
                        }
                        self.individual_arg(args.get(1).copied());
                    }
                    "ObjectHasSelf" => {
                        self.stats.has_self += 1;
                        if let Some(r) = args.first() {
                            self.concept_object_role(r);
                        }
                    }
                    "DataSomeValuesFrom" => {
                        self.stats.existentials += 1;
                        self.stats.datatype_constructors += 1;
                        self.expr.existential = true;
                        self.expr.datatype = true;
                        self.data_role_and_ranges(&args);
                    }
                    "DataAllValuesFrom" => {
                        self.stats.universals += 1;
                        self.stats.datatype_constructors += 1;
                        self.expr.existential = true;
                        self.expr.datatype = true;
                        self.data_role_and_ranges(&args);
                    }
                    "DataHasValue" => {
                        self.stats.has_values += 1;
                        self.stats.datatype_constructors += 1;
                        self.expr.datatype = true;
                        self.expr.negation_disjunction = true;
                        if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                            self.data_properties.insert(r);
                        }
                    }
                    "DataMinCardinality" => self.cardinality(&args, depth, CardKind::Min, true),
                    "DataMaxCardinality" => self.cardinality(&args, depth, CardKind::Max, true),
                    "DataExactCardinality" => self.cardinality(&args, depth, CardKind::Exact, true),
                    _ if head.starts_with("Data") => {
                        self.stats.datatype_constructors += 1;
                        self.expr.datatype = true;
                        for n in args {
                            self.data_range(n);
                        }
                    }
                    _ => {
                        // Preserve nested known class expressions in extensions
                        // without interpreting arbitrary atoms as class names.
                        for n in args {
                            if matches!(n, Node::List(..)) {
                                self.concept(n, depth + 1);
                            }
                        }
                    }
                }
            }
        }
    }

    fn concepts_at(&mut self, args: &[&Node<'a>], depth: u64) {
        for c in args {
            self.concept(c, depth);
        }
    }

    fn record_nominal_origin(&mut self) {
        if let Some(role) = self.conditional_nominal_role {
            self.conditional_nominal_roles.insert(role);
        } else {
            self.nominal_unconditional = true;
            self.nominal_from_concept = true;
        }
    }

    fn cardinality(&mut self, args: &[&Node<'a>], depth: u64, kind: CardKind, data: bool) {
        match kind {
            CardKind::Min => self.stats.min_cardinalities += 1,
            CardKind::Max => self.stats.max_cardinalities += 1,
            CardKind::Exact => self.stats.exact_cardinalities += 1,
        }
        if data {
            self.expr.datatype = true;
        }
        let n = args
            .first()
            .and_then(|n| n.as_atom())
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        self.stats.max_cardinality = self.stats.max_cardinality.max(n);
        let qualified = args.get(2).is_some_and(|f| !node_is_top(f, data));
        if qualified {
            self.stats.qualified_cardinalities += 1;
        } else {
            self.stats.unqualified_cardinalities += 1;
        }

        // This mirrors Konclude after preprocessing rather than just mapping
        // OWL constructor names. In particular, `=1` and `<=0` are rewritten
        // through nondeterministic concepts, while a plain `<=1` remains F.
        match (kind, n) {
            (CardKind::Min, 1) => self.expr.existential = true,
            (CardKind::Min, _) => {
                self.expr.existential = true;
                if qualified {
                    self.expr.qualified_cardinality = true;
                } else {
                    self.expr.cardinality = true;
                }
            }
            (CardKind::Max, 0) => self.expr.negation_disjunction = true,
            (CardKind::Max, 1) => self.expr.functionality = true,
            (CardKind::Max, _) => {
                if qualified {
                    self.expr.qualified_cardinality = true;
                } else {
                    self.expr.cardinality = true;
                }
            }
            (CardKind::Exact, 1) => {
                self.expr.negation_disjunction = true;
                self.expr.functionality = true;
            }
            (CardKind::Exact, _) => {
                self.expr.existential = true;
                if qualified {
                    self.expr.qualified_cardinality = true;
                } else {
                    self.expr.cardinality = true;
                }
            }
        }
        if let Some(role) = args.get(1) {
            if data {
                if let Some(r) = role.as_atom() {
                    self.data_properties.insert(r);
                }
            } else {
                self.concept_object_role(role);
            }
        }
        if let Some(filler) = args.get(2) {
            if data {
                self.data_range(filler);
            } else {
                self.concept(filler, depth + 1);
            }
        }
    }

    fn object_roles(&mut self, args: &[&Node<'a>]) {
        for r in args {
            self.object_role(r);
        }
    }
    fn concept_object_role(&mut self, node: &Node<'a>) {
        match node {
            Node::Atom(role) if !is_universal_role(role) => {
                self.restriction_roles.insert(role);
            }
            Node::List(head, args) if *head == "ObjectInverseOf" => {
                if let Some(role) = args.first().and_then(Node::as_atom) {
                    self.restriction_roles.insert(role);
                }
            }
            _ => {}
        }
        self.object_role(node);
    }
    fn object_role(&mut self, node: &Node<'a>) {
        match node {
            Node::Atom(r) => {
                if is_universal_role(r) {
                    self.expr.universal_role = true;
                } else {
                    self.object_properties.insert(r);
                }
            }
            Node::List(h, args) if *h == "ObjectInverseOf" => {
                self.expr.inverse = true;
                if let Some(r) = args.first().and_then(Node::as_atom) {
                    self.object_properties.insert(r);
                }
            }
            _ => {}
        }
    }
    fn data_roles(&mut self, args: &[&Node<'a>]) {
        for r in args {
            if let Some(r) = r.as_atom() {
                self.data_properties.insert(r);
            }
        }
    }
    fn data_role_and_ranges(&mut self, args: &[&Node<'a>]) {
        if let Some(r) = args.first().and_then(|n| n.as_atom()) {
            self.data_properties.insert(r);
        }
        for d in args.iter().skip(1) {
            self.data_range(d);
        }
    }
    fn data_range(&mut self, node: &Node<'a>) {
        self.expr.datatype = true;
        if let Node::List(_, args) = node {
            for n in args {
                if matches!(n, Node::List(..)) {
                    self.data_range(n);
                }
            }
        }
    }
    fn individual_arg(&mut self, node: Option<&Node<'a>>) {
        if let Some(Node::Atom(i)) = node {
            if !i.starts_with('"') {
                self.individuals.insert(i);
            }
        }
    }
    fn key_properties(&mut self, node: &Node<'a>) {
        match node {
            Node::List(h, args) if *h == "ObjectPropertyChain" => {
                for r in args {
                    self.object_role(r);
                }
            }
            Node::List(h, args) if h.contains("Data") => {
                self.expr.datatype = true;
                for r in args {
                    if let Some(r) = r.as_atom() {
                        self.data_properties.insert(r);
                    }
                }
            }
            Node::List(_, args) => {
                for r in args {
                    self.object_role(r);
                }
            }
            Node::Atom(r) => {
                self.object_properties.insert(r);
            }
        }
    }
    fn rule_atoms(&mut self, args: &[&Node<'a>]) -> bool {
        fn walk<'a>(this: &mut SourceProfileBuilder<'a>, node: &Node<'a>) {
            if let Node::List(h, args) = node {
                match *h {
                    "ClassAtom" => {
                        if let Some(c) = args.first() {
                            this.concept(c, 1);
                        }
                    }
                    "ObjectPropertyAtom" => {
                        if let Some(r) = args.first() {
                            this.object_role(r);
                        }
                    }
                    "DataPropertyAtom" | "DataRangeAtom" | "BuiltInAtom" => {
                        this.expr.datatype = true;
                    }
                    _ => {}
                }
                for n in args {
                    walk(this, n);
                }
            }
        }
        for n in args {
            walk(self, n);
        }

        fn term_supported(node: Option<&Node<'_>>) -> bool {
            matches!(node, Some(Node::Atom(_)))
                || matches!(
                    node,
                    Some(Node::List(head, values))
                        if *head == "Variable"
                            && values.first().is_some_and(|value| value.as_atom().is_some())
                )
        }
        fn group_supported(node: &Node<'_>, require_nonempty: bool) -> bool {
            let Node::List(_, atoms) = node else {
                return false;
            };
            let atoms: Vec<_> = atoms
                .iter()
                .filter(|atom| atom.head() != Some("Annotation"))
                .collect();
            if require_nonempty && atoms.is_empty() {
                return false;
            }
            atoms.into_iter().all(|atom| {
                let Node::List(head, values) = atom else {
                    return false;
                };
                match *head {
                    "ClassAtom" => {
                        values
                            .first()
                            .is_some_and(|value| value.as_atom().is_some())
                            && term_supported(values.get(1))
                    }
                    "ObjectPropertyAtom" => {
                        values
                            .first()
                            .is_some_and(|value| value.as_atom().is_some())
                            && term_supported(values.get(1))
                            && term_supported(values.get(2))
                    }
                    "DifferentIndividualsAtom" | "SameIndividualAtom" => {
                        term_supported(values.first()) && term_supported(values.get(1))
                    }
                    _ => false,
                }
            })
        }

        let body = args.iter().find(|node| node.head() == Some("Body"));
        let head = args.iter().find(|node| node.head() == Some("Head"));
        matches!((body, head), (Some(body), Some(head))
            if group_supported(body, false) && group_supported(head, true))
    }
}

/// Prove that an ABox may be omitted while classifying named TBox concepts.
///
/// The accepted source fragment has only positive assertions and a TBox/RBox
/// with no negative constraint, number restriction, nominal, datatype
/// constraint, or universal role. Interpret every named class and object role
/// as full and every individual as one domain element. This is a model of the
/// TBox and every positive assertion, so consistency is guaranteed. Moreover,
/// nominal-free SRIQ without the universal role is preserved by disjoint
/// unions. A countermodel to a TBox subsumption can therefore be disjointly
/// united with that positive ABox model, proving that the ABox adds no TBox
/// subsumption.
///
/// This mirrors the purpose of Konclude's all-assertion-individual consistency
/// precomputation, but accepts only the syntactic case where that consistency
/// result follows immediately. Every uncertain constructor fails closed onto
/// KM's exact nominal/ABox calculus.
fn positive_abox_tbox_separable(source: &SourceStatistics, expr: &ExpressivityProfile) -> bool {
    // This is deliberately a whitelist, not a blacklist. The functional-syntax
    // frontend skips several out-of-core axiom kinds soundly for ordinary TBox
    // classification. Such a skipped axiom must never accidentally become a
    // proof that dropping an ABox is complete. Imports also fail this test: the
    // certificate covers this parsed ontology only, not an external closure.
    const SAFE_AXIOMS: &[&str] = &[
        "Declaration",
        "Annotation",
        "AnnotationAssertion",
        "SubAnnotationPropertyOf",
        "AnnotationPropertyDomain",
        "AnnotationPropertyRange",
        "SubClassOf",
        "EquivalentClasses",
        "SubObjectPropertyOf",
        "EquivalentObjectProperties",
        "InverseObjectProperties",
        "TransitiveObjectProperty",
        "SymmetricObjectProperty",
        "FunctionalObjectProperty",
        "InverseFunctionalObjectProperty",
        "ReflexiveObjectProperty",
        "ObjectPropertyDomain",
        "ObjectPropertyRange",
        "SubDataPropertyOf",
        "EquivalentDataProperties",
        "DataPropertyDomain",
        "ClassAssertion",
        "ObjectPropertyAssertion",
        // Data ranges and data-property constraints require the concrete-domain
        // consistency procedure. Bare positive data assertions are harmless.
        "DataPropertyAssertion",
    ];

    source.abox_axioms > 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.bottom_occurrences == 0
        && source.bottom_role_occurrences == 0
        && source.complements == 0
        && source.disjoint_class_axioms == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && !expr.nominal_individual
        && !expr.universal_role
        && !expr.datatype
        && !expr.grounding
        && source.imports == 0
        && source
            .axiom_types
            .keys()
            .all(|kind| SAFE_AXIOMS.contains(&kind.as_str()))
}

#[derive(Clone, Copy)]
enum CardKind {
    Min,
    Max,
    Exact,
}

fn is_top(s: &str) -> bool {
    matches!(s, "owl:Thing" | "<http://www.w3.org/2002/07/owl#Thing>")
}
fn is_bottom(s: &str) -> bool {
    matches!(s, "owl:Nothing" | "<http://www.w3.org/2002/07/owl#Nothing>")
}
fn is_bottom_role(s: &str) -> bool {
    matches!(
        s,
        "owl:bottomObjectProperty"
            | "owl:bottomDataProperty"
            | "<http://www.w3.org/2002/07/owl#bottomObjectProperty>"
            | "<http://www.w3.org/2002/07/owl#bottomDataProperty>"
    )
}
fn bottom_role_occurrences(node: &Node<'_>) -> u64 {
    match node {
        Node::Atom(value) => u64::from(is_bottom_role(value)),
        Node::List(head, _) if *head == "Annotation" => 0,
        Node::List(_, args) => args.iter().map(bottom_role_occurrences).sum(),
    }
}
fn is_universal_role(s: &str) -> bool {
    matches!(
        s,
        "owl:topObjectProperty" | "<http://www.w3.org/2002/07/owl#topObjectProperty>"
    )
}
fn role_is_universal(node: &Node<'_>) -> bool {
    node.as_atom().is_some_and(is_universal_role)
}
fn node_is_top(n: &Node<'_>, data: bool) -> bool {
    n.as_atom().is_some_and(|s| {
        if data {
            matches!(
                s,
                "rdfs:Literal" | "<http://www.w3.org/2000/01/rdf-schema#Literal>"
            )
        } else {
            is_top(s)
        }
    })
}

fn term_flags(term: &crate::json_io::JTerm) -> (bool, bool) {
    use crate::json_io::JTerm;
    (
        matches!(term, JTerm::Fun { .. }),
        matches!(term, JTerm::Aux { .. }),
    )
}

/// Compute normalized-clause statistics in one borrowed pass over the final
/// clause vector.  No clause or symbol strings are cloned.
pub fn clause_statistics(clauses: &[crate::json_io::JClause]) -> ClauseStatistics {
    use crate::json_io::JAtom;
    let mut out = ClauseStatistics::default();
    let mut concepts: HashSet<&str> = HashSet::new();
    let mut roles: HashSet<&str> = HashSet::new();
    let mut top_pairs: HashSet<(&str, &str)> = HashSet::new();
    let mut bottom_pairs: HashSet<(&str, &str)> = HashSet::new();
    let mut body_concepts: SmallVec<[&str; 4]> = SmallVec::new();
    let mut head_concepts: SmallVec<[&str; 4]> = SmallVec::new();
    let mut body_roles: SmallVec<[&str; 4]> = SmallVec::new();
    let mut head_roles: SmallVec<[&str; 4]> = SmallVec::new();

    for clause in clauses {
        out.clauses += 1;
        out.body_atoms += clause.body.len() as u64;
        out.head_atoms += clause.head.len() as u64;
        out.max_body_atoms = out.max_body_atoms.max(clause.body.len() as u64);
        out.max_head_atoms = out.max_head_atoms.max(clause.head.len() as u64);
        if clause.body.is_empty() {
            out.empty_body_clauses += 1;
        }
        if clause.head.is_empty() {
            out.empty_head_clauses += 1;
        }
        body_concepts.clear();
        head_concepts.clear();
        body_roles.clear();
        head_roles.clear();
        let mut has_fun = false;
        let mut has_aux = false;
        for atom in clause.body.iter().chain(clause.head.iter()) {
            match atom {
                JAtom::Concept { concept, term } => {
                    concepts.insert(concept);
                    let (f, a) = term_flags(term);
                    has_fun |= f;
                    has_aux |= a;
                }
                JAtom::Role {
                    role,
                    source,
                    target,
                } => {
                    roles.insert(role);
                    for term in [source, target] {
                        let (f, a) = term_flags(term);
                        has_fun |= f;
                        has_aux |= a;
                    }
                }
                JAtom::Eq { .. } => out.equality_atoms += 1,
            }
        }
        for atom in &clause.body {
            match atom {
                JAtom::Concept { concept, .. } => body_concepts.push(concept.as_str()),
                JAtom::Role { role, .. } => body_roles.push(role.as_str()),
                _ => {}
            }
        }
        for atom in &clause.head {
            match atom {
                JAtom::Concept { concept, .. } => head_concepts.push(concept.as_str()),
                JAtom::Role { role, .. } => head_roles.push(role.as_str()),
                _ => {}
            }
        }
        if has_fun {
            out.clauses_with_function_terms += 1;
        }
        if has_aux {
            out.clauses_with_aux_terms += 1;
        }
        if head_concepts.len() <= 1 {
            out.horn_clauses += 1;
        } else {
            out.disjunctive_clauses += 1;
            out.max_disjunction_width = out.max_disjunction_width.max(head_concepts.len() as u64);
        }
        if clause.body.is_empty() && head_concepts.len() == 2 {
            out.binary_top_disjunctions += 1;
            top_pairs.insert(ordered_pair(head_concepts[0], head_concepts[1]));
        }
        if clause.head.is_empty() && body_concepts.len() == 2 {
            out.binary_bottom_clauses += 1;
            bottom_pairs.insert(ordered_pair(body_concepts[0], body_concepts[1]));
        }
        if body_roles.len() == 2 && head_roles.len() == 1 && head_concepts.is_empty() {
            out.role_chain_clauses += 1;
            if body_roles[0] == head_roles[0] && body_roles[1] == head_roles[0] {
                out.transitivity_clauses += 1;
            }
        }
    }
    out.concept_symbols = concepts.len() as u64;
    out.role_symbols = roles.len() as u64;
    out.complementary_definers = top_pairs.intersection(&bottom_pairs).count() as u64;
    out
}

fn ordered_pair<'a>(a: &'a str, b: &'a str) -> (&'a str, &'a str) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parse;

    fn source(text: &str) -> OntologyProfile {
        let mut builder = SourceProfileBuilder::new();
        parse::for_each_ontology_child(text, |n| {
            builder.observe(n);
            Ok(())
        })
        .unwrap();
        builder.finish(text.len() as u64)
    }

    #[test]
    fn konclude_code_precedence_is_exact() {
        let mut e = ExpressivityProfile {
            negation_disjunction: true,
            transitivity: true,
            role_hierarchy: true,
            nominal: true,
            inverse: true,
            functionality: true,
            datatype: true,
            ..Default::default()
        };
        assert_eq!(e.calculate_code(), "SHOIF(D)");
        e.complex_subrole = true;
        e.qualified_cardinality = true;
        assert_eq!(e.calculate_code(), "SROIQ(D)");
    }

    #[test]
    fn parsed_constructs_drive_expressivity_not_text_tokens() {
        let p = source(
            r#"Ontology(
              AnnotationAssertion(rdfs:comment <x> "ObjectUnionOf(")
              SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>))
              SubObjectPropertyOf(<r> <s>)
              TransitiveObjectProperty(<s>)
            )"#,
        );
        assert_eq!(p.expressivity.code, "ALEHI+");
        assert!(!p.expressivity.negation_disjunction);
        assert_eq!(p.source.existentials, 1);
        assert_eq!(p.source.logical_axioms, 3);
    }

    #[test]
    fn positive_abox_tbox_separation_certificate_fails_closed() {
        let positive = source(
            r#"Ontology(
              SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>))
              FunctionalObjectProperty(<r>)
              ClassAssertion(<A> <a>)
              ObjectPropertyAssertion(<r> <a> <b>)
              DataPropertyAssertion(<p> <a> "value")
            )"#,
        );
        assert_eq!(positive.schema_version, 2);
        assert_eq!(positive.source.bottom_occurrences, 0);
        assert!(positive.positive_abox_tbox_separable);

        for unsafe_source in [
            "Ontology(SubClassOf(<A> owl:Nothing) ClassAssertion(<A> <a>))",
            "Ontology(DisjointClasses(<A> <B>) ClassAssertion(<A> <a>))",
            "Ontology(SubClassOf(<A> ObjectOneOf(<a>)) ClassAssertion(<A> <a>))",
            "Ontology(DifferentIndividuals(<a> <b>) ClassAssertion(<A> <a>))",
            "Ontology(DataPropertyRange(<p> xsd:string) DataPropertyAssertion(<p> <a> \"x\"))",
            "Ontology(SubClassOf(<A> ObjectAllValuesFrom(owl:topObjectProperty <B>)) ClassAssertion(<A> <a>))",
            "Ontology(ObjectPropertyAssertion(owl:bottomObjectProperty <a> <b>))",
            "Ontology(Import(<http://example.org/imported>) ClassAssertion(<A> <a>))",
            "Ontology(NegativeClassAssertion(<A> <a>) ClassAssertion(<B> <a>))",
            "Ontology(UnsupportedLogicalAxiom(<A> <B>) ClassAssertion(<A> <a>))",
        ] {
            assert!(
                !source(unsafe_source).positive_abox_tbox_separable,
                "unsafe source was certified: {unsafe_source}"
            );
        }
        assert_eq!(
            source("Ontology(SubClassOf(<A> owl:Nothing) ClassAssertion(<A> <a>))")
                .source
                .bottom_occurrences,
            1
        );
        assert_eq!(
            source("Ontology(ObjectPropertyAssertion(owl:bottomObjectProperty <a> <b>))")
                .source
                .bottom_role_occurrences,
            1
        );
    }

    #[test]
    fn cardinality_matches_konclude_q_n_f_precedence() {
        let f = source("Ontology(SubClassOf(<A> ObjectMaxCardinality(1 <r> <B>)))");
        assert_eq!(f.expressivity.code, "ALIF+");
        let q = source("Ontology(SubClassOf(<A> ObjectMinCardinality(2 <r> <B>)))");
        assert_eq!(q.expressivity.code, "ALEIQ+");
        let n = source("Ontology(SubClassOf(<A> ObjectMaxCardinality(3 <r>)))");
        assert_eq!(n.expressivity.code, "ALIN+");
        let zero = source("Ontology(SubClassOf(<A> ObjectMaxCardinality(0 <r> <B>)))");
        assert_eq!(zero.expressivity.code, "SI");
        let exact_one = source("Ontology(SubClassOf(<A> ObjectExactCardinality(1 <r> <B>)))");
        assert_eq!(exact_one.expressivity.code, "SIF");
    }

    #[test]
    fn post_preprocessing_axiom_flags_match_official_konclude() {
        assert_eq!(
            source("Ontology(EquivalentClasses(<A> <B>))")
                .expressivity
                .code,
            "ALI+"
        );
        assert_eq!(
            source("Ontology(DisjointClasses(<A> <B>))")
                .expressivity
                .code,
            "SI"
        );
        assert_eq!(
            source("Ontology(ObjectPropertyDomain(<r> <A>))")
                .expressivity
                .code,
            "ALI+"
        );
        assert_eq!(
            source("Ontology(DifferentIndividuals(<i> <j>))")
                .expressivity
                .code,
            "SOI"
        );
        assert_eq!(
            source("Ontology(SubClassOf(<A> ObjectSomeValuesFrom(owl:topObjectProperty <A>)))",)
                .expressivity
                .code,
            "SI"
        );
        assert_eq!(
            source("Ontology(DataPropertyAssertion(<p> <i> \"1\"^^xsd:integer))")
                .expressivity
                .code,
            "ALI+"
        );
        assert_eq!(
            source("Ontology(NegativeDataPropertyAssertion(<p> <i> \"1\"^^xsd:integer))")
                .expressivity
                .code,
            "SI(D)"
        );
        assert_eq!(
            source("Ontology(SubClassOf(ObjectSomeValuesFrom(<r> <B>) <A>))")
                .expressivity
                .code,
            "SI"
        );
        assert_eq!(
            source("Ontology(EquivalentClasses(<A> ObjectIntersectionOf(<B> <C>)))")
                .expressivity
                .code,
            "SI"
        );
        assert_eq!(
            source(
                "Ontology(TransitiveObjectProperty(<r>) SubClassOf(<A> ObjectSomeValuesFrom(<s> <B>)))",
            )
            .expressivity
            .code,
            "ALEI+"
        );
        assert_eq!(
            source(
                "Ontology(TransitiveObjectProperty(<r>) SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>)))",
            )
            .expressivity
            .code,
            "SI"
        );
    }

    #[test]
    fn post_preprocessing_reachability_matches_official_witnesses() {
        assert_eq!(
            source(
                "Ontology(EquivalentClasses(<A> ObjectSomeValuesFrom(<r> <B>)) SubClassOf(<A> <B>))",
            )
            .expressivity
            .code,
            "SI"
        );
        assert_eq!(
            source("Ontology(InverseObjectProperties(<r> <s>) InverseObjectProperties(<r> <t>))",)
                .expressivity
                .code,
            "ALHI+"
        );
        assert_eq!(
            source(
                "Ontology(SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>)) InverseObjectProperties(<s> <t>) SubObjectPropertyOf(<u> <v>))",
            )
            .expressivity
            .code,
            "SHI"
        );
        assert_eq!(
            source(
                "Ontology(EquivalentClasses(<A> ObjectOneOf(<i>)) DLSafeRule(Body(ClassAtom(<A> Variable(<x>))) Head(ClassAtom(<B> Variable(<x>)))))",
            )
            .expressivity
            .code,
            "SI"
        );
        assert_eq!(
            source(
                "Ontology(EquivalentClasses(<A> ObjectUnionOf(<B> <C>)) DifferentIndividuals(<i> <j>))",
            )
            .expressivity
            .code,
            "SI"
        );
        assert_eq!(
            source("Ontology(ObjectPropertyDomain(<r> ObjectHasValue(<s> <i>)))")
                .expressivity
                .code,
            "ALI+"
        );
        assert_eq!(
            source(
                "Ontology(ObjectPropertyDomain(<r> ObjectHasValue(<s> <i>)) SubClassOf(<A> ObjectSomeValuesFrom(<r> owl:Thing)))",
            )
            .expressivity
            .code,
            "SOI"
        );
    }

    #[test]
    fn rule_representability_is_profiled_before_routing() {
        let supported = source(
            "Ontology(DLSafeRule(Body(ClassAtom(<A> Variable(<x>)) ObjectPropertyAtom(<r> Variable(<x>) <i>)) Head(ClassAtom(<B> Variable(<x>)))))",
        );
        assert_eq!(supported.source.rule_axioms, 1);
        assert_eq!(supported.source.unsupported_rule_axioms, 0);

        for text in [
            "Ontology(DLSafeRule(Body(BuiltInAtom(<p> Variable(<x>))) Head(ClassAtom(<B> Variable(<x>)))))",
            "Ontology(DLSafeRule(Body(ClassAtom(ObjectIntersectionOf(<A> <B>) Variable(<x>))) Head(ClassAtom(<C> Variable(<x>)))))",
            "Ontology(DLSafeRule(Body(ClassAtom(<A> Variable(<x>))) Head()))",
        ] {
            let unsupported = source(text);
            assert_eq!(unsupported.source.rule_axioms, 1);
            assert_eq!(unsupported.source.unsupported_rule_axioms, 1);
        }
    }

    #[test]
    fn complex_chain_replaces_base_with_sr() {
        let p = source(
            "Ontology(SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>) TransitiveObjectProperty(<u>) InverseObjectProperties(<t> <v>))",
        );
        assert_eq!(p.expressivity.code, "SRI");
        assert_eq!(p.source.role_chain_axioms, 1);
        assert_eq!(p.source.max_role_chain_length, 2);
    }
}
