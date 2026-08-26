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
    /// Distinct normalized Skolem-function names. Together with
    /// `individual_term_symbols`, this selects a lossless `f(o)` term layout
    /// for nominal CB workers.
    #[serde(default)]
    pub function_term_symbols: u64,
    /// Distinct normalized named-individual term names.
    #[serde(default)]
    pub individual_term_symbols: u64,
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
    /// Source-only admission gate for exact EL++ ABox materialisation. Unlike
    /// `positive_abox_tbox_separable`, this permits bottom constraints: the
    /// orchestrator must run the EL canonical-model consistency certificate
    /// before it may publish the nominal-free taxonomy.
    #[serde(default)]
    pub positive_el_abox_materializable: bool,
    /// Source-only admission gate for the disjoint-union ABox projection. This
    /// is not itself a consistency certificate: the orchestrator must first
    /// obtain an exact full-ontology consistency verdict. The gate excludes
    /// every constructor that can connect otherwise disjoint model components
    /// through a concept nominal, universal role, key, import, or rule.
    #[serde(default)]
    pub disjoint_union_abox_candidate: bool,
    /// Source-only certificate for the inverse-aware cardinality route. Every
    /// object role used by a number restriction (including functionality) is
    /// in a role-hierarchy component disjoint from inverse/symmetric and
    /// non-simple (chain/transitive) roles. `ObjectInverseOf` role expressions
    /// and inverse functionality fail closed, and at least one explicit object
    /// cardinality must supply first-class CardMeta. The inverse axioms are
    /// still processed exactly; this certificate only establishes that
    /// Konclude's NN/NI nominal-predecessor rule has no number-role premise.
    #[serde(default)]
    pub inverse_cardinality_role_separable: bool,
    /// The number-role half of the certificate above, WITHOUT the native-ABox
    /// materialization conditions. It is the exact precondition of the
    /// first-class `≥n`/`≤n` card arm; an ontology that holds this but not
    /// `inverse_cardinality_role_separable` can still take the card arm, but
    /// only with the ABox treated the way the CB engine treats it (dropped
    /// behind the frontend's asserted-inconsistency precheck), never as a
    /// natively materialized ABox.
    #[serde(default)]
    pub card_number_role_separable: bool,
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
    number_roles: HashSet<&'a str>,
    positive_assertion_roles: HashSet<&'a str>,
    negative_assertion_roles: HashSet<&'a str>,
    inverse_roles: HashSet<&'a str>,
    non_simple_roles: HashSet<&'a str>,
    chain_roles: HashSet<&'a str>,
    role_dependencies: HashMap<&'a str, HashSet<&'a str>>,
    /// Roles carrying an axiom the FIRST-CLASS RBox channel cannot represent
    /// while `parse.rs`/`normalise.rs` still clausify it exactly (irreflexivity,
    /// reflexivity, a complex domain/range on a named role). The certificate
    /// keeps them out of the number-role component instead of declining
    /// outright; see [`SourceProfileBuilder::card_number_role_separable`].
    clause_retained_constraint_roles: HashSet<&'a str>,
    /// `owl:topObjectProperty` observed anywhere except as the SUPER role of a
    /// plain `SubObjectPropertyOf` (where it is a tautology the frontend
    /// compiles to a write-only bridge clause).
    universal_role_beyond_subrole_super: bool,
    number_role_seen: bool,
    object_cardinality_seen: bool,
    inverse_role_seen: bool,
    inverse_cardinality_certificate_invalid: bool,
    explicit_inverse_relation: bool,
    object_role_hierarchy: bool,
    nominal_unconditional: bool,
    nominal_from_abox: bool,
    nominal_from_concept: bool,
    /// Source identity constraints retained for the positive-ABox separation
    /// certificate. SameIndividual is an n-ary equality; DifferentIndividuals
    /// is pairwise inequality over every pair in one axiom.
    same_individual_groups: Vec<Vec<&'a str>>,
    different_individual_groups: Vec<Vec<&'a str>>,
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
            number_roles: HashSet::new(),
            positive_assertion_roles: HashSet::new(),
            negative_assertion_roles: HashSet::new(),
            inverse_roles: HashSet::new(),
            non_simple_roles: HashSet::new(),
            chain_roles: HashSet::new(),
            role_dependencies: HashMap::new(),
            clause_retained_constraint_roles: HashSet::new(),
            universal_role_beyond_subrole_super: false,
            number_role_seen: false,
            object_cardinality_seen: false,
            inverse_role_seen: false,
            inverse_cardinality_certificate_invalid: false,
            explicit_inverse_relation: false,
            object_role_hierarchy: false,
            nominal_unconditional: false,
            nominal_from_abox: false,
            nominal_from_concept: false,
            same_individual_groups: Vec::new(),
            different_individual_groups: Vec::new(),
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
                        // The direct HT RBox bridge represents only binary
                        // chains. The normalizer compiles longer chains for CB,
                        // but this source-side HT certificate must still decline.
                        if rs.len() != 2 {
                            self.inverse_cardinality_certificate_invalid = true;
                        }
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
                        let mut dependency_roles: Vec<&'a str> = Vec::new();
                        for role in rs {
                            if let Some(role) = self.atomic_certificate_role(role) {
                                dependency_roles.push(role);
                                self.non_simple_roles.insert(role);
                            }
                        }
                        if let Some(role) = args
                            .get(1)
                            .and_then(|role| self.atomic_certificate_role(role))
                        {
                            dependency_roles.push(role);
                            self.non_simple_roles.insert(role);
                        }
                        if !all_transitive {
                            self.chain_roles.extend(dependency_roles.iter().copied());
                        }
                        self.connect_role_component(&dependency_roles);
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
                let dependency_sub = args
                    .first()
                    .and_then(|role| self.atomic_certificate_role(role));
                let dependency_sup = args
                    .get(1)
                    .and_then(|role| self.atomic_certificate_role(role));
                if let (Some(sub), Some(sup)) = (dependency_sub, dependency_sup) {
                    // `R ⊑ owl:topObjectProperty` is a tautology: it merges no
                    // role components and adds no constraint. The frontend
                    // compiles it into the write-only bridge clause
                    // `R(x,y) → U(x,y)`, so it is not a USE of the universal
                    // connection either. The normalized recheck independently
                    // proves nothing ever reads `U`.
                    if !is_universal_role(sup) {
                        self.connect_roles(sub, sup);
                    }
                }
                for (index, r) in args.iter().enumerate() {
                    let universal_super = index == 1 && role_is_universal(r);
                    let seen_before = self.universal_role_beyond_subrole_super;
                    self.object_role(r);
                    if universal_super {
                        self.universal_role_beyond_subrole_super = seen_before;
                    }
                }
            }
            "EquivalentObjectProperties" => {
                self.logical_rbox(head);
                self.expr.role_hierarchy = true;
                self.object_role_hierarchy = true;
                let dependency_roles: Vec<&'a str> = args
                    .iter()
                    .filter_map(|role| self.atomic_certificate_role(role))
                    .collect();
                self.connect_role_component(&dependency_roles);
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
                    self.inverse_roles.insert(left);
                    self.inverse_roles.insert(right);
                    self.inverse_role_seen = true;
                    self.connect_roles(left, right);
                } else {
                    self.inverse_cardinality_certificate_invalid = true;
                }
                for r in &args {
                    self.object_role(r);
                }
            }
            "DisjointObjectProperties" => {
                self.logical_rbox(head);
                // cb_to_ht keeps this as a role-constraint fence. A source
                // certificate that admitted it could select the nominal card
                // portfolio before the normalized worker correctly declined.
                self.inverse_cardinality_certificate_invalid = true;
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
                    self.non_simple_roles.insert(r);
                } else {
                    self.inverse_cardinality_certificate_invalid = true;
                }
                self.object_roles(&args);
            }
            "SymmetricObjectProperty" => {
                self.logical_rbox(head);
                // Konclude represents symmetry through an inverse-equivalent
                // role link, which sets the I occurrence flag.
                self.expr.inverse = true;
                if let Some(role) = args
                    .first()
                    .and_then(|role| self.atomic_certificate_role(role))
                {
                    self.inverse_roles.insert(role);
                    self.inverse_role_seen = true;
                }
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
                self.number_role_seen = true;
                if let Some(role) = args
                    .first()
                    .and_then(|role| self.atomic_certificate_role(role))
                {
                    self.number_roles.insert(role);
                }
                self.object_roles(&args);
            }
            "InverseFunctionalObjectProperty" => {
                self.logical_rbox(head);
                self.stats.inverse_functional_role_axioms += 1;
                self.expr.functionality = true;
                self.expr.inverse = true;
                self.number_role_seen = true;
                self.inverse_role_seen = true;
                self.inverse_cardinality_certificate_invalid = true;
                if let Some(role) = args
                    .first()
                    .and_then(|role| self.atomic_certificate_role(role))
                {
                    self.number_roles.insert(role);
                    self.inverse_roles.insert(role);
                }
                self.object_roles(&args);
            }
            "AsymmetricObjectProperty" => {
                self.logical_rbox(head);
                // `normalise.rs` clausifies asymmetry exactly, but `rbox.rs`
                // records it under the same conservative `role-constraint`
                // category as disjoint roles. Keep the source-profile
                // certificate closed until the exact typed-source route checks
                // the normalized constructor directly.
                self.inverse_cardinality_certificate_invalid = true;
                self.object_roles(&args);
            }
            "ReflexiveObjectProperty" => {
                self.logical_rbox(head);
                // The `R(x,x)` fact carries the semantics into the clause set;
                // only the RBox side channel fences it.
                self.clause_retained_role_constraint(args.first().copied());
                self.object_roles(&args);
            }
            "IrreflexiveObjectProperty" => {
                self.logical_rbox(head);
                self.expr.negation_disjunction = true;
                // `R(x,x) → ⊥` is emitted into the clause set; the RBox row is
                // fenced only because the first-class channel has no shape for
                // it.
                self.clause_retained_role_constraint(args.first().copied());
                self.object_roles(&args);
            }
            "ObjectPropertyDomain" => {
                self.logical_rbox(head);
                self.stats.domain_axioms += 1;
                self.object_property_domain_range_certificate(
                    args.first().copied(),
                    args.get(1).copied(),
                );
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
                self.object_property_domain_range_certificate(
                    args.first().copied(),
                    args.get(1).copied(),
                );
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
                self.inverse_cardinality_certificate_invalid = true;
                self.stats.role_inclusion_axioms += 1;
                self.expr.role_hierarchy = true;
                self.data_roles(&args);
            }
            "DisjointDataProperties" => {
                self.logical_rbox(head);
                self.inverse_cardinality_certificate_invalid = true;
                self.data_roles(&args);
            }
            "FunctionalDataProperty" => {
                self.logical_rbox(head);
                self.inverse_cardinality_certificate_invalid = true;
                self.stats.functional_role_axioms += 1;
                self.expr.functionality = true;
                self.expr.datatype = true;
                self.data_roles(&args);
            }
            "DataPropertyDomain" => {
                self.logical_rbox(head);
                self.inverse_cardinality_certificate_invalid = true;
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
                self.inverse_cardinality_certificate_invalid = true;
                self.stats.range_axioms += 1;
                if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                    self.data_properties.insert(r);
                }
            }
            "DatatypeDefinition" => {
                self.logical_tbox(head);
                self.inverse_cardinality_certificate_invalid = true;
                // A standalone datatype definition is internalized as a
                // nondeterministic concept but does not attach a data role, so
                // Konclude reports SI rather than a `(D)` suffix.
                self.expr.negation_disjunction = true;
            }
            "HasKey" => {
                self.logical_tbox(head);
                // Key equalities are not first-class number restrictions and
                // are outside the scoped NN/NI absence proof.
                self.inverse_cardinality_certificate_invalid = true;
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
                    match self.atomic_certificate_role(r) {
                        Some(role) if !is_universal_role(role) && !is_bottom_role(role) => {
                            self.positive_assertion_roles.insert(role);
                        }
                        _ => self.inverse_cardinality_certificate_invalid = true,
                    }
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
                    match self.atomic_certificate_role(r) {
                        Some(role) if !is_universal_role(role) && !is_bottom_role(role) => {
                            self.negative_assertion_roles.insert(role);
                        }
                        _ => self.inverse_cardinality_certificate_invalid = true,
                    }
                    self.object_role(r);
                }
                self.individual_arg(args.get(1).copied());
                self.individual_arg(args.get(2).copied());
            }
            "DataPropertyAssertion" => {
                self.logical_abox(head);
                self.inverse_cardinality_certificate_invalid = true;
                self.stats.role_assertions += 1;
                if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                    self.data_properties.insert(r);
                }
                self.individual_arg(args.get(1).copied());
            }
            "NegativeDataPropertyAssertion" => {
                self.logical_abox(head);
                self.inverse_cardinality_certificate_invalid = true;
                self.stats.role_assertions += 1;
                self.expr.datatype = true;
                self.expr.negation_disjunction = true;
                if let Some(r) = args.first().and_then(|n| n.as_atom()) {
                    self.data_properties.insert(r);
                }
                self.individual_arg(args.get(1).copied());
            }
            "SameIndividual" => {
                self.logical_abox(head);
                // A ground equality has an Eq head without a counted role; the
                // independent normalized certificate rejects that shape.
                self.inverse_cardinality_certificate_invalid = true;
                self.expr.nominal_individual = true;
                self.nominal_unconditional = true;
                self.nominal_from_abox = true;
                self.expr.negation_disjunction = true;
                self.same_individual_groups
                    .push(args.iter().filter_map(|n| n.as_atom()).collect());
                for n in &args {
                    self.individual_arg(Some(*n));
                }
            }
            "DifferentIndividuals" => {
                self.logical_abox(head);
                self.expr.nominal_individual = true;
                self.nominal_unconditional = true;
                self.nominal_from_abox = true;
                self.expr.negation_disjunction = true;
                self.different_individual_groups
                    .push(args.iter().filter_map(|n| n.as_atom()).collect());
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
            // Unknown top-level logical constructors are outside every exact
            // source certificate.  Ordinary parsing may conservatively ignore
            // them, but they must never help admit the native card route.
            _ => self.inverse_cardinality_certificate_invalid = true,
        }
    }

    pub fn finish(self, file_bytes: u64) -> OntologyProfile {
        self.finish_with_separable_class_names(file_bytes).0
    }

    /// Finish the profile and return source-signature classes only when an
    /// ABox-projection route could use them. Ordinary and rejected ABox inputs
    /// therefore allocate no extra signature vector. The orchestrator still
    /// needs an exact consistency verdict before the disjoint-union candidate
    /// may project anything.
    pub(crate) fn finish_with_separable_class_names(
        mut self,
        file_bytes: u64,
    ) -> (OntologyProfile, Vec<&'a str>) {
        // Compute borrowed-set certificates before moving the raw axiom-type
        // map and entity sets into their owned statistics representation.
        let card_number_role_separable = self.card_number_role_separable();
        let inverse_cardinality_role_separable = self.inverse_cardinality_role_separable();
        let identity_consistent = self.identity_constraints_consistent();
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
        let positive_abox_tbox_separable = positive_abox_tbox_separable(
            &self.stats,
            &self.expr,
            self.nominal_from_concept,
            identity_consistent,
        );
        let positive_el_abox_materializable = positive_el_abox_materializable(
            &self.stats,
            &self.expr,
            self.nominal_from_concept,
            identity_consistent,
        );
        let any_concept_nominal =
            self.nominal_from_concept || !self.conditional_nominal_roles.is_empty();
        let disjoint_union_abox_candidate =
            disjoint_union_abox_candidate(&self.stats, &self.expr, any_concept_nominal);
        let mut separable_class_names =
            if positive_abox_tbox_separable || disjoint_union_abox_candidate {
                self.classes.iter().copied().collect::<Vec<_>>()
            } else {
                Vec::new()
            };
        separable_class_names.sort_unstable();
        (
            OntologyProfile {
                schema_version: 2,
                positive_abox_tbox_separable,
                positive_el_abox_materializable,
                disjoint_union_abox_candidate,
                inverse_cardinality_role_separable,
                card_number_role_separable,
                expressivity: self.expr,
                source: self.stats,
                clauses: ClauseStatistics::default(),
            },
            separable_class_names,
        )
    }

    /// Decide the ground equality/inequality fragment exactly.
    ///
    /// Equality groups are unioned first. Every pair in each n-ary
    /// DifferentIndividuals axiom must then have distinct representatives.
    fn identity_constraints_consistent(&self) -> bool {
        let mut ids: HashMap<&str, usize> = HashMap::new();
        for group in self
            .same_individual_groups
            .iter()
            .chain(self.different_individual_groups.iter())
        {
            for &individual in group {
                let next = ids.len();
                ids.entry(individual).or_insert(next);
            }
        }
        let mut parent: Vec<usize> = (0..ids.len()).collect();

        fn find(parent: &mut [usize], mut node: usize) -> usize {
            let mut root = node;
            while parent[root] != root {
                root = parent[root];
            }
            while parent[node] != node {
                let next = parent[node];
                parent[node] = root;
                node = next;
            }
            root
        }

        for group in &self.same_individual_groups {
            let Some(first) = group.first().and_then(|name| ids.get(name)).copied() else {
                continue;
            };
            for name in group.iter().skip(1) {
                let Some(&other) = ids.get(name) else {
                    continue;
                };
                let left = find(&mut parent, first);
                let right = find(&mut parent, other);
                if left != right {
                    parent[right] = left;
                }
            }
        }
        for group in &self.different_individual_groups {
            // DifferentIndividuals is pairwise inequality. Its representatives
            // are pairwise distinct exactly when this set has no duplicate;
            // avoid an O(n²) scan on ORE's 100k-individual identity groups.
            let mut representatives = HashSet::with_capacity(group.len());
            for name in group {
                let Some(&node) = ids.get(name) else {
                    continue;
                };
                if !representatives.insert(find(&mut parent, node)) {
                    return false;
                }
            }
        }
        true
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
            // The fast cardinality worker has no concrete-domain oracle. Keep
            // the inverse/cardinality certificate source-object-only.
            self.inverse_cardinality_certificate_invalid = true;
        } else {
            self.number_role_seen = true;
            self.object_cardinality_seen = true;
            match args
                .get(1)
                .and_then(|role| self.atomic_certificate_role(role))
            {
                Some(role) if !is_universal_role(role) && !is_bottom_role(role) => {
                    self.number_roles.insert(role);
                }
                _ => self.inverse_cardinality_certificate_invalid = true,
            }
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
                    self.universal_role_beyond_subrole_super = true;
                } else {
                    self.object_properties.insert(r);
                }
            }
            Node::List(h, args) if *h == "ObjectInverseOf" => {
                self.expr.inverse = true;
                // Concept-position/in-line inverse roles use generated
                // `__inv__` bridges and are intentionally outside the scoped
                // named-RBox certificate.
                self.inverse_cardinality_certificate_invalid = true;
                if let Some(r) = args.first().and_then(Node::as_atom) {
                    self.object_properties.insert(r);
                }
            }
            _ => {}
        }
    }

    fn atomic_certificate_role(&mut self, node: &Node<'a>) -> Option<&'a str> {
        match node {
            Node::Atom(role) => Some(*role),
            _ => {
                self.inverse_cardinality_certificate_invalid = true;
                None
            }
        }
    }

    /// Record a role whose only unrepresentable axiom is a clause-retained
    /// constraint (irreflexivity / reflexivity / a complex domain or range on a
    /// named role). `parse.rs` and `normalise.rs` emit the exact clause, so the
    /// Ht still consumes the axiom; the certificate only has to keep such a
    /// role out of the number-role component. Anything else fails closed.
    fn clause_retained_role_constraint(&mut self, node: Option<&Node<'a>>) {
        match node.and_then(|node| node.as_atom()) {
            Some(role) if !is_universal_role(role) && !is_bottom_role(role) => {
                self.clause_retained_constraint_roles.insert(role);
            }
            _ => self.inverse_cardinality_certificate_invalid = true,
        }
    }

    /// `ObjectPropertyDomain`/`ObjectPropertyRange` certificate arm. A named
    /// role with a named non-⊥ class is the exact first-class RBox row. A named
    /// role with a COMPLEX class is fenced in the RBox but clausified by
    /// `parse.rs` as `∃R.⊤ ⊑ C` / `⊤ ⊑ ∀R.C`, so it is clause-retained. Every
    /// other shape (inverse role expression, or a ⊥ class, which `parse.rs`
    /// does not clausify) fails closed.
    fn object_property_domain_range_certificate(
        &mut self,
        role: Option<&Node<'a>>,
        class: Option<&Node<'a>>,
    ) {
        let Some(true) = role.map(|role| role.as_atom().is_some()) else {
            self.inverse_cardinality_certificate_invalid = true;
            return;
        };
        match class {
            Some(Node::Atom(name)) if !is_bottom(name) => {}
            Some(Node::List(..)) => self.clause_retained_role_constraint(role),
            _ => self.inverse_cardinality_certificate_invalid = true,
        }
    }

    fn connect_roles(&mut self, left: &'a str, right: &'a str) {
        self.role_dependencies
            .entry(left)
            .or_default()
            .insert(right);
        self.role_dependencies
            .entry(right)
            .or_default()
            .insert(left);
    }

    fn connect_role_component(&mut self, roles: &[&'a str]) {
        let Some((&first, rest)) = roles.split_first() else {
            self.inverse_cardinality_certificate_invalid = true;
            return;
        };
        for &role in rest {
            self.connect_roles(first, role);
        }
    }

    /// The NUMBER-ROLE half of the scoped inverse+cardinality certificate: no
    /// number restriction applies to an inverse, inverse-connected, chained,
    /// transitive, universal, bottom, or clause-retained-constraint role. That
    /// is what the fast Ht's first-class `≥n`/`≤n` rules plus inverse-aware
    /// blocking need; it says nothing about how a native ABox is materialized.
    /// [`SourceProfileBuilder::inverse_cardinality_role_separable`] adds the
    /// ABox half on top.
    fn card_number_role_separable(&self) -> bool {
        if !self.number_role_seen
            || !self.object_cardinality_seen
            || !self.inverse_role_seen
            || self.inverse_cardinality_certificate_invalid
            || self.number_roles.is_empty()
            || self.inverse_roles.is_empty()
            || self.stats.imports != 0
            || self.stats.rule_axioms != 0
            || self.expr.datatype
            || self.universal_role_beyond_subrole_super
            || self.stats.bottom_role_occurrences != 0
        {
            return false;
        }

        let mut seen: HashSet<&'a str> = HashSet::new();
        let mut pending: Vec<&'a str> = self.number_roles.iter().copied().collect();
        while let Some(role) = pending.pop() {
            if !seen.insert(role) {
                continue;
            }
            if self.inverse_roles.contains(role)
                || self.non_simple_roles.contains(role)
                || self.clause_retained_constraint_roles.contains(role)
                || is_universal_role(role)
                || is_bottom_role(role)
            {
                return false;
            }
            if let Some(neighbours) = self.role_dependencies.get(role) {
                pending.extend(neighbours.iter().copied());
            }
        }
        true
    }

    fn inverse_cardinality_role_separable(&self) -> bool {
        if !self.card_number_role_separable() {
            return false;
        }

        // A negative ground assertion ¬R(a,b) is checked by a guarded clash
        // clause in the native Ht. The production Ht keeps role hierarchies and
        // inverse bridges as ordinary clauses, but role-chain/transitive edges
        // are side data used primarily for universal propagation. Until native
        // ABox edge materialization through those automata is a default-certified
        // mechanism, require every negative-assertion component to be disjoint
        // from every non-simple role. This retains 9540: its has_point/is_front/
        // is_back negative roles are disconnected from its two transitive roles.
        let mut seen_negative: HashSet<&'a str> = HashSet::new();
        let mut pending_negative: Vec<&'a str> =
            self.negative_assertion_roles.iter().copied().collect();
        while let Some(role) = pending_negative.pop() {
            if !seen_negative.insert(role) {
                continue;
            }
            if self.non_simple_roles.contains(role) {
                return false;
            }
            if let Some(neighbours) = self.role_dependencies.get(role) {
                pending_negative.extend(neighbours.iter().copied());
            }
        }

        // Positive named-individual edges also need exact materialization when
        // they participate in a proper role chain: R(a,b), S(b,c), R∘S⊑T can
        // trigger T's domain/range and ground constraints. The current side-data
        // chain path handles universal propagation but does not generally emit
        // every T(a,c), so reject any positive-ABox role component connected to
        // a non-transitive role-chain component. Explicit TransitiveObjectProperty
        // alone is safe here; its direct edges already trigger domain/range and
        // transitive universal propagation is implemented separately.
        let mut seen_positive: HashSet<&'a str> = HashSet::new();
        let mut pending_positive: Vec<&'a str> =
            self.positive_assertion_roles.iter().copied().collect();
        while let Some(role) = pending_positive.pop() {
            if !seen_positive.insert(role) {
                continue;
            }
            if self.chain_roles.contains(role) {
                return false;
            }
            if let Some(neighbours) = self.role_dependencies.get(role) {
                pending_positive.extend(neighbours.iter().copied());
            }
        }
        true
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

/// Admit a source whose ABox may be projected after, and only after, an exact
/// consistency decision for the full ontology. Nominal-free DL TBoxes without
/// the universal role are closed under disjoint unions. Individual names can
/// all be interpreted in the certified full-model component, so the ABox
/// cannot turn a TBox countermodel into a new named-class subsumption.
///
/// Keys can compare data values across components; imports and rules escape the
/// self-contained local TBox contract. They therefore fail closed here.
fn disjoint_union_abox_candidate(
    source: &SourceStatistics,
    expr: &ExpressivityProfile,
    nominal_from_concept: bool,
) -> bool {
    source.abox_axioms > 0
        && !nominal_from_concept
        && !expr.universal_role
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.axiom_types.get("HasKey").copied().unwrap_or(0) == 0
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
fn positive_abox_tbox_separable(
    source: &SourceStatistics,
    expr: &ExpressivityProfile,
    nominal_from_concept: bool,
    identity_consistent: bool,
) -> bool {
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
        // Pure ground identity constraints are harmless after the exact
        // union-find check below, provided the TBox has no equality-generating
        // or negative constructor and no concept-level nominal.
        "SameIndividual",
        "DifferentIndividuals",
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
        && (!expr.nominal_individual || (!nominal_from_concept && identity_consistent))
        && (!expr.nominal_individual
            || (source.functional_role_axioms == 0 && source.inverse_functional_role_axioms == 0))
        && !expr.universal_role
        && !expr.datatype
        && !expr.grounding
        && source.imports == 0
        && source
            .axiom_types
            .keys()
            .all(|kind| SAFE_AXIOMS.contains(&kind.as_str()))
}

/// Admit the positive EL++ ABox fragment whose consistency can be decided by
/// [`crate::elcomplete::positive_abox_consistent`].
///
/// This is a source whitelist. The completion consumer independently requires
/// complete typed-ABox coverage and a pure-EL normalized clause set, so any
/// source/profile mismatch declines instead of publishing a partial answer.
fn positive_el_abox_materializable(
    source: &SourceStatistics,
    expr: &ExpressivityProfile,
    nominal_from_concept: bool,
    identity_consistent: bool,
) -> bool {
    const SAFE_AXIOMS: &[&str] = &[
        "Declaration",
        "Annotation",
        "AnnotationAssertion",
        "SubAnnotationPropertyOf",
        "AnnotationPropertyDomain",
        "AnnotationPropertyRange",
        "SubClassOf",
        "EquivalentClasses",
        "DisjointClasses",
        "SubObjectPropertyOf",
        "EquivalentObjectProperties",
        "TransitiveObjectProperty",
        "ReflexiveObjectProperty",
        "ObjectPropertyDomain",
        "ObjectPropertyRange",
        "ClassAssertion",
        "ObjectPropertyAssertion",
        "SameIndividual",
        "DifferentIndividuals",
    ];

    source.abox_axioms > 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.bottom_role_occurrences == 0
        && source.unions == 0
        && source.complements == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.functional_role_axioms == 0
        && source.inverse_functional_role_axioms == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
        && !nominal_from_concept
        && identity_consistent
        && !expr.datatype
        && !expr.grounding
        // The EL completion core treats range propagation as a residual
        // canonical-model check, not a cert-off normal form. A positive ABox
        // can activate a range, so keep this source certificate in lockstep
        // with the normalized consumer. The independent ABox/TBox separation
        // certificate can still route range-only taxonomy cases exactly.
        && source.range_axioms == 0
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

fn observe_term<'a>(
    term: &'a crate::json_io::JTerm,
    functions: &mut HashSet<&'a str>,
    individuals: &mut HashSet<&'a str>,
) -> (bool, bool) {
    use crate::json_io::JTerm;
    match term {
        JTerm::Fun { function, arg } => {
            functions.insert(function);
            let (_, aux) = observe_term(arg, functions, individuals);
            (true, aux)
        }
        JTerm::Ind { name } => {
            individuals.insert(name);
            (false, false)
        }
        JTerm::Aux { .. } => (false, true),
        JTerm::Var { .. } => (false, false),
    }
}

/// Compute normalized-clause statistics in one borrowed pass over the final
/// clause vector.  No clause or symbol strings are cloned.
pub fn clause_statistics(clauses: &[crate::json_io::JClause]) -> ClauseStatistics {
    use crate::json_io::JAtom;
    let mut out = ClauseStatistics::default();
    let mut concepts: HashSet<&str> = HashSet::new();
    let mut roles: HashSet<&str> = HashSet::new();
    let mut functions: HashSet<&str> = HashSet::new();
    let mut individuals: HashSet<&str> = HashSet::new();
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
                    let (f, a) = observe_term(term, &mut functions, &mut individuals);
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
                        let (f, a) = observe_term(term, &mut functions, &mut individuals);
                        has_fun |= f;
                        has_aux |= a;
                    }
                }
                JAtom::Eq { left, right } => {
                    out.equality_atoms += 1;
                    for term in [left, right] {
                        let (f, a) = observe_term(term, &mut functions, &mut individuals);
                        has_fun |= f;
                        has_aux |= a;
                    }
                }
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
    out.function_term_symbols = functions.len() as u64;
    out.individual_term_symbols = individuals.len() as u64;
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

        let identity_only = source(
            r#"Ontology(
              SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>))
              ClassAssertion(<A> <a>)
              SameIndividual(<a> <aa>)
              DifferentIndividuals(<aa> <b> <c>)
              ObjectPropertyAssertion(<r> <b> <c>)
            )"#,
        );
        assert!(
            identity_only.positive_abox_tbox_separable,
            "consistent identity constraints do not change a positive TBox taxonomy"
        );
        assert!(
            identity_only.positive_el_abox_materializable,
            "the same positive identity ABox is materializable by EL completion"
        );
        let ranged_role_abox = source(
            r#"Ontology(
              ObjectPropertyRange(<r> <B>)
              ObjectPropertyAssertion(<r> <a> <b>)
            )"#,
        );
        assert!(
            !ranged_role_abox.positive_el_abox_materializable,
            "the source certificate must reject range rules exactly as the cert-off normalized EL consumer does"
        );
        let bottom_constrained = source(
            "Ontology(SubClassOf(ObjectIntersectionOf(<A> <B>) owl:Nothing) ClassAssertion(<A> <a>))",
        );
        assert!(!bottom_constrained.positive_abox_tbox_separable);
        assert!(
            bottom_constrained.positive_el_abox_materializable,
            "EL completion, rather than the full-model shortcut, decides bottom constraints"
        );
        let identity_clash = source(
            "Ontology(SameIndividual(<a> <b>) DifferentIndividuals(<a> <b>) ClassAssertion(<A> <a>))",
        );
        assert!(
            !identity_clash.positive_abox_tbox_separable,
            "union-find must reject an equality/inequality clash"
        );
        assert!(!identity_clash.positive_el_abox_materializable);
        let identity_with_functionality = source(
            "Ontology(FunctionalObjectProperty(<r>) DifferentIndividuals(<a> <b>) ClassAssertion(<A> <a>))",
        );
        assert!(
            !identity_with_functionality.positive_abox_tbox_separable,
            "an equality-generating TBox remains outside the certificate"
        );

        for unsafe_source in [
            "Ontology(SubClassOf(<A> owl:Nothing) ClassAssertion(<A> <a>))",
            "Ontology(DisjointClasses(<A> <B>) ClassAssertion(<A> <a>))",
            "Ontology(SubClassOf(<A> ObjectOneOf(<a>)) ClassAssertion(<A> <a>))",
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
    fn disjoint_union_abox_gate_excludes_component_connectors() {
        let admitted = source(
            r#"Ontology(
              DisjointClasses(<A> <B>)
              InverseObjectProperties(<r> <s>)
              ClassAssertion(<A> <a>)
              SameIndividual(<a> <aa>)
              DifferentIndividuals(<aa> <b>)
            )"#,
        );
        assert!(admitted.disjoint_union_abox_candidate);
        assert!(!admitted.positive_abox_tbox_separable);

        for rejected in [
            "Ontology(EquivalentClasses(<A> ObjectOneOf(<a>)) ClassAssertion(<A> <a>))",
            "Ontology(ObjectPropertyDomain(<r> ObjectHasValue(<s> <a>)) ClassAssertion(<A> <a>))",
            "Ontology(SubClassOf(<A> ObjectAllValuesFrom(owl:topObjectProperty <B>)) ClassAssertion(<A> <a>))",
            "Ontology(HasKey(<A> (<p>)) ClassAssertion(<A> <a>))",
            "Ontology(Import(<http://e/import>) ClassAssertion(<A> <a>))",
            "Ontology(DLSafeRule(Body(ClassAtom(<A> Variable(<x>))) Head(ClassAtom(<B> Variable(<x>)))) ClassAssertion(<A> <a>))",
        ] {
            assert!(!source(rejected).disjoint_union_abox_candidate, "{rejected}");
        }
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
    fn inverse_cardinality_role_separation_is_source_certified() {
        // The inverse role remains semantically active (domain/range and a
        // restriction share class A with the cardinality axiom), but its role
        // component is disjoint from the simple number role p. Exact inverse
        // processing therefore composes with the SHOQ number rule without an
        // NN/NI number-role premise.
        let separated = source(
            r#"Ontology(
              InverseObjectProperties(<i> <j>)
              SubObjectPropertyOf(<i> <k>)
              TransitiveObjectProperty(<k>)
              ObjectPropertyDomain(<i> <A>)
              ObjectPropertyRange(<j> <B>)
              FunctionalObjectProperty(<f>)
              SubClassOf(<A> ObjectExactCardinality(2 <p> <C>))
              SubClassOf(<A> ObjectSomeValuesFrom(<i> ObjectOneOf(<a>)))
            )"#,
        );
        assert!(separated.inverse_cardinality_role_separable);

        let separated_negative_abox = source(
            r#"Ontology(
              InverseObjectProperties(<is_front> <is_back>)
              TransitiveObjectProperty(<is_completely_inside>)
              SubClassOf(<Shape> ObjectExactCardinality(2 <has_point> <Point>))
              ObjectPropertyAssertion(<has_point> <shape> <p2>)
              NegativeObjectPropertyAssertion(<has_point> <shape> <p>)
              NegativeObjectPropertyAssertion(<is_front> <shape> <other>)
            )"#,
        );
        assert!(
            separated_negative_abox.inverse_cardinality_role_separable,
            "9540-shaped negative/cardinality and inverse components are separate from transitivity"
        );

        for unsafe_source in [
            // Functionality has no CardMeta under the production default, so
            // it cannot by itself select a first-class-cardinality portfolio.
            "Ontology(InverseObjectProperties(<i> <j>) FunctionalObjectProperty(<f>))",
            // direct use of an inverse role by a number restriction
            "Ontology(InverseObjectProperties(<p> <q>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // role-inclusion / equivalence paths into an inverse component
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(<p> <i>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) EquivalentObjectProperties(<p> <i>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(<f> <i>) FunctionalObjectProperty(<f>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // chain and transitive number roles are non-simple
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(ObjectPropertyChain(<p> <r>) <s>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(ObjectPropertyChain(<a> <b> <c>) <s>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) TransitiveObjectProperty(<p>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // inverse functionality combines the two mechanisms directly
            "Ontology(InverseObjectProperties(<i> <j>) InverseFunctionalObjectProperty(<r>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // inline inverse expressions retain the hard fail-closed fence
            "Ontology(InverseObjectProperties(<i> <j>) SubClassOf(<A> ObjectMaxCardinality(1 ObjectInverseOf(<p>) <C>)))",
            // Every normalized RBox / equality fence must also fail at source,
            // before a nominal ontology can be sent away from its exact CB path.
            // A clause-retained role constraint is admitted (see
            // `clause_retained_role_constraints_stay_out_of_the_number_component`)
            // but ONLY while it stays out of the number-role component.
            "Ontology(InverseObjectProperties(<i> <j>) ObjectPropertyDomain(<p> ObjectUnionOf(<A> <B>)) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) ObjectPropertyRange(<p> ObjectUnionOf(<A> <B>)) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) IrreflexiveObjectProperty(<p>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(<p> <r>) ReflexiveObjectProperty(<r>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // A ⊥ domain/range is fenced in the RBox and NOT clausified by
            // parse.rs, so it is a genuine drop, not a clause-retained row.
            "Ontology(InverseObjectProperties(<i> <j>) ObjectPropertyDomain(<i> owl:Nothing) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // Asymmetry shares the ambiguous `role-constraint` fence reason
            // with the dropped DisjointObjectProperties, so it fails closed.
            "Ontology(InverseObjectProperties(<i> <j>) AsymmetricObjectProperty(<r>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // owl:topObjectProperty is inert only as the SUPER of a plain role
            // inclusion; in the sub position it is a genuine universal premise.
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(owl:topObjectProperty <r>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) SameIndividual(<a> <b>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) HasKey(<A> <r> <d>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // no concrete-domain oracle in the card worker
            "Ontology(InverseObjectProperties(<i> <j>) SubClassOf(<A> DataMaxCardinality(1 <d> xsd:string)) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // top/bottom roles anywhere, and unknown logical constructors,
            // invalidate the global semantic certificate.
            "Ontology(InverseObjectProperties(<i> <j>) SubClassOf(<X> ObjectSomeValuesFrom(owl:topObjectProperty <Y>)) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) ObjectPropertyAssertion(owl:bottomObjectProperty <a> <b>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) UnsupportedLogicalAxiom(<X> <Y>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
        ] {
            let profile = source(unsafe_source);
            assert!(
                !profile.inverse_cardinality_role_separable,
                "unsafe inverse/cardinality source was certified: {unsafe_source}"
            );
            assert!(
                !profile.card_number_role_separable,
                "a number-role violation must decline both certificates: {unsafe_source}"
            );
        }

        // The ABox-materialization premises are the OTHER half. They decline
        // the native nominal route without touching the number-role proof, so
        // the cardinality arm stays available through the proxy-ABox route.
        for abox_only in [
            // A native negative edge may not depend on role-chain or
            // transitivity materialization (directly or through hierarchy).
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>) NegativeObjectPropertyAssertion(<t> <a> <b>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(<n> <t>) TransitiveObjectProperty(<t>) NegativeObjectPropertyAssertion(<n> <a> <b>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
            // ore_ont_7499's shape: an asserted edge feeding a proper chain.
            "Ontology(InverseObjectProperties(<i> <j>) SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>) ObjectPropertyAssertion(<r> <a> <b>) ObjectPropertyAssertion(<s> <b> <c>) ObjectPropertyRange(<t> <C>) DisjointClasses(<C> <D>) ClassAssertion(<D> <c>) SubClassOf(<A> ObjectMaxCardinality(1 <p> <C>)))",
        ] {
            let profile = source(abox_only);
            assert!(
                !profile.inverse_cardinality_role_separable,
                "an unmaterializable ABox must decline the native nominal route: {abox_only}"
            );
            assert!(
                profile.card_number_role_separable,
                "an ABox premise must not decline the number-role proof: {abox_only}"
            );
        }
    }

    #[test]
    fn clause_retained_role_constraints_stay_out_of_the_number_component() {
        // ore_ont_7499 in miniature: named inverse pairs, a transitive role, a
        // role chain, a complex range and an irreflexive role on roles that the
        // number restriction never touches, plus the tautological
        // `R ⊑ owl:topObjectProperty`. `rbox.rs` fences the range/irreflexivity
        // rows because the first-class RBox channel has no shape for them, but
        // `parse.rs`/`normalise.rs` clausify both exactly, so the certificate
        // must not decline: no number restriction reaches an inverse,
        // non-simple, universal or constrained role.
        let retained = source(
            r#"Ontology(
              InverseObjectProperties(<i> <j>)
              TransitiveObjectProperty(<i>)
              SubObjectPropertyOf(ObjectPropertyChain(<i> <i>) <k>)
              SubObjectPropertyOf(<u> owl:topObjectProperty)
              IrreflexiveObjectProperty(<v>)
              ObjectPropertyRange(<w> ObjectUnionOf(<A> <B>))
              FunctionalObjectProperty(<f>)
              SubClassOf(<A> ObjectMinCardinality(2 <p> <C>))
            )"#,
        );
        assert!(
            retained.card_number_role_separable,
            "clause-retained role constraints on non-number roles must not decline"
        );
        assert!(
            retained.inverse_cardinality_role_separable,
            "without ABox assertions both halves of the certificate hold"
        );

        // The ABox half is independent: an asserted edge whose role feeds a
        // proper role chain cannot be materialized exactly, so the native
        // nominal route declines while the number-role certificate still holds
        // (this is exactly the ore_ont_7499 split, which the
        // `certified_card_proxy_abox` route serves).
        let chain_abox = source(
            r#"Ontology(
              InverseObjectProperties(<i> <j>)
              SubObjectPropertyOf(ObjectPropertyChain(<e> <e>) <k>)
              IrreflexiveObjectProperty(<v>)
              ObjectPropertyAssertion(<e> <a> <b>)
              ClassAssertion(<A> <a>)
              SubClassOf(<A> ObjectMinCardinality(2 <p> <C>))
            )"#,
        );
        assert!(
            chain_abox.card_number_role_separable,
            "the number-role half is independent of ABox materialization"
        );
        assert!(
            !chain_abox.inverse_cardinality_role_separable,
            "a chain-connected positive assertion still declines the native ABox route"
        );
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
