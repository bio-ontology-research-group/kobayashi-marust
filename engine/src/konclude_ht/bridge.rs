//! # Bridge: `TInput` (cb_to_ht HtClauses) → `OntologyArenas`
//!
//! The production-route input builder for `konclude_ht` — maps KM's
//! reverse-Skolemized HT clause form (`orchestrate::cb_to_ht::TInput`, the
//! same input the fast Ht consumes) onto Konclude-style concept structures
//! (`CCATOM`/`CCIMPL`/`CCOR`/`CCALL`/`CCSOME` operand trees): exactly the
//! encoding `completion::classify_test`'s `Env` builds programmatically, so
//! everything the completion engine already runs (implication unfolding, the
//! OR rule + the sound same-node backtrack, ∃/∀ successor rules) applies
//! unchanged to bridged ontologies.
//!
//! The production `ht_bridge` route reaches this module through the typed
//! orchestrator. Coverage remains deliberately partial: every clause the
//! encoder cannot express is counted in [`Bridged::unsupported`], and the
//! public classification entry points return `None` (DEFER) whenever coverage
//! or an exact fragment certificate fails. Production therefore never emits a
//! taxonomy from an under-approximated bridged ontology.
//!
//! v1 clause coverage (one implication concept per clause, seeded per pass by
//! the re-drive loop exactly like the classify_test GCI harness):
//!   - concept-only clauses over the clause root variable:
//!     `C1 ∧ … ∧ Cn → D1 ∨ … ∨ Dm`  ⇒  `CCIMPL[ head, ¬C1, …, ¬Cn ]` with
//!     `head = Dm | CCOR[D1..Dm] | CCBOTTOM` (heads may be `Exist` ⇒ `CCSOME`);
//!   - single-role-body clauses `…C(0)… ∧ R(0,1) ∧ …D(1)… → …E(0)… ∨ …F(1)…`
//!     ⇒  `CCIMPL[ CCOR[E…, CCALL(R, CCOR[¬D…, F…])], ¬C… ]`
//!     (the standard `∀`-form of a guarded two-variable clause);
//!   - everything else (multiple role atoms, head role atoms / role
//!     hierarchy, `Eq`, body `Exist`, nominals, card_defs, chains) counts as
//!     unsupported in v1.
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use super::classifier::{
    OptimizedKPSetClassSubsumptionClassifierThread, RecordingClassificationMessageDataObserver,
    SynchronousKPSetClassState,
};
use super::completion::algorithm::CompletionTaskHandleAlgorithm;
use super::completion::context::CalculationAlgorithmContextBase;
use super::completion::stubs::SatisfiableTaskClassificationMessageAnalyser;
use super::model::concept::Concept;
use super::model::concept_process::{ConceptProcessData, ReplacementData};
use super::model::individual::{ConceptAssertion, Individual, ReverseRoleAssertion, RoleAssertion};
use super::model::op;
use super::model::role::Role;
use super::model::role_chain::RoleChain;
use super::model::stubs::NameId;
use super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::model::{ConceptId, IndividualId, RoleId};
use super::preprocess::role_chain_automata::RoleChainAutomataTransformationPreProcess;
use super::process::descriptor::{
    ConceptDescriptor, ConceptProcessDescriptor, ConceptProcessPriority,
};
use super::process::node::IndividualProcessNode;
use super::process::queues::ConceptProcessingQueue;
use super::process::NodeId;
use super::task::adapters::{SatisfiableTaskClassificationMessageAdapter, EFEXTRACTALL};
use crate::json_io::DefinerKind;
use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};

type SourceConcept = crate::frontend::syntax::Concept;
type SourceRole = crate::frontend::syntax::Role;

/// The frontend currently carries the OWL built-in top roles through
/// `TInput::roles` as names.  The bridge has no universal-role object: treating
/// one of these names as an ordinary role would be an under-approximation, so
/// every public bridge route must fail closed before constructing an arena.
/// Collision suffixes are included deliberately.  Without the source IRI map,
/// a false positive is preferable to returning an inexact classification.
fn is_builtin_top_role_name(name: &str) -> bool {
    let raw = name.trim_matches(['<', '>']);
    raw == "__U__"
        || raw == "owl:topObjectProperty"
        || raw == "owl:topDataProperty"
        || raw == "http://www.w3.org/2002/07/owl#topObjectProperty"
        || raw == "http://www.w3.org/2002/07/owl#topDataProperty"
        || raw == "topObjectProperty"
        || raw == "topDataProperty"
        || raw.starts_with("owl:topObjectProperty__")
        || raw.starts_with("owl:topDataProperty__")
        || raw.starts_with("topObjectProperty__")
        || raw.starts_with("topDataProperty__")
}

fn is_builtin_bottom_role_name(name: &str) -> bool {
    let raw = name.trim_matches(['<', '>']);
    raw == "owl:bottomObjectProperty"
        || raw == "owl:bottomDataProperty"
        || raw == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
        || raw == "http://www.w3.org/2002/07/owl#bottomDataProperty"
        || raw == "bottomObjectProperty"
        || raw == "bottomDataProperty"
        || raw.starts_with("owl:bottomObjectProperty__")
        || raw.starts_with("owl:bottomDataProperty__")
        || raw.starts_with("bottomObjectProperty__")
        || raw.starts_with("bottomDataProperty__")
}

fn has_builtin_top_role(tin: &TInput) -> bool {
    tin.roles.iter().any(|role| is_builtin_top_role_name(role))
}

/// A fixed datatype abstraction in object position cannot be interpreted as
/// an ordinary, freely chosen OWL class.  Datatype fillers below an ordinary
/// data role are not in object position, but a `DatatypeDefinition` (carried as
/// a source equivalence) is.  Until the bridge has a typed data-domain object,
/// such an input must be deferred by the whole route, not merely rejected by
/// an optional consistency certificate.
fn fixed_datatype_in_object_position(concept: &SourceConcept) -> bool {
    match concept {
        SourceConcept::Name(name) => name.starts_with("__dt__"),
        SourceConcept::Not(operand) => fixed_datatype_in_object_position(operand),
        SourceConcept::And(operands) | SourceConcept::Or(operands) => {
            operands.iter().any(fixed_datatype_in_object_position)
        }
        // An ordinary data role separates the object and data domains, so its
        // filler is not in object position.  The universal role is not an
        // ordinary empty-able data role and therefore preserves the check.
        SourceConcept::Exists(role, filler)
        | SourceConcept::Forall(role, filler)
        | SourceConcept::AtLeast(_, role, filler)
        | SourceConcept::AtMost(_, role, filler) => {
            matches!(role, SourceRole::Universal) && fixed_datatype_in_object_position(filler)
        }
        SourceConcept::Top
        | SourceConcept::Bottom
        | SourceConcept::Nominal(_)
        | SourceConcept::HasSelf(_) => false,
    }
}

fn has_fixed_datatype_object_position(tin: &TInput) -> bool {
    tin.source_axioms.iter().any(|axiom| {
        fixed_datatype_in_object_position(&axiom.left)
            || fixed_datatype_in_object_position(&axiom.right)
    })
}

/// Recognise the exact, role-free clause vocabulary emitted by
/// `frontend::datatypes::datatype_relation_clauses`.  These clauses are not
/// clausifier copies of `source_axioms`: they carry the datatype map's
/// membership, disjointness, finite-cover, and value-singleton consequences.
/// Source mode must therefore retain them.  The `__dt__` namespace is a
/// collision-protected frontend-internal namespace, and the deliberately
/// narrow shape rejects roles, existentials, negated literals, body equality,
/// and mixed object/data concepts.
fn is_pure_internal_datatype_relation_clause(tin: &TInput, clause: &HtClause) -> bool {
    let mut saw_datatype = false;
    for atom in &clause.body {
        match atom {
            HAtom::Concept { neg: false, c, .. }
                if tin
                    .concepts
                    .get(*c)
                    .is_some_and(|name| name.starts_with("__dt__")) =>
            {
                saw_datatype = true;
            }
            _ => return false,
        }
    }
    for atom in &clause.head {
        match atom {
            HAtom::Concept { neg: false, c, .. }
                if tin
                    .concepts
                    .get(*c)
                    .is_some_and(|name| name.starts_with("__dt__")) =>
            {
                saw_datatype = true;
            }
            HAtom::Eq { .. } => {}
            _ => return false,
        }
    }
    saw_datatype
}

fn clause_contains_internal_datatype(tin: &TInput, clause: &HtClause) -> bool {
    clause.body.iter().chain(&clause.head).any(|atom| {
        let concept = match atom {
            HAtom::Concept { c, .. } | HAtom::Exist { c, .. } => Some(*c),
            HAtom::Role { .. } | HAtom::Eq { .. } => None,
        };
        concept.is_some_and(|concept| {
            tin.concepts
                .get(concept)
                .is_some_and(|name| name.starts_with("__dt__"))
        })
    })
}

/// Mirror the source-mode clause suppression used by the terminology builder.
/// Source class axioms, including their datatype restrictions, are
/// reconstructed from `source_axioms`; only pure datatype-map relation clauses
/// and new unit-bottom certificates remain authoritative concept clauses.
/// Keeping this predicate shared prevents the datatype route gate from
/// rejecting a definer-shaped clausifier copy that the builder will never
/// encode.
fn source_mode_suppresses_ordinary_concept_clause(tin: &TInput, clause: &HtClause) -> bool {
    let unit_bottom = matches!(
        (clause.body.as_slice(), clause.head.as_slice()),
        ([HAtom::Concept { neg: false, .. }], [])
    );
    !unit_bottom
        && !is_pure_internal_datatype_relation_clause(tin, clause)
        && clause
            .body
            .iter()
            .chain(&clause.head)
            .any(|atom| matches!(atom, HAtom::Concept { .. } | HAtom::Exist { .. }))
}

struct DependencyComponents {
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl DependencyComponents {
    fn new(len: usize) -> Self {
        Self {
            parent: (0..len).collect(),
            size: vec![1; len],
        }
    }

    fn find(&mut self, mut item: usize) -> usize {
        let mut root = item;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        while self.parent[item] != item {
            let next = self.parent[item];
            self.parent[item] = root;
            item = next;
        }
        root
    }

    fn union(&mut self, left: usize, right: usize) {
        let mut left = self.find(left);
        let mut right = self.find(right);
        if left == right {
            return;
        }
        if self.size[left] < self.size[right] {
            std::mem::swap(&mut left, &mut right);
        }
        self.parent[right] = left;
        self.size[left] += self.size[right];
    }

    fn union_all(&mut self, symbols: &[usize]) {
        if let Some((&first, rest)) = symbols.split_first() {
            for &symbol in rest {
                self.union(first, symbol);
            }
        }
    }
}

fn collect_source_dependency_symbols(
    concept: &SourceConcept,
    concept_index: &HashMap<&str, usize>,
    role_index: &HashMap<&str, usize>,
    role_offset: usize,
    symbols: &mut Vec<usize>,
    forces_existing_element: &mut bool,
) -> bool {
    match concept {
        SourceConcept::Name(name) => match concept_index.get(name.as_str()) {
            Some(&index) => symbols.push(index),
            None => return false,
        },
        SourceConcept::Top | SourceConcept::Bottom => {}
        SourceConcept::Nominal(_) => *forces_existing_element = true,
        SourceConcept::Not(operand) => {
            return collect_source_dependency_symbols(
                operand,
                concept_index,
                role_index,
                role_offset,
                symbols,
                forces_existing_element,
            );
        }
        SourceConcept::And(operands) | SourceConcept::Or(operands) => {
            for operand in operands {
                if !collect_source_dependency_symbols(
                    operand,
                    concept_index,
                    role_index,
                    role_offset,
                    symbols,
                    forces_existing_element,
                ) {
                    return false;
                }
            }
        }
        SourceConcept::Exists(role, filler)
        | SourceConcept::Forall(role, filler)
        | SourceConcept::AtLeast(_, role, filler)
        | SourceConcept::AtMost(_, role, filler) => {
            let role_name = match role {
                SourceRole::Name(name) | SourceRole::Inverse(name) => name,
                SourceRole::Universal => return false,
            };
            let Some(&role) = role_index.get(role_name.as_str()) else {
                return false;
            };
            symbols.push(role_offset + role);
            if !collect_source_dependency_symbols(
                filler,
                concept_index,
                role_index,
                role_offset,
                symbols,
                forces_existing_element,
            ) {
                return false;
            }
        }
        SourceConcept::HasSelf(role) => {
            let role_name = match role {
                SourceRole::Name(name) | SourceRole::Inverse(name) => name,
                SourceRole::Universal => return false,
            };
            let Some(&role) = role_index.get(role_name.as_str()) else {
                return false;
            };
            symbols.push(role_offset + role);
        }
    }
    true
}

/// Fail-closed certificate for using the object completion bridge in the
/// presence of an abstracted OWL datatype map.
///
/// The frontend's datatype clauses are all sound, but unknown datatype
/// relations intentionally emit no clause.  Consequently, merely retaining
/// the emitted relation clauses does not prove completeness for an arbitrary
/// datatype-dependent named class.  Build an undirected symbol dependency
/// graph over every source axiom, normalized clause, structural definer, and
/// RBox side channel.  Every real named class in a component containing a
/// `__dt__` concept must already have an exact positive unit-bottom
/// consequence.  Such a component has no remaining taxonomy subject: setting
/// its object classes empty satisfies the cut, while the unit constraints give
/// the complete UNSAT answers.  A datatype component connected to TOP, a
/// nominal assertion, or any non-certified real class is deferred.
///
/// This is intentionally stronger than necessary.  It is mechanical,
/// ontology-name independent, and false positives only decline this optional
/// route.
fn datatype_effects_covered_by_unit_bottom(tin: &TInput, source_mode: bool) -> bool {
    let datatype_concepts: Vec<usize> = tin
        .concepts
        .iter()
        .enumerate()
        .filter_map(|(index, name)| name.starts_with("__dt__").then_some(index))
        .collect();
    if datatype_concepts.is_empty() {
        return true;
    }
    if !source_mode {
        return false;
    }

    let concept_count = tin.concepts.len();
    let role_offset = concept_count;
    let global = role_offset + tin.roles.len();
    let mut components = DependencyComponents::new(global + 1);
    let concept_index: HashMap<&str, usize> = tin
        .concepts
        .iter()
        .enumerate()
        .map(|(index, name)| (name.as_str(), index))
        .collect();
    let role_index: HashMap<&str, usize> = tin
        .roles
        .iter()
        .enumerate()
        .map(|(index, name)| (name.as_str(), index))
        .collect();

    for axiom in &tin.source_axioms {
        let mut symbols = Vec::new();
        let mut forces_existing_element = matches!(&axiom.left, SourceConcept::Top)
            || (matches!(axiom.kind, crate::json_io::SourceAxiomKind::Equivalent)
                && matches!(&axiom.right, SourceConcept::Top));
        if !collect_source_dependency_symbols(
            &axiom.left,
            &concept_index,
            &role_index,
            role_offset,
            &mut symbols,
            &mut forces_existing_element,
        ) || !collect_source_dependency_symbols(
            &axiom.right,
            &concept_index,
            &role_index,
            role_offset,
            &mut symbols,
            &mut forces_existing_element,
        ) {
            return false;
        }
        if forces_existing_element {
            symbols.push(global);
        }
        components.union_all(&symbols);
    }

    for clause in &tin.clauses {
        let mut symbols = Vec::new();
        for atom in clause.body.iter().chain(&clause.head) {
            match atom {
                HAtom::Concept { c, .. } => {
                    if *c >= concept_count {
                        return false;
                    }
                    symbols.push(*c);
                }
                HAtom::Role { r, .. } => {
                    if *r >= tin.roles.len() {
                        return false;
                    }
                    symbols.push(role_offset + *r);
                }
                HAtom::Exist { r, c, .. } => {
                    if *r >= tin.roles.len() || *c >= concept_count {
                        return false;
                    }
                    symbols.push(role_offset + *r);
                    symbols.push(*c);
                }
                HAtom::Eq { .. } => {}
            }
        }
        if clause.body.is_empty() && !clause.head.is_empty() {
            symbols.push(global);
        }
        components.union_all(&symbols);
    }

    for &(left, right, super_role) in &tin.chains {
        if left >= tin.roles.len() || right >= tin.roles.len() || super_role >= tin.roles.len() {
            return false;
        }
        components.union_all(&[
            role_offset + left,
            role_offset + right,
            role_offset + super_role,
        ]);
    }
    for &(role, concept) in tin.role_domains.iter().chain(&tin.role_ranges) {
        if role >= tin.roles.len() || concept >= concept_count {
            return false;
        }
        components.union(role_offset + role, concept);
    }
    for card in &tin.card_defs {
        if card.marker >= concept_count
            || card.filler >= concept_count
            || card.role >= tin.roles.len()
        {
            return false;
        }
        components.union_all(&[card.marker, card.filler, role_offset + card.role]);
    }
    for definer in &tin.definers {
        let Some(&marker) = concept_index.get(definer.marker.as_str()) else {
            return false;
        };
        let mut symbols = vec![marker];
        for operand in &definer.operands {
            let Some(&operand) = concept_index.get(operand.as_str()) else {
                return false;
            };
            symbols.push(operand);
        }
        if let Some(role) = &definer.role {
            let Some(&role) = role_index.get(role.as_str()) else {
                return false;
            };
            symbols.push(role_offset + role);
        }
        components.union_all(&symbols);
    }
    // A source class assertion forces an existing individual to satisfy its
    // expression.  Link its symbols to the global node; different-individual
    // metadata contains no class or datatype expression.
    for individual in &tin.nominal_abox.individuals {
        for assertion in &individual.assertions {
            let mut symbols = vec![global];
            let mut forces_existing_element = true;
            if !collect_source_dependency_symbols(
                assertion,
                &concept_index,
                &role_index,
                role_offset,
                &mut symbols,
                &mut forces_existing_element,
            ) {
                return false;
            }
            components.union_all(&symbols);
        }
    }

    let certified: std::collections::HashSet<usize> = tin
        .clauses
        .iter()
        .filter_map(
            |clause| match (clause.body.as_slice(), clause.head.as_slice()) {
                ([HAtom::Concept { neg: false, c, .. }], []) if *c < concept_count => Some(*c),
                _ => None,
            },
        )
        .collect();
    let datatype_roots: std::collections::HashSet<usize> = datatype_concepts
        .into_iter()
        .map(|concept| components.find(concept))
        .collect();
    if datatype_roots.contains(&components.find(global)) {
        return false;
    }

    let query_set: std::collections::HashSet<usize> =
        tin.queries.iter().map(|&query| query as usize).collect();
    for (concept, name) in tin.concepts.iter().enumerate() {
        if datatype_roots.contains(&components.find(concept))
            && (query_set.contains(&concept)
                || (!crate::orchestrate::cb_to_ht::is_internal(name)
                    && !crate::orchestrate::cb_to_ht::is_bottom(name)))
            && !certified.contains(&concept)
        {
            return false;
        }
    }
    true
}

fn source_concept_contains_internal_datatype(concept: &SourceConcept) -> bool {
    match concept {
        SourceConcept::Name(name) => name.starts_with("__dt__"),
        SourceConcept::Not(operand) => source_concept_contains_internal_datatype(operand),
        SourceConcept::And(operands) | SourceConcept::Or(operands) => operands
            .iter()
            .any(source_concept_contains_internal_datatype),
        SourceConcept::Exists(_, filler)
        | SourceConcept::Forall(_, filler)
        | SourceConcept::AtLeast(_, _, filler)
        | SourceConcept::AtMost(_, _, filler) => source_concept_contains_internal_datatype(filler),
        SourceConcept::Top
        | SourceConcept::Bottom
        | SourceConcept::Nominal(_)
        | SourceConcept::HasSelf(_) => false,
    }
}

fn source_concept_mentions_roles(
    concept: &SourceConcept,
    roles: &std::collections::HashSet<&str>,
) -> bool {
    match concept {
        SourceConcept::Not(operand) => source_concept_mentions_roles(operand, roles),
        SourceConcept::And(operands) | SourceConcept::Or(operands) => operands
            .iter()
            .any(|operand| source_concept_mentions_roles(operand, roles)),
        SourceConcept::Exists(role, filler)
        | SourceConcept::Forall(role, filler)
        | SourceConcept::AtLeast(_, role, filler)
        | SourceConcept::AtMost(_, role, filler) => {
            let mentioned = match role {
                SourceRole::Name(name) | SourceRole::Inverse(name) => roles.contains(name.as_str()),
                SourceRole::Universal => true,
            };
            mentioned || source_concept_mentions_roles(filler, roles)
        }
        SourceConcept::HasSelf(role) => match role {
            SourceRole::Name(name) | SourceRole::Inverse(name) => roles.contains(name.as_str()),
            SourceRole::Universal => true,
        },
        SourceConcept::Name(_)
        | SourceConcept::Top
        | SourceConcept::Bottom
        | SourceConcept::Nominal(_) => false,
    }
}

fn functional_role_clause(clause: &HtClause, role: usize) -> bool {
    let (
        [HAtom::Role {
            r: first_role,
            s: first_source,
            t: first_target,
        }, HAtom::Role {
            r: second_role,
            s: second_source,
            t: second_target,
        }],
        [HAtom::Eq { s: left, t: right }],
    ) = (clause.body.as_slice(), clause.head.as_slice())
    else {
        return false;
    };
    if *first_role != role
        || *second_role != role
        || first_source != second_source
        || first_target == second_target
    {
        return false;
    }
    (*left == *first_target && *right == *second_target)
        || (*left == *second_target && *right == *first_target)
}

fn positive_datatype_inclusion(clause: &HtClause, sub: usize, sup: usize) -> bool {
    matches!(
        (clause.body.as_slice(), clause.head.as_slice()),
        (
            [HAtom::Concept { neg: false, c: left, t: left_term }],
            [HAtom::Concept { neg: false, c: right, t: right_term }]
        ) if *left == sub && *right == sup && left_term == right_term
    )
}

fn positive_datatype_disjointness(clause: &HtClause, left: usize, right: usize) -> bool {
    let (body, head) = (clause.body.as_slice(), clause.head.as_slice());
    if !head.is_empty() || body.len() != 2 {
        return false;
    }
    let (
        HAtom::Concept {
            neg: false,
            c: first,
            t: first_term,
        },
        HAtom::Concept {
            neg: false,
            c: second,
            t: second_term,
        },
    ) = (&body[0], &body[1])
    else {
        return false;
    };
    first_term == second_term
        && ((*first == left && *second == right) || (*first == right && *second == left))
}

fn datatype_singleton_clause(clause: &HtClause, concept: usize) -> bool {
    let (
        [HAtom::Concept {
            neg: false,
            c: left,
            t: left_term,
        }, HAtom::Concept {
            neg: false,
            c: right,
            t: right_term,
        }],
        [HAtom::Eq {
            s: equal_left,
            t: equal_right,
        }],
    ) = (clause.body.as_slice(), clause.head.as_slice())
    else {
        return false;
    };
    if *left != concept || *right != concept || left_term == right_term {
        return false;
    }
    (*equal_left == *left_term && *equal_right == *right_term)
        || (*equal_left == *right_term && *equal_right == *left_term)
}

fn supported_datatype_clause_shape(tin: &TInput, clause: &HtClause) -> bool {
    if is_pure_internal_datatype_relation_clause(tin, clause) {
        return true;
    }
    match (clause.body.as_slice(), clause.head.as_slice()) {
        ([HAtom::Concept { neg: false, .. }], [HAtom::Exist { neg: false, c, .. }]) => tin
            .concepts
            .get(*c)
            .is_some_and(|name| name.starts_with("__dt__")),
        (body, [HAtom::Concept { neg: false, c, .. }]) if body.len() == 2 => {
            let has_concept = body
                .iter()
                .any(|atom| matches!(atom, HAtom::Concept { neg: false, .. }));
            let has_role = body.iter().any(|atom| matches!(atom, HAtom::Role { .. }));
            has_concept
                && has_role
                && tin
                    .concepts
                    .get(*c)
                    .is_some_and(|name| name.starts_with("__dt__"))
        }
        _ => false,
    }
}

fn datatype_families_provably_disjoint(left: &str, right: &str) -> bool {
    left != right && !matches!((left, right), ("integer", "float") | ("float", "integer"))
}

fn pure_datatype_relation_is_exact(tin: &TInput, clause: &HtClause) -> bool {
    if !is_pure_internal_datatype_relation_clause(tin, clause) {
        return false;
    }
    if let (
        [HAtom::Concept {
            neg: false,
            c: sub,
            t: sub_term,
        }],
        [HAtom::Concept {
            neg: false,
            c: sup,
            t: sup_term,
        }],
    ) = (clause.body.as_slice(), clause.head.as_slice())
    {
        if sub_term != sup_term {
            return false;
        }
        let (Some(sub_name), Some(sup_name)) = (tin.concepts.get(*sub), tin.concepts.get(*sup))
        else {
            return false;
        };
        let sub_value = sub_name.starts_with("__dt__val__");
        let sup_value = sup_name.starts_with("__dt__val__");
        return match (sub_value, sup_value) {
            (true, true) => {
                crate::frontend::datatypes::bridge_exact_value_equal(sub_name, sup_name)
                    == Some(true)
            }
            (true, false) => {
                crate::frontend::datatypes::bridge_exact_atomic_family(sub_name)
                    == crate::frontend::datatypes::bridge_exact_atomic_family(sup_name)
            }
            (false, false) => crate::frontend::datatypes::bridge_exact_atomic_family(sub_name)
                .zip(crate::frontend::datatypes::bridge_exact_atomic_family(
                    sup_name,
                ))
                .is_some_and(|(sub_family, sup_family)| sub_family == sup_family),
            (false, true) => false,
        };
    }
    if clause.head.is_empty() && clause.body.len() == 2 {
        let (
            HAtom::Concept {
                neg: false,
                c: left,
                t: left_term,
            },
            HAtom::Concept {
                neg: false,
                c: right,
                t: right_term,
            },
        ) = (&clause.body[0], &clause.body[1])
        else {
            return false;
        };
        if left_term != right_term {
            return false;
        }
        let (Some(left_name), Some(right_name)) =
            (tin.concepts.get(*left), tin.concepts.get(*right))
        else {
            return false;
        };
        let left_value = left_name.starts_with("__dt__val__");
        let right_value = right_name.starts_with("__dt__val__");
        if left_value && right_value {
            return crate::frontend::datatypes::bridge_exact_value_equal(left_name, right_name)
                == Some(false);
        }
        let (Some(left_family), Some(right_family)) = (
            crate::frontend::datatypes::bridge_exact_atomic_family(left_name),
            crate::frontend::datatypes::bridge_exact_atomic_family(right_name),
        ) else {
            return false;
        };
        return datatype_families_provably_disjoint(left_family, right_family);
    }
    if clause.body.len() == 2 && clause.head.len() == 1 {
        // The only exact equality-head shape is a value singleton.
        return tin.concepts.iter().enumerate().any(|(concept, name)| {
            name.starts_with("__dt__val__") && datatype_singleton_clause(clause, concept)
        });
    }
    if let ([HAtom::Concept { neg: false, c, t }], head) =
        (clause.body.as_slice(), clause.head.as_slice())
    {
        let Some(range_name) = tin.concepts.get(*c) else {
            return false;
        };
        if crate::frontend::datatypes::bridge_exact_atomic_family(range_name) != Some("boolean")
            || range_name.starts_with("__dt__val__")
            || head.len() != 2
        {
            return false;
        }
        let mut values = Vec::new();
        for atom in head {
            let HAtom::Concept {
                neg: false,
                c: value,
                t: value_term,
            } = atom
            else {
                return false;
            };
            if value_term != t {
                return false;
            }
            let Some(value_name) = tin.concepts.get(*value) else {
                return false;
            };
            if !value_name.starts_with("__dt__val__")
                || crate::frontend::datatypes::bridge_exact_atomic_family(value_name)
                    != Some("boolean")
            {
                return false;
            }
            values.push(value_name);
        }
        return crate::frontend::datatypes::bridge_exact_value_equal(values[0], values[1])
            == Some(false);
    }
    false
}

/// Evaluate an object-language concept on one fresh data-domain element in
/// the separated OWL interpretation used by the exact atomic-datatype route.
/// Ordinary classes and nominals have no data-domain instances, and ordinary
/// object/data roles have no outgoing edge from this element. The built-in
/// universal role cannot be represented by that witness and therefore makes
/// the certificate fail closed.
fn blank_data_node_holds(concept: &SourceConcept) -> Option<bool> {
    Some(match concept {
        SourceConcept::Name(_) | SourceConcept::Bottom | SourceConcept::Nominal(_) => false,
        SourceConcept::Top => true,
        SourceConcept::Not(operand) => !blank_data_node_holds(operand)?,
        SourceConcept::And(operands) => {
            for operand in operands {
                if !blank_data_node_holds(operand)? {
                    return Some(false);
                }
            }
            true
        }
        SourceConcept::Or(operands) => {
            for operand in operands {
                if blank_data_node_holds(operand)? {
                    return Some(true);
                }
            }
            false
        }
        SourceConcept::Exists(role, _) => match role {
            SourceRole::Name(_) | SourceRole::Inverse(_) => false,
            SourceRole::Universal => return None,
        },
        SourceConcept::Forall(role, _) => match role {
            SourceRole::Name(_) | SourceRole::Inverse(_) => true,
            SourceRole::Universal => return None,
        },
        SourceConcept::AtLeast(cardinality, role, _) => match role {
            SourceRole::Name(_) | SourceRole::Inverse(_) => *cardinality <= 0,
            SourceRole::Universal => return None,
        },
        SourceConcept::AtMost(cardinality, role, _) => match role {
            SourceRole::Name(_) | SourceRole::Inverse(_) => 0 <= *cardinality,
            SourceRole::Universal => return None,
        },
        SourceConcept::HasSelf(role) => match role {
            SourceRole::Name(_) | SourceRole::Inverse(_) => false,
            SourceRole::Universal => return None,
        },
    })
}

/// Complete datatype fragment used by the 10621 route.  The accepted syntax
/// is intentionally atomic and role-local:
///
/// * `NamedClass <= exists(dataRole, atomic value/range)`;
/// * `Top <= forall(dataRole, atomic range)`;
/// * at most one range family per data role;
/// * boolean/integer/string literals and boolean/integer/string/float ranges;
/// * no datatype cardinality, definition, Boolean range expression, nominal
///   assertion, or unsupported normalized clause shape.
///
/// It then checks the concrete relation-clause evidence rather than assuming
/// the frontend emitted it: every value is a singleton, every value pair is
/// proved equal or disjoint, each value belongs to its present family range,
/// and boolean has its exact two-value cover.  This is a reusable syntactic
/// certificate, not an ontology-name special case.
fn exact_atomic_datatype_bridge_fragment(tin: &TInput, source_mode: bool) -> bool {
    macro_rules! defer {
        ($reason:literal) => {{
            if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                eprintln!("BRIDGE-DATATYPE-DEFER: {}", $reason);
            }
            return false;
        }};
    }

    let datatype_ids: Vec<usize> = tin
        .concepts
        .iter()
        .enumerate()
        .filter_map(|(index, name)| name.starts_with("__dt__").then_some(index))
        .collect();
    if datatype_ids.is_empty() {
        return true;
    }
    if !source_mode
        || datatype_ids.iter().any(|&concept| {
            !crate::frontend::datatypes::bridge_exact_atomic_name(&tin.concepts[concept])
        })
    {
        defer!("source mode is disabled or a datatype symbol is not in the exact atomic map");
    }

    let role_index: HashMap<&str, usize> = tin
        .roles
        .iter()
        .enumerate()
        .map(|(index, name)| (name.as_str(), index))
        .collect();
    let mut role_ranges: HashMap<usize, &'static str> = HashMap::new();
    let mut role_existentials: Vec<(usize, &'static str)> = Vec::new();
    fn atomic_datatype_existential(concept: &SourceConcept) -> Option<(&str, &'static str)> {
        let SourceConcept::Exists(SourceRole::Name(role), filler) = concept else {
            return None;
        };
        let SourceConcept::Name(datatype) = filler.as_ref() else {
            return None;
        };
        crate::frontend::datatypes::bridge_exact_atomic_family(datatype)
            .map(|family| (role.as_str(), family))
    }
    for axiom in &tin.source_axioms {
        if !source_concept_contains_internal_datatype(&axiom.left)
            && !source_concept_contains_internal_datatype(&axiom.right)
        {
            continue;
        }
        let mut occurrences: Vec<(&str, &'static str, bool)> = Vec::new();
        match (axiom.kind, &axiom.left, &axiom.right) {
            (crate::json_io::SourceAxiomKind::SubClass, SourceConcept::Name(left), right)
                if !left.starts_with("__dt__") =>
            {
                let Some((role, family)) = atomic_datatype_existential(right) else {
                    defer!("a datatype existential has a non-atomic filler");
                };
                occurrences.push((role, family, false));
            }
            (
                crate::json_io::SourceAxiomKind::SubClass,
                SourceConcept::Top,
                SourceConcept::Forall(SourceRole::Name(role), filler),
            ) => {
                let SourceConcept::Name(datatype) = filler.as_ref() else {
                    defer!("a datatype range has a non-atomic filler");
                };
                let Some(family) = crate::frontend::datatypes::bridge_exact_atomic_family(datatype)
                else {
                    defer!("a datatype range filler has no exact family");
                };
                occurrences.push((role.as_str(), family, true));
            }
            // Normalization retains an exact source equivalence such as
            // `N = M and dataHasValue(r,v)` as one source axiom. Its datatype
            // obligation is still role-local and atomic; the remaining
            // conjuncts stay in the ordinary source terminology. Accept every
            // datatype-bearing top-level conjunct only when it has that exact
            // existential shape.
            (
                crate::json_io::SourceAxiomKind::Equivalent,
                SourceConcept::Name(left),
                SourceConcept::And(conjuncts),
            )
            | (
                crate::json_io::SourceAxiomKind::Equivalent,
                SourceConcept::And(conjuncts),
                SourceConcept::Name(left),
            ) if !left.starts_with("__dt__") => {
                for conjunct in conjuncts
                    .iter()
                    .filter(|conjunct| source_concept_contains_internal_datatype(conjunct))
                {
                    let Some((role, family)) = atomic_datatype_existential(conjunct) else {
                        defer!("a datatype equivalence conjunct is not an atomic existential");
                    };
                    occurrences.push((role, family, false));
                }
            }
            _ => defer!("a datatype source axiom is outside the role-local fragment"),
        }
        if occurrences.is_empty() {
            defer!("a datatype source axiom has no exact role-local occurrence");
        }
        for (role, family, is_range) in occurrences {
            let Some(&role) = role_index.get(role) else {
                defer!("a datatype source role is absent from TInput roles");
            };
            if is_range {
                if role_ranges
                    .insert(role, family)
                    .is_some_and(|old| old != family)
                {
                    defer!("one data role has conflicting range families");
                }
            } else {
                role_existentials.push((role, family));
            }
        }
    }
    if role_existentials
        .iter()
        .any(|&(role, family)| role_ranges.get(&role).is_some_and(|range| *range != family))
    {
        defer!("a datatype existential conflicts with its role range");
    }

    let datatype_roles: std::collections::HashSet<usize> = role_ranges
        .keys()
        .copied()
        .chain(role_existentials.iter().map(|&(role, _)| role))
        .collect();
    let datatype_role_names: std::collections::HashSet<&str> = datatype_roles
        .iter()
        .map(|&role| tin.roles[role].as_str())
        .collect();
    fn data_role_uses_are_safe_cardinality_only(
        concept: &SourceConcept,
        datatype_roles: &std::collections::HashSet<&str>,
    ) -> bool {
        if !source_concept_mentions_roles(concept, datatype_roles) {
            return true;
        }
        match concept {
            SourceConcept::And(conjuncts) | SourceConcept::Or(conjuncts) => conjuncts
                .iter()
                .all(|conjunct| data_role_uses_are_safe_cardinality_only(conjunct, datatype_roles)),
            SourceConcept::AtLeast(0..=2, SourceRole::Name(role), filler)
            | SourceConcept::AtMost(0..=2, SourceRole::Name(role), filler)
                if datatype_roles.contains(role.as_str())
                    && matches!(filler.as_ref(), SourceConcept::Top) =>
            {
                true
            }
            SourceConcept::Exists(SourceRole::Name(role), filler)
            | SourceConcept::Forall(SourceRole::Name(role), filler)
                if !datatype_roles.contains(role.as_str()) =>
            {
                data_role_uses_are_safe_cardinality_only(filler, datatype_roles)
            }
            SourceConcept::AtLeast(_, SourceRole::Name(role), filler)
            | SourceConcept::AtMost(_, SourceRole::Name(role), filler)
                if !datatype_roles.contains(role.as_str()) =>
            {
                data_role_uses_are_safe_cardinality_only(filler, datatype_roles)
            }
            _ => false,
        }
    }

    // Data successors share the completion graph implementation with object
    // successors. Prove that every non-datatype source axiom holds on a fresh
    // data element when all object concepts, nominals, and ordinary outgoing
    // roles are empty. Checking only Top-left GCIs is insufficient: for
    // example, `not(A) <= Bottom` is false on that element and would let the
    // untyped completion graph manufacture an object/data-domain clash.
    //
    // Separately, the only non-dt source use allowed on a data role is its
    // ordinary property-domain axiom `exists(role, Top) <= NamedClass`,
    // evaluated at the object predecessor.
    for (axiom_index, axiom) in tin.source_axioms.iter().enumerate() {
        if source_concept_contains_internal_datatype(&axiom.left)
            || source_concept_contains_internal_datatype(&axiom.right)
        {
            continue;
        }
        let (Some(left), Some(right)) = (
            blank_data_node_holds(&axiom.left),
            blank_data_node_holds(&axiom.right),
        ) else {
            defer!("a non-datatype axiom cannot be evaluated on a blank data node");
        };
        let satisfied = match axiom.kind {
            crate::json_io::SourceAxiomKind::SubClass => !left || right,
            crate::json_io::SourceAxiomKind::Equivalent => left == right,
            crate::json_io::SourceAxiomKind::Disjoint => !(left && right),
        };
        if !satisfied {
            defer!("a non-datatype axiom rejects a blank data node");
        }
        if source_concept_mentions_roles(&axiom.left, &datatype_role_names)
            || source_concept_mentions_roles(&axiom.right, &datatype_role_names)
        {
            let allowed_domain = matches!(
                (axiom.kind, &axiom.left, &axiom.right),
                (
                    crate::json_io::SourceAxiomKind::SubClass,
                    SourceConcept::Exists(SourceRole::Name(role), filler),
                    right
                ) if datatype_role_names.contains(role.as_str())
                    && matches!(filler.as_ref(), SourceConcept::Top)
                    && !source_concept_contains_internal_datatype(right)
                    && !source_concept_mentions_roles(right, &datatype_role_names)
            );
            // Objectification preserves bounds zero through two over Top.
            // Every admitted atomic datatype family contains at least two
            // values, and exact singleton relation clauses retain equality and
            // clashes between fixed values. Recurse through ordinary-role
            // fillers, but keep larger data bounds and non-Top data fillers
            // fail-closed.
            let allowed_safe_cardinality =
                data_role_uses_are_safe_cardinality_only(&axiom.left, &datatype_role_names)
                    && data_role_uses_are_safe_cardinality_only(&axiom.right, &datatype_role_names);
            if !allowed_domain && !allowed_safe_cardinality {
                if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                    eprintln!(
                        "BRIDGE-DATATYPE-DEFER: a data role occurs outside an exact datatype \
                         or object-domain axiom; source_axiom={axiom_index} value={axiom:?}"
                    );
                }
                return false;
            }
        }
    }

    if tin.chains.iter().any(|&(left, right, super_role)| {
        datatype_roles.contains(&left)
            || datatype_roles.contains(&right)
            || datatype_roles.contains(&super_role)
    }) || tin
        .transitive
        .iter()
        .any(|role| datatype_roles.contains(role))
    {
        defer!("a data role participates in a chain or transitivity axiom");
    }
    for &(role, concept) in &tin.role_ranges {
        if !datatype_roles.contains(&role) {
            continue;
        }
        let Some(name) = tin.concepts.get(concept) else {
            defer!("a data-role range concept index is invalid");
        };
        let Some(family) = crate::frontend::datatypes::bridge_exact_atomic_family(name) else {
            defer!("a data-role range has no exact atomic family");
        };
        if role_ranges.get(&role) != Some(&family) {
            defer!("source and side-channel data-role ranges disagree");
        }
    }

    // Apart from exact datatype-bearing copies, a data role may occur only in
    // its functionality clause or its object-domain clause.  This excludes
    // subproperty, inverse, chain, and object-range interactions that would
    // invalidate the role-local datatype model.
    for (clause_index, clause) in tin.clauses.iter().enumerate() {
        if clause_contains_internal_datatype(tin, clause) {
            continue;
        }
        if source_mode_suppresses_ordinary_concept_clause(tin, clause) {
            continue;
        }
        let touched: Vec<usize> = clause
            .body
            .iter()
            .chain(&clause.head)
            .filter_map(|atom| match atom {
                HAtom::Role { r, .. } | HAtom::Exist { r, .. } if datatype_roles.contains(r) => {
                    Some(*r)
                }
                _ => None,
            })
            .collect();
        if touched.is_empty() {
            continue;
        }
        let functional = touched
            .iter()
            .copied()
            .any(|role| functional_role_clause(clause, role));
        let domain = matches!(
            (clause.body.as_slice(), clause.head.as_slice()),
            (
                [HAtom::Role { r, s, .. }],
                [HAtom::Concept {
                    neg: false,
                    c,
                    t,
                }]
            ) if datatype_roles.contains(r)
                && s == t
                && tin
                    .concepts
                    .get(*c)
                    .is_some_and(|name| !name.starts_with("__dt__"))
        );
        if !functional && !domain {
            if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                let encoded = serde_json::to_string(clause)
                    .unwrap_or_else(|_| "<serialization failed>".to_string());
                eprintln!(
                    "BRIDGE-DATATYPE-DEFER: a data role occurs in an unsupported \
                     non-datatype clause; clause={clause_index} touched={touched:?} \
                     value={encoded}"
                );
            }
            return false;
        }
    }

    if tin.nominal_abox.individuals.iter().any(|individual| {
        individual
            .assertions
            .iter()
            .any(source_concept_contains_internal_datatype)
    }) {
        defer!("a nominal assertion contains a datatype expression");
    }
    if tin.card_defs.iter().any(|card| {
        [card.marker, card.filler].into_iter().any(|concept| {
            tin.concepts
                .get(concept)
                .is_some_and(|name| name.starts_with("__dt__"))
        })
    }) {
        defer!("a cardinality side channel contains a datatype marker or filler");
    }
    for (clause_index, clause) in tin.clauses.iter().enumerate() {
        if clause_contains_internal_datatype(tin, clause)
            && !source_mode_suppresses_ordinary_concept_clause(tin, clause)
            && !supported_datatype_clause_shape(tin, clause)
        {
            if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                let encoded = serde_json::to_string(clause)
                    .unwrap_or_else(|_| "<serialization failed>".to_string());
                eprintln!(
                    "BRIDGE-DATATYPE-DEFER: a datatype-bearing clause has an unsupported \
                     shape; clause={clause_index} value={encoded}"
                );
            }
            return false;
        }
    }
    for (clause_index, clause) in tin.clauses.iter().enumerate() {
        if is_pure_internal_datatype_relation_clause(tin, clause)
            && !pure_datatype_relation_is_exact(tin, clause)
        {
            if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                let encoded = serde_json::to_string(clause)
                    .unwrap_or_else(|_| "<serialization failed>".to_string());
                eprintln!(
                    "BRIDGE-DATATYPE-DEFER: a pure datatype relation clause is not exact \
                     in the supported map; clause={clause_index} value={encoded}"
                );
            }
            return false;
        }
    }

    let values: Vec<usize> = datatype_ids
        .iter()
        .copied()
        .filter(|&concept| tin.concepts[concept].starts_with("__dt__val__"))
        .collect();
    let mut ranges: HashMap<&'static str, Vec<usize>> = HashMap::new();
    for &concept in datatype_ids
        .iter()
        .filter(|&&concept| !tin.concepts[concept].starts_with("__dt__val__"))
    {
        let Some(family) =
            crate::frontend::datatypes::bridge_exact_atomic_family(&tin.concepts[concept])
        else {
            defer!("a datatype range has no exact atomic family");
        };
        ranges.entry(family).or_default().push(concept);
    }

    for &value in &values {
        if !tin
            .clauses
            .iter()
            .any(|clause| datatype_singleton_clause(clause, value))
        {
            defer!("a datatype value lacks its singleton equality clause");
        }
        let Some(family) =
            crate::frontend::datatypes::bridge_exact_atomic_family(&tin.concepts[value])
        else {
            defer!("a datatype value has no exact atomic family");
        };
        if let Some(family_ranges) = ranges.get(family) {
            for &range in family_ranges {
                if !tin
                    .clauses
                    .iter()
                    .any(|clause| positive_datatype_inclusion(clause, value, range))
                {
                    defer!("a datatype value lacks membership in its present family range");
                }
            }
        }
    }
    for (position, &left) in values.iter().enumerate() {
        for &right in values.iter().skip(position + 1) {
            let equal = tin.clauses.iter().any(|clause| {
                positive_datatype_inclusion(clause, left, right)
                    && tin
                        .clauses
                        .iter()
                        .any(|reverse| positive_datatype_inclusion(reverse, right, left))
            });
            let disjoint = tin
                .clauses
                .iter()
                .any(|clause| positive_datatype_disjointness(clause, left, right));
            if !equal && !disjoint {
                defer!("a datatype value pair is neither proved equal nor disjoint");
            }
        }
    }

    if let Some(boolean_ranges) = ranges.get("boolean") {
        let boolean_values: BTreeSet<usize> = values
            .iter()
            .copied()
            .filter(|&value| {
                crate::frontend::datatypes::bridge_exact_atomic_family(&tin.concepts[value])
                    == Some("boolean")
            })
            .collect();
        if boolean_values.len() != 2
            || boolean_ranges.iter().any(|boolean| {
                !tin.clauses.iter().any(|clause| {
                    let ([HAtom::Concept { neg: false, c, t }], head) =
                        (clause.body.as_slice(), clause.head.as_slice())
                    else {
                        return false;
                    };
                    c == boolean
                        && head.len() == 2
                        && head.iter().all(|atom| {
                            matches!(atom, HAtom::Concept { neg: false, c, t: ht }
                                if *ht == *t && boolean_values.contains(c))
                        })
                })
            })
        {
            defer!("the boolean family lacks an exact two-value cover");
        }
    }
    true
}

fn datatype_bridge_route_exact(tin: &TInput, source_mode: bool) -> bool {
    exact_atomic_datatype_bridge_fragment(tin, source_mode)
        || datatype_effects_covered_by_unit_bottom(tin, source_mode)
}

/// The bridged terminology: arena ids for the TInput's named concepts/roles
/// plus the per-clause implication concepts the probe driver re-seeds.
pub struct Bridged {
    /// `named[i]` = the `CCATOM` concept for `TInput.concepts[i]`.
    pub named: Vec<ConceptId>,
    /// `roles[i]` = the arena role for `TInput.roles[i]`.
    pub roles: Vec<RoleId>,
    /// One implication (`CCIMPL`) concept per encoded clause — the TBox the
    /// driver seeds on every re-drive pass (the classify_test GCI harness
    /// pattern; stands in for the unported condensed reapply queue).
    pub tbox: Vec<ConceptId>,
    /// Clauses the v1 encoder could NOT express. `> 0` ⇒ the bridged ontology
    /// under-approximates the input: "satisfiable" verdicts are unreliable.
    pub unsupported: usize,
    /// Implications absorbed onto their first positive trigger concept
    /// (`CCATOM` host promoted to `CCSUB`; see the attachment pass) — these
    /// are unfolded only in nodes whose label contains the trigger.
    pub absorbed: usize,
    /// Implications with no positive concept trigger, attached to the
    /// ontology TOP concept (scanned by EVERY node).
    pub top_attached: usize,
    /// Singleton concepts (`C(x) ∧ C(y) → x = y` clause shape — datatype
    /// value identity): consumed by the kernel's deterministic
    /// scan-at-fixpoint merge; must be installed on every probe algorithm.
    pub singleton_concepts: Vec<ConceptId>,
    /// True when the terminology was built from normalized source axioms.
    /// Native CCSUB/trigger/range links reach queue fixpoint in one completion
    /// task and do not need the legacy clause re-drive repair.
    pub source_tbox: bool,
    /// Named concepts proved empty by an exact normalized unit constraint
    /// `C(x) -> bottom`. Source-mode reconstruction normally suppresses
    /// concept clauses duplicated by `source_axioms`, but these also include
    /// new consequences certified by the frontend bottom prepass. They must
    /// remain in the terminology and can answer the corresponding taxonomy
    /// subjects without a tableau probe.
    certified_unsatisfiable: Vec<usize>,
    /// Native ontology individuals that must be reconstructed in every probe.
    /// Empty retains the historical nominal-free bridge behaviour.
    nominal_seeds: Vec<NominalSeed>,
    /// Mixed cardinality+ABox tasks copy positive assertion-role linkers
    /// directly. Nominal-only tasks retain the previously validated
    /// `exists R.{b}` completion encoding.
    direct_native_role_assertions: bool,
    /// Explicit OWL inequalities. Absence never implies inequality (no UNA).
    nominal_different: Vec<(Cint64, Cint64)>,
    /// Konclude's representative-backend association written by the ABox
    /// individual-saturation jobs and read by every later full-completion
    /// graph. `RefCell` mirrors the precomputation lifecycle: saturation owns
    /// the one write, while probe resets only read the immutable association.
    native_representative_cache: RefCell<Option<NativeAboxRepresentativeCache>>,
    /// Immutable-by-value copy of the completed ontology-consistency graph's
    /// non-deterministic nominal-label prefixes. Konclude exposes these only
    /// after individual saturation, representative-cache recomputation, and
    /// the authoritative full consistency task have finished.
    native_consistency_nominal_nondeterministic_prefix:
        RefCell<Option<HashMap<Cint64, Vec<(ConceptId, bool)>>>>,
}

#[derive(Clone)]
struct NominalSeed {
    individual: IndividualId,
    individual_tag: Cint64,
    nominal_concept: ConceptId,
    /// Completion concept assertions. Positive object-property assertions use
    /// `exists R.{b}` only on the legacy nominal-only profile; the mixed
    /// cardinality+ABox profile copies their typed role linkers directly.
    assertions: Vec<(ConceptId, bool)>,
    /// Saturation's native ABox edge view. Keeping these separate prevents a
    /// positive edge from being represented both as a real named neighbour and
    /// as an anonymous existential successor.
    role_assertions: Vec<(RoleId, Cint64)>,
}

impl Bridged {
    fn has_native_nominals(&self) -> bool {
        !self.nominal_seeds.is_empty()
    }
}

/// One representative-memory neighbour-role-set label.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct NativeAboxNeighbourRoleSet {
    neighbour_tag: Cint64,
    /// `(role, inversed)` entries, sorted by role id then polarity.
    roles: Vec<(RoleId, bool)>,
    /// Exact backend cache values for this neighbour role-set label.
    role_values: Option<Vec<NativeAboxRoleValue>>,
    /// `connIndiDetMerged` used while Konclude creates these values. `false`
    /// requires every role value contributed through this alias to remain
    /// nondeterministic.
    merged_alias_deterministic: Option<bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NativeAboxRoleValue {
    role: RoleId,
    inversed: bool,
    deterministic: bool,
}

/// One value of Konclude's `FULL_CONCEPT_SET_LABEL`. Completion writeback must
/// retain the cache-value determinism bit; replaying a branch-dependent value
/// with the base dependency would turn one model choice into an entailment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NativeAboxConceptValue {
    concept: ConceptId,
    negated: bool,
    deterministic: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NativeAboxAssociationOrigin {
    IndividualSaturation,
    CompletionWriteback,
}

/// The typed subset of
/// `CBackendRepresentativeMemoryCacheIndividualAssociationData` consumed by
/// the bridge's full-completion path.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct NativeAboxRepresentativeEntry {
    individual_tag: Cint64,
    /// FULL_CONCEPT_SET_LABEL.
    concepts: Vec<(ConceptId, bool)>,
    /// Exact cache values, including the deterministic/non-deterministic
    /// identifier. `None` means that label family was not serialized and keeps
    /// the association fail-closed.
    concept_values: Option<Vec<NativeAboxConceptValue>>,
    /// COMBINED_INSTANTIATED_ROLE_SET_LABEL.
    instantiated_roles: Vec<RoleId>,
    instantiated_role_values: Option<Vec<NativeAboxRoleValue>>,
    /// COMBINED_EXISTENTIAL_INSTANTIATED_ROLE_SET_LABEL.
    existential_roles: Vec<RoleId>,
    existential_role_values: Option<Vec<NativeAboxRoleValue>>,
    /// CARDINALITY_ASSOCIATION_DATA, minimum upper bound per role.
    at_most_cardinalities: Vec<(RoleId, Cint64)>,
    /// CARDINALITY_ASSOCIATION_DATA, maximum existential cardinality already
    /// represented by the cached completion label, per role.
    existential_max_cardinalities: Vec<(RoleId, Cint64)>,
    /// INDIRECTLY_CONNECTED_NOMINAL_INDIVIDUAL_SET_LABEL.
    indirect_nominal_connections: Vec<Cint64>,
    /// NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL.
    neighbour_role_combinations: Vec<NativeAboxNeighbourRoleSet>,
    /// Konclude's association-status triple. `completely_propagated` is
    /// independent metadata; the expansion-blocking status conjunct is
    /// `completely_handled`.
    completely_saturated: bool,
    completely_handled: bool,
    completely_propagated: bool,
    insufficient: bool,
    /// `hasRepresentativeSameIndividualMerging()`. `None` is deliberately
    /// unknown/fail-closed; the native ABox route currently rejects source
    /// `SameIndividual`, so its saturation writer records `Some(false)`.
    representative_same_individual_merging: Option<bool>,
    /// Pointer identity of
    /// `DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL`. These are identities rather
    /// than only equal contents because Konclude's blocking gate compares the
    /// two cache-entry pointers.
    deterministic_same_individual_label_identity: Option<u64>,
    /// Pointer identity returned by
    /// `getDeterministicMergedSameConsideredLabelCacheEntry()`.
    deterministic_merged_same_considered_label_identity: Option<u64>,
    /// Canonical contents behind the two identities above. Pointer equality in
    /// Konclude implies canonical-label equality; retaining the contents avoids
    /// relying on a potentially colliding numeric fingerprint.
    deterministic_same_individuals: Option<Vec<Cint64>>,
    deterministic_merged_same_considered_individuals: Option<Vec<Cint64>>,
    nondeterministic_same_individuals: Option<Vec<Cint64>>,
    deterministic_different_individuals: Option<Vec<Cint64>>,
    nondeterministic_different_individuals: Option<Vec<Cint64>>,
    representative_same_individual_id: Option<Cint64>,
    deterministic_same_individual_id: Option<Cint64>,
    /// Exact completion-node status captured by the successful association
    /// writer. Saturation associations use `None` because their status is held
    /// by the saturation flag words instead.
    completion_processing_restriction_flags: Option<Cint64>,
    completion_label_descriptor_count: Option<usize>,
    /// Cache update/synchronization metadata corresponding to
    /// `usedAssociationUpdateId` and the representative adapter's scheduled
    /// bit.
    association_update_id: u64,
    used_association_update_id: Option<u64>,
    scheduled_individual: Option<bool>,
    association_origin: Option<NativeAboxAssociationOrigin>,
    /// These gates are set only when the writer serialized every field that
    /// the current bridge reader relies on. An unsupported merge/link/sync
    /// shape leaves the entry present but incomplete.
    merge_identity_metadata_complete: bool,
    role_metadata_complete: bool,
    synchronization_metadata_complete: bool,
}

impl NativeAboxRepresentativeEntry {
    fn complete_for_precomputation(&self) -> bool {
        self.completely_handled
            && self.concept_values.is_some()
            && self.merge_identity_metadata_complete
            && self.role_metadata_complete
            && self.synchronization_metadata_complete
            && match (
                self.representative_same_individual_merging,
                self.representative_same_individual_id,
                self.deterministic_same_individual_id,
            ) {
                (Some(false), Some(representative), Some(deterministic)) => {
                    representative == self.individual_tag && deterministic == self.individual_tag
                }
                (Some(true), Some(representative), Some(deterministic)) => {
                    representative != self.individual_tag && deterministic == representative
                }
                _ => false,
            }
            && self
                .deterministic_same_individual_label_identity
                .zip(self.deterministic_merged_same_considered_label_identity)
                .is_some_and(|(same, considered)| same == considered)
            && self.deterministic_same_individuals.is_some()
            && self.deterministic_same_individuals
                == self.deterministic_merged_same_considered_individuals
    }

    fn reusable_for_full_completion(&self) -> bool {
        self.complete_for_precomputation()
            && self.representative_same_individual_merging == Some(false)
        // Konclude's `tryEstablishExpansionBlockingWithBackendCacheSynchronisation`
        // does not inspect the non-deterministic same-individual label here.
        // The exact blocking predicate is complete handling, no
        // representative-same merge, canonical deterministic-same identity, and
        // concept-label synchronization (the latter is checked by the caller).
        //
        // KONCLUDE-PORT-NOTE[reuse]: the backend-expansion REUSE queue is a
        // different mechanism from this blocking predicate and is NOT off by
        // default upstream — `mConfBackendExpansionReuse` is a ctor `true`
        // (cpp 514) and `mOptBackendExpansionReuse` is switched on for every
        // task carrying a representative-backend updating adapter (cpp 844-845),
        // with the late-dynamic arm at cpp 22892-22924 setting the DATABOX flag
        // `setBackendIndividualLateReuseExpansionActivated(true)`, which
        // `initProcessingDataBox(parent)` (cpp 453) then propagates to every
        // derived task including the class jobs. See `has_reusable_elements`.
    }

    /// Konclude's `hasReuseableElements` (cpp 22884-22916): does this
    /// association carry any NON-deterministic content that a later task could
    /// replay instead of re-deriving? Konclude reads exactly four slots —
    /// non-deterministic elements in `FULL_CONCEPT_SET_LABEL`, a
    /// `NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL`, a
    /// `NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL`, and a
    /// `NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL` — and queues the node
    /// for `reuseIndividualBackendExpansion` (cpp 25092-25373) when any is set.
    ///
    /// KM writes all four (see `write_completed_native_representative_associations`)
    /// and reads none of them: `replay_native_representative_cache` filters to
    /// `value.deterministic`, and `u25::reuse_individual_backend_expansion` is a
    /// PORT-PENDING stub. This predicate exists so the gap is measurable before
    /// it is closed.
    fn has_reusable_elements(&self) -> bool {
        let nondeterministic_concepts = self
            .concept_values
            .as_ref()
            .is_some_and(|values| values.iter().any(|value| !value.deterministic));
        nondeterministic_concepts
            || self.has_nondeterministic_neighbour_roles()
            || self
                .nondeterministic_same_individuals
                .as_ref()
                .is_some_and(|values| !values.is_empty())
            || self
                .nondeterministic_different_individuals
                .as_ref()
                .is_some_and(|values| !values.is_empty())
    }

    /// The `NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL`
    /// slot, i.e. the neighbour role links Konclude's reuse expansion re-creates
    /// at cpp 25318-25440. In the Stage-2 trace this slot is set on 86 of the
    /// 198 associations (`ANALYSIS.md` section 4).
    fn has_nondeterministic_neighbour_roles(&self) -> bool {
        self.neighbour_role_combinations.iter().any(|combination| {
            combination
                .role_values
                .as_ref()
                .is_some_and(|values| values.iter().any(|value| !value.deterministic))
        })
    }

    /// FAIL-CLOSED gate for `u25::reuse_individual_backend_expansion`: every
    /// slot that replay reads must be present with its determinism bit, and the
    /// association must be completely handled (Konclude only reaches the reuse
    /// queue under `indiAssData->isCompletelyHandled()`, cpp 22710).
    ///
    /// Konclude's cache is authoritative, so it has no equivalent test — a
    /// missing label there simply means the slot is empty. The bridge's typed
    /// record uses `None` for "the writer could not serialize this exactly", so
    /// `None` must NOT be read as "empty": replaying a model with a silently
    /// dropped merge, link or distinction under one non-deterministic track
    /// point would assert a state the recorded model never had.
    fn reuse_replay_representable(&self) -> bool {
        self.completely_handled
            && self.concept_values.is_some()
            && self.instantiated_role_values.is_some()
            && self.existential_role_values.is_some()
            && self
                .neighbour_role_combinations
                .iter()
                .all(|combination| combination.role_values.is_some())
            && self.deterministic_same_individuals.is_some()
            && self.nondeterministic_same_individuals.is_some()
            && self.deterministic_different_individuals.is_some()
            && self.nondeterministic_different_individuals.is_some()
            && self.representative_same_individual_id.is_some()
            && self.merge_identity_metadata_complete
            && self.role_metadata_complete
    }
}

/// Per-slot occupancy of the published associations: how much of the recorded
/// model's non-deterministic half `reuse_individual_backend_expansion` has to
/// replay. Test-only read-off over [`NativeAboxRepresentativeCache`].
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct NativeAssociationNondeterminismStats {
    total: usize,
    complete: usize,
    nondeterministic_concepts: usize,
    nondeterministic_neighbour_roles: usize,
    nondeterministic_same_individuals: usize,
    nondeterministic_different_individuals: usize,
    reusable_elements: usize,
}

#[cfg(test)]
fn native_association_nondeterminism_stats(
    cache: &NativeAboxRepresentativeCache,
) -> NativeAssociationNondeterminismStats {
    let mut stats = NativeAssociationNondeterminismStats::default();
    for entry in cache.entries.values() {
        stats.total += 1;
        if entry.complete_for_precomputation() {
            stats.complete += 1;
        }
        if entry
            .concept_values
            .as_ref()
            .is_some_and(|values| values.iter().any(|value| !value.deterministic))
        {
            stats.nondeterministic_concepts += 1;
        }
        if entry.has_nondeterministic_neighbour_roles() {
            stats.nondeterministic_neighbour_roles += 1;
        }
        if entry
            .nondeterministic_same_individuals
            .as_ref()
            .is_some_and(|values| !values.is_empty())
        {
            stats.nondeterministic_same_individuals += 1;
        }
        if entry
            .nondeterministic_different_individuals
            .as_ref()
            .is_some_and(|values| !values.is_empty())
        {
            stats.nondeterministic_different_individuals += 1;
        }
        if entry.has_reusable_elements() {
            stats.reusable_elements += 1;
        }
    }
    stats
}

/// Exact association-status split from
/// `CSaturationNodeBackendAssociationCacheHandler`: handling depends only on
/// indirect insufficiency and the two completed flags. Direct propagation is
/// recorded independently and does not disable backend expansion blocking.
fn native_abox_association_status(direct_flags: Cint64, indirect_flags: Cint64) -> (bool, bool) {
    use super::process::sat_node::IndividualSaturationProcessNodeStatusFlags as F;

    let insufficient = indirect_flags & F::INDSATFLAGINSUFFICIENT != 0
        || indirect_flags & F::INDSATFLAGCOMPLETED == 0
        || direct_flags & F::INDSATFLAGCOMPLETED == 0;
    let completely_propagated = direct_flags & F::INDSATFLAGPROPAGATIONINCOMPLETE == 0;
    (!insufficient, completely_propagated)
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct NativeAboxRepresentativeCache {
    entries: HashMap<Cint64, NativeAboxRepresentativeEntry>,
    /// Konclude aborts the whole association write when any representative
    /// saturation node clashes. Completion remains authoritative in this case.
    association_write_aborted: bool,
    /// Monotone bridge-local equivalent of Konclude's association update id.
    next_association_update_id: u64,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum NativePrecomputationPhase {
    Start,
    IndividualSaturation,
    FullConsistencyCompletion,
    ConsistencyDeclared,
}

fn advance_native_precomputation_phase(
    phase: &mut NativePrecomputationPhase,
    next: NativePrecomputationPhase,
) -> Option<()> {
    let valid = matches!(
        (*phase, next),
        (
            NativePrecomputationPhase::Start,
            NativePrecomputationPhase::IndividualSaturation
        ) | (
            NativePrecomputationPhase::IndividualSaturation,
            NativePrecomputationPhase::FullConsistencyCompletion
        ) | (
            NativePrecomputationPhase::FullConsistencyCompletion,
            NativePrecomputationPhase::ConsistencyDeclared
        )
    );
    if !valid {
        return None;
    }
    *phase = next;
    Some(())
}

/// Tag base for bridged concepts (tag 1 is the ontology TOP sentinel).
const TAG_BASE: Cint64 = 10;

struct Builder<'a> {
    ctx: &'a mut CalculationAlgorithmContextBase,
    next_tag: Cint64,
}

impl<'a> Builder<'a> {
    fn fresh_tag(&mut self) -> Cint64 {
        let t = self.next_tag;
        self.next_tag += 1;
        t
    }
    fn atom(&mut self, tag: Cint64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATOM);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// `CCOR` over `ops` — or the single operand itself (collapsed; the
    /// caller keeps the operand's negation in that case).
    fn or_of(&mut self, ops: &[(ConceptId, bool)]) -> (ConceptId, bool) {
        if ops.len() == 1 {
            return ops[0];
        }
        // `CConcept::addOperandLinker` inserts through `CSortedNegLinker`.
        // Stable tag order is part of Konclude's semantic-branch partition and
        // of its cold branch-priority tie break.
        let mut sorted_ops = ops.to_vec();
        sorted_ops.sort_unstable_by_key(|(concept, negated)| {
            (
                self.ctx
                    .ontology_arenas()
                    .concept(*concept)
                    .get_concept_tag(),
                *negated,
            )
        });
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCOR);
        for (o, n) in sorted_ops {
            c.add_operand_linker(o, n);
        }
        c.set_operand_count(ops.len() as i64);
        (self.ctx.ontology_arenas_mut().alloc_concept(c), false)
    }
    /// Transport one signed concept through an attachment vector whose entries
    /// are positive concept ids. A positive value needs no wrapper. A negative
    /// value uses the exact singleton-OR degeneration: saturation's OR rule
    /// immediately adds its sole signed operand, without introducing a choice.
    fn positive_attachment_concept(&mut self, concept: (ConceptId, bool)) -> ConceptId {
        if !concept.1 {
            return concept.0;
        }
        let tag = self.fresh_tag();
        let mut wrapper = Concept::new();
        wrapper
            .set_concept_tag(tag)
            .set_operator_code(op::CCOR)
            .add_operand_linker(concept.0, true)
            .set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(wrapper)
    }
    fn and_of(&mut self, ops: &[(ConceptId, bool)]) -> (ConceptId, bool) {
        if ops.len() == 1 {
            return ops[0];
        }
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCAND);
        for &(o, n) in ops {
            c.add_operand_linker(o, n);
        }
        c.set_operand_count(ops.len() as i64);
        (self.ctx.ontology_arenas_mut().alloc_concept(c), false)
    }
    fn bottom(&mut self) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCBOTTOM);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    fn some(&mut self, role: RoleId, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCSOME);
        c.set_role(role);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    fn all(&mut self, role: RoleId, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCALL);
        c.set_role(role);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    fn self_restriction(&mut self, role: RoleId) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCSELF);
        c.set_role(role);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Port of `createTriggerConcept(false)` from Konclude's binary absorber.
    fn implication_trigger(&mut self) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCIMPLTRIG);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Port of `createTriggerPropagationConcept`: when the trigger holds on an
    /// R-successor, `CCIMPLALL(R-, dest)` propagates `dest` to its predecessor.
    fn implication_all(&mut self, inverse_role: RoleId, dest: ConceptId) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCIMPLALL);
        c.set_role(inverse_role);
        c.add_operand_linker(dest, false);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Port of `addUnfoldingConceptForConcept`. Absorption may only extend an
    /// atom/subclass or a generated trigger concept, never a restriction.
    fn add_unfolding(&mut self, host: ConceptId, added: ConceptId, negated: bool) -> bool {
        let op_code = self.ctx.ontology_arenas().concept(host).get_operator_code();
        if !matches!(op_code, op::CCATOM | op::CCSUB | op::CCIMPLTRIG) {
            return false;
        }
        let host_concept = self.ctx.ontology_arenas_mut().concept_mut(host);
        host_concept.add_operand_linker(added, negated);
        host_concept.inc_operand_count(1);
        if op_code == op::CCATOM {
            host_concept.set_operator_code(op::CCSUB);
        }
        true
    }
    /// Port of `buildConceptEquivalentClass`: a still-undefined named atom can
    /// carry one complete equivalent definition directly as `CCEQ`. Positive
    /// use expands conjunctively and negative use disjunctively, so no reverse
    /// TOP GCI is required.
    fn add_equivalent_definition(
        &mut self,
        host: ConceptId,
        definition: ConceptId,
        negated: bool,
    ) -> bool {
        if self.ctx.ontology_arenas().concept(host).get_operator_code() != op::CCATOM {
            return false;
        }
        let concept = self.ctx.ontology_arenas_mut().concept_mut(host);
        concept.set_operator_code(op::CCEQ);
        concept.add_operand_linker(definition, negated);
        concept.set_operand_count(1);
        true
    }
    /// Unqualified `≤n R.⊤` — `CCATMOST` with parameter `n` and NO operand
    /// (empty qualifier ⇒ every R-successor counts). `n = 1` is a functional
    /// role; the completion routes it through `apply_atmost_rule` →
    /// `ht_apply_atmost_merge` (merge excess successors, else clash).
    fn atmost(&mut self, role: RoleId, n: Cint64) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role);
        c.set_parameter(n);
        c.set_operand_count(0);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Qualified `≤n R.C` — `CCATMOST` with parameter `n` and qualifier
    /// operand `C` (the at-most merge counts only `C`-successors).
    fn atmost_q(&mut self, role: RoleId, n: Cint64, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role);
        c.set_parameter(n);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Qualified `≥n R.C` — `CCATLEAST` with parameter `n` and qualifier
    /// operand `C` (creates `n` pairwise-distinct `C`-successors).
    fn atleast_q(&mut self, role: RoleId, n: Cint64, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role);
        c.set_parameter(n);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// `CCIMPL[ head, triggers… ]` — fires `head` once every trigger concept
    /// is present with the OPPOSITE polarity of its linker (see
    /// `apply_implication_rule`): a positive body atom becomes a NEGATED
    /// trigger linker.
    fn implication(
        &mut self,
        head: (ConceptId, bool),
        triggers: &[(ConceptId, bool)],
    ) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCIMPL);
        c.add_operand_linker(head.0, head.1);
        for &(t, body_neg) in triggers {
            // body atom `C` (body_neg=false) triggers on POSITIVE presence ⇒
            // linker negated=true (the `¬sub` convention); `¬C` the reverse.
            c.add_operand_linker(t, !body_neg);
        }
        c.set_operand_count(1 + triggers.len() as i64);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
}

#[derive(Clone, Copy, Debug)]
struct AbsorptionTrigger {
    concept: ConceptId,
    complexity: Cint64,
}

#[derive(Default)]
struct TriggerCaches {
    full: HashMap<(ConceptId, bool), Option<AbsorptionTrigger>>,
    partial: HashMap<(ConceptId, bool), Option<AbsorptionTrigger>>,
    pairs: HashMap<(ConceptId, ConceptId), AbsorptionTrigger>,
    role_domains: HashMap<RoleId, AbsorptionTrigger>,
}

/// Port of `getUpdatedTriggerComplexities` plus
/// `getImplicationTriggeredConceptForTriggers`: punish over-used trigger hosts,
/// reuse existing trigger pairs, then build Konclude's left-deep binary chain
/// in decreasing (complexity, concept-address) order.
fn combine_absorption_triggers(
    b: &mut Builder,
    mut triggers: Vec<AbsorptionTrigger>,
    caches: &mut TriggerCaches,
) -> Option<AbsorptionTrigger> {
    // CTriggeredImplicationBinaryAbsorberPreProcess.cpp 3336-3346.
    for trigger in &mut triggers {
        let operand_count = b
            .ctx
            .ontology_arenas()
            .concept(trigger.concept)
            .get_operand_count();
        if operand_count > 20 {
            trigger.complexity -= operand_count / 20;
        }
    }

    triggers.sort_by_key(|trigger| trigger.concept.raw);
    triggers.dedup_by_key(|trigger| trigger.concept);

    // Port `findAndReplaceImplicationFromTriggers`: greedily collapse pairs
    // already present in mConceptImplicationImpliedHash before sorting.
    let mut pending = triggers;
    let mut collapsed = Vec::new();
    while !pending.is_empty() {
        let mut trigger = pending.remove(0);
        let mut check_collapsed = false;
        loop {
            let pending_match = pending.iter().position(|other| {
                let key = if trigger.concept.raw <= other.concept.raw {
                    (trigger.concept, other.concept)
                } else {
                    (other.concept, trigger.concept)
                };
                caches.pairs.contains_key(&key)
            });
            if let Some(index) = pending_match {
                let other = pending.remove(index);
                let key = if trigger.concept.raw <= other.concept.raw {
                    (trigger.concept, other.concept)
                } else {
                    (other.concept, trigger.concept)
                };
                trigger = caches.pairs[&key];
                check_collapsed = true;
                continue;
            }
            if check_collapsed {
                let collapsed_match = collapsed.iter().position(|other: &AbsorptionTrigger| {
                    let key = if trigger.concept.raw <= other.concept.raw {
                        (trigger.concept, other.concept)
                    } else {
                        (other.concept, trigger.concept)
                    };
                    caches.pairs.contains_key(&key)
                });
                if let Some(index) = collapsed_match {
                    let other = collapsed.remove(index);
                    let key = if trigger.concept.raw <= other.concept.raw {
                        (trigger.concept, other.concept)
                    } else {
                        (other.concept, trigger.concept)
                    };
                    trigger = caches.pairs[&key];
                    continue;
                }
            }
            break;
        }
        collapsed.push(trigger);
    }

    // CConceptTriggerLinker::operator<= sorts decreasing complexity, then
    // decreasing pointer. Arena ids are the port's stable pointer surrogate.
    collapsed.sort_by(|left, right| {
        right
            .complexity
            .cmp(&left.complexity)
            .then_with(|| right.concept.raw.cmp(&left.concept.raw))
    });
    let mut trigger_it = collapsed.into_iter();
    let mut left = trigger_it.next()?;
    for right in trigger_it {
        let key = if left.concept.raw <= right.concept.raw {
            (left.concept, right.concept)
        } else {
            (right.concept, left.concept)
        };
        let combined = if let Some(&cached) = caches.pairs.get(&key) {
            cached
        } else {
            let implied = b.implication_trigger();
            let implication = b.implication((implied, false), &[(right.concept, false)]);
            if !b.add_unfolding(left.concept, implication, false) {
                return None;
            }
            let combined = AbsorptionTrigger {
                concept: implied,
                complexity: left.complexity + right.complexity,
            };
            caches.pairs.insert(key, combined);
            combined
        };
        left = combined;
    }
    Some(left)
}

fn role_domain_trigger(
    b: &mut Builder,
    role: RoleId,
    inverse_role: RoleId,
    caches: &mut TriggerCaches,
) -> AbsorptionTrigger {
    if let Some(&trigger) = caches.role_domains.get(&role) {
        return trigger;
    }
    let concept = b.implication_trigger();
    let link = super::model::substrate::NegLink {
        target: concept,
        negated: false,
    };
    b.ctx
        .ontology_arenas_mut()
        .role_mut(role)
        .domain_linker
        .push(link);
    b.ctx
        .ontology_arenas_mut()
        .role_mut(inverse_role)
        .range_linker
        .push(link);
    let trigger = AbsorptionTrigger {
        concept,
        complexity: 1,
    };
    caches.role_domains.insert(role, trigger);
    trigger
}

/// Role-domain marker fragment of Konclude's `CBranchTriggerPreProcess`.
/// For every disjunctive concept, qualified universal/cardinality leaves are
/// indexed by an empty `CCIMPLTRIG` on the restriction role's domain. The
/// completion-side branching metadata is separate; this terminology marker
/// is also required by saturation and common-concept extraction.
fn install_branch_role_domain_triggers(b: &mut Builder, caches: &mut TriggerCaches) -> usize {
    let concept_count = b.ctx.ontology_arenas().concept_count();
    let mut roles = BTreeSet::new();
    for index in 0..concept_count {
        let concept = ConceptId::new(index as Cint64);
        let (op_code, operand_count) = {
            let concept = b.ctx.ontology_arenas().concept(concept);
            (concept.get_operator_code(), concept.get_operand_count())
        };
        if operand_count <= 1 || !matches!(op_code, op::CCAND | op::CCEQ | op::CCOR) {
            continue;
        }
        let mut pending = vec![(concept, op_code != op::CCOR)];
        while let Some((candidate, negated)) = pending.pop() {
            let (candidate_code, candidate_role, candidate_operands) = {
                let candidate = b.ctx.ontology_arenas().concept(candidate);
                (
                    candidate.get_operator_code(),
                    candidate.get_role(),
                    candidate.get_operand_list().to_vec(),
                )
            };
            if (!negated && candidate_code == op::CCOR)
                || (negated && matches!(candidate_code, op::CCAND | op::CCEQ))
            {
                pending.extend(
                    candidate_operands
                        .into_iter()
                        .map(|operand| (operand.target, operand.negated ^ negated)),
                );
                continue;
            }
            let role_trigger = (!negated && matches!(candidate_code, op::CCALL | op::CCATMOST))
                || (negated
                    && matches!(candidate_code, op::CCSOME | op::CCATLEAST)
                    && !candidate_operands.is_empty());
            if role_trigger && candidate_role.is_some() {
                roles.insert(candidate_role.raw);
            }
        }
    }

    let mut installed = 0;
    for role in roles.into_iter().map(RoleId::new) {
        let inverse = b.ctx.ontology_arenas().role(role).get_inverse_role();
        if inverse.is_none() {
            continue;
        }
        let existed = caches.role_domains.contains_key(&role);
        role_domain_trigger(b, role, inverse, caches);
        installed += usize::from(!existed);
    }
    installed
}

/// Faithful fragment of Konclude's `getTriggersForConcept`: atoms are direct
/// triggers, Boolean structure is recursively compiled, and existential
/// structure becomes an inverse-role `CCIMPLALL` trigger-propagation chain.
fn full_absorption_trigger(
    b: &mut Builder,
    literal: (ConceptId, bool),
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
) -> Option<AbsorptionTrigger> {
    if let Some(cached) = caches.full.get(&literal) {
        return *cached;
    }
    let (concept, negated) = literal;
    let (op_code, parameter, role, operands) = {
        let c = b.ctx.ontology_arenas().concept(concept);
        (
            c.get_operator_code(),
            c.get_parameter(),
            c.get_role(),
            c.get_operand_list().to_vec(),
        )
    };
    let result =
        if !negated && matches!(op_code, op::CCATOM | op::CCSUB | op::CCTOP | op::CCIMPLTRIG) {
            Some(AbsorptionTrigger {
                concept,
                complexity: 1,
            })
        } else if !negated && op_code == op::CCNOMINAL {
            // Exact `getTriggersForConcept` CCNOMINAL branch (C++ 3246–3271):
            // a nominal is a usable positive trigger, but the trigger lives on
            // its named individual rather than as an unfolding of the nominal
            // concept. This is what absorbs `{a} -> C` and
            // `({a1} or ... or {an}) -> C` without leaving a critical OR on
            // TOP. The representative-assertion resolver consumes the real
            // individual assertion linker when it builds the saturation seed.
            let individual = b
                .ctx
                .ontology_arenas()
                .concept(concept)
                .get_nominal_individual();
            if individual.is_none() {
                None
            } else {
                let nominal_trigger = b.implication_trigger();
                let assertion = ConceptAssertion {
                    target: nominal_trigger,
                    negated: false,
                };
                let individual = b.ctx.ontology_arenas_mut().individual_mut(individual);
                if !individual
                    .get_assertion_concept_linker()
                    .contains(&assertion)
                {
                    individual.add_assertion_concept_linker(assertion);
                }
                Some(AbsorptionTrigger {
                    concept: nominal_trigger,
                    complexity: 1,
                })
            }
        } else if (!negated && matches!(op_code, op::CCAND | op::CCEQ))
            || (negated && op_code == op::CCOR)
        {
            let mut triggers = Vec::new();
            for operand in operands {
                triggers.push(full_absorption_trigger(
                    b,
                    (operand.target, operand.negated ^ negated),
                    role_inverses,
                    caches,
                )?);
            }
            combine_absorption_triggers(b, triggers, caches)
        } else if (!negated && op_code == op::CCOR)
            || (negated && matches!(op_code, op::CCAND | op::CCEQ))
        {
            let mut alternatives = Vec::new();
            for operand in operands {
                let trigger = full_absorption_trigger(
                    b,
                    (operand.target, operand.negated ^ negated),
                    role_inverses,
                    caches,
                )?;
                alternatives.push(trigger);
            }
            if alternatives.len() <= 1 {
                alternatives.into_iter().next()
            } else {
                let implied = b.implication_trigger();
                let complexity_sum: Cint64 =
                    alternatives.iter().map(|trigger| trigger.complexity).sum();
                let trigger_count = alternatives.len() as Cint64;
                for trigger in alternatives {
                    if !b.add_unfolding(trigger.concept, implied, false) {
                        return None;
                    }
                }
                // Exact C++ `(triggerComplexity + 1) / triggerCount`.
                Some(AbsorptionTrigger {
                    concept: implied,
                    complexity: (complexity_sum + 1) / trigger_count,
                })
            }
        } else if (!negated && op_code == op::CCSOME)
            || (negated && op_code == op::CCALL)
            || (!negated && op_code == op::CCATLEAST && parameter == 1)
            || (negated && op_code == op::CCATMOST && parameter == 0)
        {
            let &inverse = role_inverses.get(&role)?;
            if operands.is_empty() {
                Some(role_domain_trigger(b, role, inverse, caches))
            } else if operands.len() == 1
                && !operands[0].negated
                && b.ctx
                    .ontology_arenas()
                    .concept(operands[0].target)
                    .get_operator_code()
                    == op::CCTOP
                && !negated
            {
                // `∃R.Thing` (and `≥1 R.Thing`) is exactly the existence of an
                // R edge. Konclude uses the role-domain trigger directly; TOP
                // is not an unfolding host for a successor propagation.
                Some(role_domain_trigger(b, role, inverse, caches))
            } else {
                let mut filler_triggers = Vec::new();
                for operand in operands {
                    let operand_negated = if matches!(op_code, op::CCATLEAST | op::CCATMOST) {
                        operand.negated
                    } else {
                        operand.negated ^ negated
                    };
                    filler_triggers.push(full_absorption_trigger(
                        b,
                        (operand.target, operand_negated),
                        role_inverses,
                        caches,
                    )?);
                }
                let filler = combine_absorption_triggers(b, filler_triggers, caches)?;
                let propagated = b.implication_trigger();
                let propagation = b.implication_all(inverse, propagated);
                if !b.add_unfolding(filler.concept, propagation, false) {
                    None
                } else {
                    Some(AbsorptionTrigger {
                        concept: propagated,
                        complexity: filler.complexity + 1,
                    })
                }
            }
        } else {
            None
        };
    caches.full.insert(literal, result);
    result
}

/// Collect the top-level conjunctive triggers for one absorbed GCI literal.
/// Konclude passes all of these to the same final implication and chooses the
/// most complex one as its unfolding host. It does not first collapse them to
/// a generated binary-trigger tree.
fn collect_full_absorption_triggers(
    b: &mut Builder,
    literal: (ConceptId, bool),
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
    triggers: &mut Vec<AbsorptionTrigger>,
) -> bool {
    let (concept, negated) = literal;
    let (op_code, operands) = {
        let concept = b.ctx.ontology_arenas().concept(concept);
        (
            concept.get_operator_code(),
            concept.get_operand_list().to_vec(),
        )
    };
    if (!negated && matches!(op_code, op::CCAND | op::CCEQ)) || (negated && op_code == op::CCOR) {
        return operands.into_iter().all(|operand| {
            collect_full_absorption_triggers(
                b,
                (operand.target, operand.negated ^ negated),
                role_inverses,
                caches,
                triggers,
            )
        });
    }
    if let Some(trigger) = full_absorption_trigger(b, literal, role_inverses, caches) {
        triggers.push(trigger);
        true
    } else {
        false
    }
}

/// Port of the null-`firstImplicationConcept` path used by
/// `createGCIAbsorbedTriggeredImplication`: combine every condition into the
/// reusable binary trigger chain, then unfold the conclusion from its final
/// trigger concept.
fn attach_implied_to_combined_trigger(
    b: &mut Builder,
    implied: (ConceptId, bool),
    triggers: Vec<AbsorptionTrigger>,
    caches: &mut TriggerCaches,
) -> bool {
    let Some(trigger) = combine_absorption_triggers(b, triggers, caches) else {
        return false;
    };
    b.add_unfolding(trigger.concept, implied.0, implied.1)
}

/// Port of `getPartialTriggersForConcept`. The returned trigger is a necessary
/// condition only; callers unfold the original residual GCI from it, exactly as
/// `createGCIPartialAbsorbedTriggeredImplication` does in Konclude.
fn partial_absorption_trigger(
    b: &mut Builder,
    literal: (ConceptId, bool),
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
) -> Option<AbsorptionTrigger> {
    if let Some(trigger) = full_absorption_trigger(b, literal, role_inverses, caches) {
        return Some(trigger);
    }
    if let Some(cached) = caches.partial.get(&literal) {
        return *cached;
    }
    let (concept, negated) = literal;
    let (op_code, role, operands) = {
        let c = b.ctx.ontology_arenas().concept(concept);
        (
            c.get_operator_code(),
            c.get_role(),
            c.get_operand_list().to_vec(),
        )
    };
    let result = if (!negated && op_code == op::CCAND) || (negated && op_code == op::CCOR) {
        let triggers: Vec<_> = operands
            .into_iter()
            .filter_map(|operand| {
                partial_absorption_trigger(
                    b,
                    (operand.target, operand.negated ^ negated),
                    role_inverses,
                    caches,
                )
            })
            .collect();
        combine_absorption_triggers(b, triggers, caches)
    } else if (!negated && op_code == op::CCOR)
        || (negated && matches!(op_code, op::CCAND | op::CCEQ))
    {
        let mut alternatives = Vec::new();
        for operand in operands {
            alternatives.push(partial_absorption_trigger(
                b,
                (operand.target, operand.negated ^ negated),
                role_inverses,
                caches,
            )?);
        }
        if alternatives.len() <= 1 {
            alternatives.into_iter().next()
        } else {
            let implied = b.implication_trigger();
            // Exact partial-trigger code initializes the minimum at zero.
            let complexity = alternatives
                .iter()
                .fold(0, |minimum, trigger| minimum.min(trigger.complexity));
            for trigger in alternatives {
                if !b.add_unfolding(trigger.concept, implied, false) {
                    return None;
                }
            }
            Some(AbsorptionTrigger {
                concept: implied,
                complexity,
            })
        }
    } else if (!negated && matches!(op_code, op::CCSOME | op::CCSELF | op::CCATLEAST))
        || (negated && matches!(op_code, op::CCALL | op::CCATMOST))
    {
        let &inverse = role_inverses.get(&role)?;
        let mut filler_triggers = Vec::new();
        for operand in operands {
            if let Some(trigger) = partial_absorption_trigger(
                b,
                (
                    operand.target,
                    operand.negated ^ (negated && op_code == op::CCALL),
                ),
                role_inverses,
                caches,
            ) {
                filler_triggers.push(trigger);
            }
        }
        if filler_triggers.is_empty() {
            Some(role_domain_trigger(b, role, inverse, caches))
        } else {
            let filler = combine_absorption_triggers(b, filler_triggers, caches)?;
            let propagated = b.implication_trigger();
            let propagation = b.implication_all(inverse, propagated);
            if !b.add_unfolding(filler.concept, propagation, false) {
                None
            } else {
                Some(AbsorptionTrigger {
                    concept: propagated,
                    complexity: filler.complexity + 1,
                })
            }
        }
    } else {
        None
    };
    caches.partial.insert(literal, result);
    result
}

/// Port of the full/partial GCI split in
/// `createGCIAbsorbedTriggeredImplication`. `body` contains conjunctive
/// antecedents; `heads` contains the disjunctive consequent. Fully triggerable
/// head complements move into the antecedent. If full absorption is impossible,
/// a necessary partial trigger unfolds the original GCI instead.
fn absorb_concept_disjunction(
    b: &mut Builder,
    body: &[(ConceptId, bool)],
    heads: &[(ConceptId, bool)],
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
) -> bool {
    let mut full_triggers = Vec::new();
    let mut body_fully_triggerable = true;
    for &literal in body {
        if !collect_full_absorption_triggers(b, literal, role_inverses, caches, &mut full_triggers)
        {
            body_fully_triggerable = false;
        }
    }

    let mut residual_heads = Vec::new();
    for &(concept, negated) in heads {
        if !collect_full_absorption_triggers(
            b,
            (concept, !negated),
            role_inverses,
            caches,
            &mut full_triggers,
        ) {
            residual_heads.push((concept, negated));
        }
    }

    if body_fully_triggerable && !full_triggers.is_empty() {
        let implied = if residual_heads.is_empty() {
            (b.bottom(), false)
        } else {
            b.or_of(&residual_heads)
        };
        return attach_implied_to_combined_trigger(b, implied, full_triggers, caches);
    }

    // Partial absorption is only a gate. Preserve the complete original GCI
    // under that gate, as Konclude does before installing branch metadata.
    let mut partial_triggers = Vec::new();
    for &literal in body {
        if let Some(trigger) = partial_absorption_trigger(b, literal, role_inverses, caches) {
            partial_triggers.push(trigger);
        }
    }
    for &(concept, negated) in heads {
        if let Some(trigger) =
            partial_absorption_trigger(b, (concept, !negated), role_inverses, caches)
        {
            partial_triggers.push(trigger);
        }
    }
    let Some(trigger) = combine_absorption_triggers(b, partial_triggers, caches) else {
        return false;
    };
    let mut original_disjunction: Vec<(ConceptId, bool)> = body
        .iter()
        .map(|&(concept, negated)| (concept, !negated))
        .collect();
    original_disjunction.extend_from_slice(heads);
    let original = if original_disjunction.is_empty() {
        (b.bottom(), false)
    } else {
        b.or_of(&original_disjunction)
    };
    b.add_unfolding(trigger.concept, original.0, original.1)
}

/// Build the normalized frontend concept directly in Konclude's native DAG.
/// This mirrors `CConcreteOntologyUpdateBuilder::buildClassConcept`: structural
/// expressions are shared, named classes retain their fixed terminology atom,
/// and inverse role expressions use the role's wired inverse object.
fn build_source_concept(
    b: &mut Builder,
    source: &SourceConcept,
    concept_index: &HashMap<&str, usize>,
    role_index: &HashMap<&str, usize>,
    named: &[ConceptId],
    roles: &[RoleId],
    inv_roles: &[RoleId],
    nominals: &HashMap<String, ConceptId>,
    cache: &mut HashMap<SourceConcept, (ConceptId, bool)>,
) -> Option<(ConceptId, bool)> {
    if let Some(&built) = cache.get(source) {
        return Some(built);
    }
    let role = |r: &SourceRole| -> Option<RoleId> {
        match r {
            SourceRole::Name(name) => role_index.get(name.as_str()).map(|&i| roles[i]),
            SourceRole::Inverse(name) => role_index.get(name.as_str()).map(|&i| inv_roles[i]),
            SourceRole::Universal => None,
        }
    };
    let built = match source {
        SourceConcept::Name(name) => {
            let i = *concept_index.get(name.as_str())?;
            (named[i], false)
        }
        SourceConcept::Top => (b.ctx.processing_data_box().ontology_top_concept(), false),
        SourceConcept::Bottom => (b.bottom(), false),
        SourceConcept::Nominal(individual) => (*nominals.get(individual)?, false),
        SourceConcept::Not(operand) => {
            let (concept, negated) = build_source_concept(
                b,
                operand,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                nominals,
                cache,
            )?;
            (concept, !negated)
        }
        SourceConcept::And(operands) | SourceConcept::Or(operands) => {
            let built_operands: Option<Vec<_>> = operands
                .iter()
                .map(|operand| {
                    build_source_concept(
                        b,
                        operand,
                        concept_index,
                        role_index,
                        named,
                        roles,
                        inv_roles,
                        nominals,
                        cache,
                    )
                })
                .collect();
            let built_operands = built_operands?;
            if matches!(source, SourceConcept::And(_)) {
                b.and_of(&built_operands)
            } else {
                b.or_of(&built_operands)
            }
        }
        SourceConcept::Exists(r, filler) | SourceConcept::Forall(r, filler) => {
            let filler = build_source_concept(
                b,
                filler,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                nominals,
                cache,
            )?;
            let role = role(r)?;
            if matches!(source, SourceConcept::Exists(..)) {
                (b.some(role, filler), false)
            } else {
                (b.all(role, filler), false)
            }
        }
        SourceConcept::AtLeast(n, r, filler) | SourceConcept::AtMost(n, r, filler) => {
            let filler = build_source_concept(
                b,
                filler,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                nominals,
                cache,
            )?;
            let role = role(r)?;
            if matches!(source, SourceConcept::AtLeast(..)) {
                (b.atleast_q(role, *n, filler), false)
            } else {
                (b.atmost_q(role, *n, filler), false)
            }
        }
        SourceConcept::HasSelf(r) => (b.self_restriction(role(r)?), false),
    };
    cache.insert(source.clone(), built);
    Some(built)
}

fn source_role_id(
    role: &SourceRole,
    role_index: &HashMap<&str, usize>,
    roles: &[RoleId],
    inv_roles: &[RoleId],
) -> Option<RoleId> {
    match role {
        SourceRole::Name(name) => role_index.get(name.as_str()).map(|&i| roles[i]),
        SourceRole::Inverse(name) => role_index.get(name.as_str()).map(|&i| inv_roles[i]),
        SourceRole::Universal => None,
    }
}

#[derive(Clone, Copy)]
enum SourceEncoding {
    Direct,
    RoleLink,
    AbsorbedGci,
    TopGci,
    Unsupported,
}

/// Port of `CConcreteOntologyUpdateBuilder::buildConceptSubClassInclusion`.
/// Atomic left sides become native `CCSUB` unfoldings; only a structural left
/// side reaches the binary GCI absorber. Domain/range-shaped inclusions are
/// stored on the role, matching Konclude's object-property axiom builder.
#[allow(clippy::too_many_arguments)]
fn encode_source_subclass(
    b: &mut Builder,
    left: &SourceConcept,
    right: &SourceConcept,
    concept_index: &HashMap<&str, usize>,
    role_index: &HashMap<&str, usize>,
    named: &[ConceptId],
    roles: &[RoleId],
    inv_roles: &[RoleId],
    nominals: &HashMap<String, ConceptId>,
    role_inverses: &HashMap<RoleId, RoleId>,
    concept_cache: &mut HashMap<SourceConcept, (ConceptId, bool)>,
    trigger_caches: &mut TriggerCaches,
    tbox: &mut Vec<ConceptId>,
    top_gcis: &mut Vec<ConceptId>,
) -> SourceEncoding {
    // The frontend represents complex ObjectPropertyDomain/Range axioms by
    // their DL-equivalent subclass forms. Konclude keeps these as role links.
    if let SourceConcept::Exists(role, filler) = left {
        if matches!(filler.as_ref(), SourceConcept::Top) {
            let Some(role) = source_role_id(role, role_index, roles, inv_roles) else {
                return SourceEncoding::Unsupported;
            };
            let Some((target, negated)) = build_source_concept(
                b,
                right,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                nominals,
                concept_cache,
            ) else {
                return SourceEncoding::Unsupported;
            };
            let link = super::model::substrate::NegLink { target, negated };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .domain_linker
                .push(link);
            if let Some(&inverse) = role_inverses.get(&role) {
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inverse)
                    .range_linker
                    .push(link);
            }
            return SourceEncoding::RoleLink;
        }
    }
    if matches!(left, SourceConcept::Top) {
        if let SourceConcept::Forall(role, filler) = right {
            let Some(role) = source_role_id(role, role_index, roles, inv_roles) else {
                return SourceEncoding::Unsupported;
            };
            let Some((target, negated)) = build_source_concept(
                b,
                filler,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                nominals,
                concept_cache,
            ) else {
                return SourceEncoding::Unsupported;
            };
            let link = super::model::substrate::NegLink { target, negated };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .range_linker
                .push(link);
            if let Some(&inverse) = role_inverses.get(&role) {
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inverse)
                    .domain_linker
                    .push(link);
            }
            return SourceEncoding::RoleLink;
        }
    }

    let Some(left_built) = build_source_concept(
        b,
        left,
        concept_index,
        role_index,
        named,
        roles,
        inv_roles,
        nominals,
        concept_cache,
    ) else {
        return SourceEncoding::Unsupported;
    };
    let Some(right_built) = build_source_concept(
        b,
        right,
        concept_index,
        role_index,
        named,
        roles,
        inv_roles,
        nominals,
        concept_cache,
    ) else {
        return SourceEncoding::Unsupported;
    };

    if matches!(left, SourceConcept::Top) {
        // Exact `CConcreteOntologyUpdateBuilder::buildConceptSubClassInclusion`
        // CCTOP branch: TOP receives the inclusion expression itself via
        // `setConceptOperandsFromClassTerms`. Do not manufacture
        // `not TOP or right`: when `right` is already a disjunction, that
        // creates a nested OR whose outer critical check cannot be discharged
        // by an asserted inner disjunct. The unsigned attachment vectors use a
        // deterministic singleton wrapper only for a negative signed value.
        let inclusion = b.positive_attachment_concept(right_built);
        tbox.push(inclusion);
        top_gcis.push(inclusion);
        return SourceEncoding::TopGci;
    }

    if matches!(left, SourceConcept::Name(_))
        && !left_built.1
        && b.add_unfolding(left_built.0, right_built.0, right_built.1)
    {
        return SourceEncoding::Direct;
    }

    if absorb_concept_disjunction(
        b,
        &[left_built],
        &[right_built],
        role_inverses,
        trigger_caches,
    ) {
        return SourceEncoding::AbsorbedGci;
    }

    // Exact fallback: TOP carries `¬left ∨ right`, so every node checks the
    // original GCI even when no binary trigger can be constructed.
    let disjunction = b.or_of(&[(left_built.0, !left_built.1), right_built]);
    tbox.push(disjunction.0);
    top_gcis.push(disjunction.0);
    SourceEncoding::TopGci
}

fn role_tree_trigger(
    b: &mut Builder,
    node: usize,
    children: &HashMap<usize, Vec<(usize, usize)>>,
    local: &HashMap<usize, Vec<(ConceptId, bool)>>,
    roles: &[RoleId],
    inv_roles: &[RoleId],
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
    visiting: &mut BTreeSet<usize>,
) -> Option<AbsorptionTrigger> {
    if !visiting.insert(node) {
        return None;
    }
    let mut triggers = Vec::new();
    for &literal in local.get(&node).into_iter().flatten() {
        triggers.push(full_absorption_trigger(b, literal, role_inverses, caches)?);
    }
    for &(role_index, child) in children.get(&node).into_iter().flatten() {
        if let Some(child_trigger) = role_tree_trigger(
            b,
            child,
            children,
            local,
            roles,
            inv_roles,
            role_inverses,
            caches,
            visiting,
        ) {
            let propagated = b.implication_trigger();
            let propagation = b.implication_all(inv_roles[role_index], propagated);
            if !b.add_unfolding(child_trigger.concept, propagation, false) {
                return None;
            }
            triggers.push(AbsorptionTrigger {
                concept: propagated,
                complexity: child_trigger.complexity + 1,
            });
        } else if local.get(&child).map_or(true, Vec::is_empty)
            && children.get(&child).map_or(true, Vec::is_empty)
        {
            triggers.push(role_domain_trigger(
                b,
                roles[role_index],
                inv_roles[role_index],
                caches,
            ));
        } else {
            return None;
        }
    }
    visiting.remove(&node);
    combine_absorption_triggers(b, triggers, caches)
}

/// Clause-graph counterpart of Konclude's recursive existential trigger
/// construction. A rooted role tree is compiled into nested inverse-role
/// `CCIMPLALL` propagation, rather than emitted as an unsupported multi-role
/// DL clause.
fn absorb_role_tree_clause(
    b: &mut Builder,
    cl: &HtClause,
    resolved: &[(ConceptId, bool)],
    roles: &[RoleId],
    inv_roles: &[RoleId],
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
) -> bool {
    let mut children: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
    let mut incoming: HashMap<usize, usize> = HashMap::new();
    let mut local: HashMap<usize, Vec<(ConceptId, bool)>> = HashMap::new();
    for atom in &cl.body {
        match atom {
            HAtom::Role { r, s, t } if s != t => {
                if incoming.insert(*t, *s).is_some() {
                    return false;
                }
                children.entry(*s).or_default().push((*r, *t));
            }
            HAtom::Concept { neg, c, t } => {
                local
                    .entry(*t)
                    .or_default()
                    .push((resolved[*c].0, resolved[*c].1 ^ *neg));
            }
            _ => return false,
        }
    }
    if incoming.contains_key(&0) {
        return false;
    }
    let mut all_nodes: BTreeSet<usize> = BTreeSet::from([0]);
    all_nodes.extend(incoming.keys().copied());
    all_nodes.extend(children.keys().copied());
    if all_nodes
        .iter()
        .any(|&node| node != 0 && !incoming.contains_key(&node))
    {
        return false;
    }
    let Some(trigger) = role_tree_trigger(
        b,
        0,
        &children,
        &local,
        roles,
        inv_roles,
        role_inverses,
        caches,
        &mut BTreeSet::new(),
    ) else {
        return false;
    };
    let mut heads = Vec::new();
    for atom in &cl.head {
        match atom {
            HAtom::Concept { neg, c, t } if *t == 0 => {
                heads.push((resolved[*c].0, resolved[*c].1 ^ *neg));
            }
            HAtom::Exist { r, neg, c, t } if *t == 0 => {
                heads.push((
                    b.some(roles[*r], (resolved[*c].0, resolved[*c].1 ^ *neg)),
                    false,
                ));
            }
            _ => return false,
        }
    }
    let implied = if heads.is_empty() {
        (b.bottom(), false)
    } else {
        b.or_of(&heads)
    };
    b.add_unfolding(trigger.concept, implied.0, implied.1)
}

/// Dense equivalent of Konclude's `QSet<TConNegPair>` for one ontology.
/// Concept ids are arena-dense, so generation stamps implement the same
/// signed-concept set without hashing every pointer pair. `entries` keeps the
/// iterable members; root clearing is O(1), and branch rollback clears only
/// entries inserted since its saved mark.
struct DenseSignedConceptSet {
    marks: Vec<u32>,
    generation: u32,
    entries: Vec<(ConceptId, bool)>,
}

impl DenseSignedConceptSet {
    fn new(concept_count: usize) -> Self {
        Self {
            marks: vec![0; concept_count.saturating_mul(2)],
            generation: 1,
            entries: Vec::new(),
        }
    }

    #[inline]
    fn key(entry: (ConceptId, bool)) -> usize {
        entry.0.index() * 2 + usize::from(entry.1)
    }

    #[inline]
    fn insert(&mut self, entry: (ConceptId, bool)) -> bool {
        let key = Self::key(entry);
        if self.marks[key] == self.generation {
            return false;
        }
        self.marks[key] = self.generation;
        self.entries.push(entry);
        true
    }

    #[inline]
    fn contains(&self, entry: (ConceptId, bool)) -> bool {
        self.marks[Self::key(entry)] == self.generation
    }

    fn clear(&mut self) {
        self.entries.clear();
        self.generation = self.generation.wrapping_add(1);
        if self.generation == 0 {
            self.marks.fill(0);
            self.generation = 1;
        }
    }

    fn rollback(&mut self, mark: usize) {
        while self.entries.len() > mark {
            let entry = self.entries.pop().expect("branch mark within set");
            self.marks[Self::key(entry)] = 0;
        }
    }

    fn extend(&mut self, entries: &[(ConceptId, bool)]) {
        for &entry in entries {
            self.insert(entry);
        }
    }

    fn retain_members_of(&mut self, other: &Self) {
        let mut write = 0usize;
        for read in 0..self.entries.len() {
            let entry = self.entries[read];
            if other.contains(entry) {
                self.entries[write] = entry;
                write += 1;
            } else {
                self.marks[Self::key(entry)] = 0;
            }
        }
        self.entries.truncate(write);
    }
}

/// Two branch sets per nested disjunction. Konclude's local QSets reuse their
/// allocations through Qt's containers; this pool gives the Rust port the
/// same lifetime shape without allocating arena-sized marker vectors for each
/// of the 73k disjunction visits in ore_ont_3215.
#[derive(Default)]
struct CommonDisjunctScratch {
    levels: Vec<Option<(DenseSignedConceptSet, DenseSignedConceptSet)>>,
}

impl CommonDisjunctScratch {
    fn take(
        &mut self,
        depth: usize,
        concept_count: usize,
    ) -> (DenseSignedConceptSet, DenseSignedConceptSet) {
        while self.levels.len() <= depth {
            self.levels.push(None);
        }
        self.levels[depth].take().unwrap_or_else(|| {
            (
                DenseSignedConceptSet::new(concept_count),
                DenseSignedConceptSet::new(concept_count),
            )
        })
    }

    fn put(&mut self, depth: usize, sets: (DenseSignedConceptSet, DenseSignedConceptSet)) {
        debug_assert!(self.levels[depth].is_none());
        self.levels[depth] = Some(sets);
    }
}

fn collect_common_disjunct_concepts(
    arenas: &super::model::ontology::OntologyArenas,
    concept: ConceptId,
    negated: bool,
    collect: &mut DenseSignedConceptSet,
    considered: &mut DenseSignedConceptSet,
    cache: &mut HashMap<(ConceptId, bool), Vec<(ConceptId, bool)>>,
    scratch: &mut CommonDisjunctScratch,
    disjunction_depth: usize,
) {
    let entry = (concept, negated);
    if !considered.insert(entry) {
        return;
    }
    collect.insert(entry);
    let (op_code, operand_count) = {
        let c = arenas.concept(concept);
        (c.get_operator_code(), c.get_operand_count() as usize)
    };

    let unfolds = (!negated
        && (matches!(op_code, op::CCSUB | op::CCEQ | op::CCAND)
            || (op_code == op::CCOR && operand_count == 1)))
        || (negated
            && (op_code == op::CCOR
                || (operand_count == 1 && matches!(op_code, op::CCAND | op::CCEQ))));
    if unfolds {
        for operand_index in 0..operand_count {
            // Konclude advances one intrusive operand linker at a time. Copy
            // one small arena link, rather than cloning the whole operand Vec
            // on every recursive visit.
            let operand = arenas.concept(concept).get_operand_list()[operand_index];
            collect_common_disjunct_concepts(
                arenas,
                operand.target,
                operand.negated ^ negated,
                collect,
                considered,
                cache,
                scratch,
                disjunction_depth,
            );
        }
        return;
    }

    let is_disjunction =
        (!negated && op_code == op::CCOR) || (negated && matches!(op_code, op::CCAND | op::CCEQ));
    if !is_disjunction {
        return;
    }

    let key = (concept, negated);
    if let Some(cached) = cache.get(&key) {
        // Konclude stores a pointer to the cached QSet and inserts its members
        // directly into the caller's set (cpp 147-185). Cloning the whole set
        // here retained gigabytes on disjunction-heavy terminologies such as
        // ore_ont_3215 and defeated the cache's purpose.
        collect.extend(cached);
        return;
    }

    let concept_count = arenas.concept_count() as usize;
    let (mut intersection, mut next) = scratch.take(disjunction_depth, concept_count);
    intersection.clear();
    next.clear();
    if operand_count > 0 {
        // QSet copies in Konclude are implicitly shared. Reproduce their
        // branch-local semantics without deep-cloning the complete visited
        // set: record additions, then roll them back after each disjunct.
        let first = arenas.concept(concept).get_operand_list()[0];
        let mark = considered.entries.len();
        collect_common_disjunct_concepts(
            arenas,
            first.target,
            first.negated ^ negated,
            &mut intersection,
            considered,
            cache,
            scratch,
            disjunction_depth + 1,
        );
        considered.rollback(mark);
        for operand_index in 1..operand_count {
            if intersection.entries.is_empty() {
                break;
            }
            next.clear();
            let operand = arenas.concept(concept).get_operand_list()[operand_index];
            let mark = considered.entries.len();
            collect_common_disjunct_concepts(
                arenas,
                operand.target,
                operand.negated ^ negated,
                &mut next,
                considered,
                cache,
                scratch,
                disjunction_depth + 1,
            );
            considered.rollback(mark);
            intersection.retain_members_of(&next);
        }
    }
    collect.extend(&intersection.entries);
    // Konclude owns a separate cached QSet pointer. Cache its iterable
    // members; membership tests stay in the dense scratch sets above.
    cache.insert(key, intersection.entries.clone());
    scratch.put(disjunction_depth, (intersection, next));
}

/// Port of Konclude `CCommonDisjunctConceptExtractionPreProcess` over the
/// completed bridge terminology.  It materialises the producer data consumed
/// by `initializeORProcessing`, rather than recomputing common concepts in the
/// completion hot loop.
fn extract_common_disjunct_replacements(ctx: &mut CalculationAlgorithmContextBase) -> usize {
    let concept_count = ctx.ontology_arenas().concept_count() as usize;
    let mut cache = HashMap::new();
    let mut considered = DenseSignedConceptSet::new(concept_count);
    let mut common = DenseSignedConceptSet::new(concept_count);
    let mut scratch = CommonDisjunctScratch::default();
    let mut extracted = Vec::new();
    for index in 0..concept_count {
        let concept = ConceptId::new(index as Cint64);
        let (op_code, operand_count) = {
            let c = ctx.ontology_arenas().concept(concept);
            (c.get_operator_code(), c.get_operand_count())
        };
        if operand_count < 1 || !matches!(op_code, op::CCAND | op::CCEQ | op::CCOR) {
            continue;
        }
        let negated = matches!(op_code, op::CCAND | op::CCEQ);
        considered.clear();
        common.clear();
        collect_common_disjunct_concepts(
            ctx.ontology_arenas(),
            concept,
            negated,
            &mut common,
            &mut considered,
            &mut cache,
            &mut scratch,
            0,
        );
        if common.entries.len() > 1 {
            let mut common: Vec<_> = common
                .entries
                .iter()
                .copied()
                .filter(|&entry| entry != (concept, negated))
                .collect();
            if common.is_empty() {
                continue;
            }
            common.sort_by_key(|(concept, negated)| {
                (
                    ctx.ontology_arenas().concept(*concept).get_concept_tag(),
                    *negated,
                )
            });
            extracted.push((concept, common));
        }
    }

    for (concept, common) in &extracted {
        let concept_data = ctx.ontology_arenas().concept(*concept).get_concept_data();
        let process_data = if concept_data == INVALID {
            let id = ctx
                .ontology_arenas_mut()
                .alloc_concept_process_data(ConceptProcessData::new());
            ctx.ontology_arenas_mut()
                .concept_mut(*concept)
                .set_concept_data(id.raw);
            id
        } else {
            Id::new(concept_data)
        };
        let previous = ctx
            .ontology_arenas()
            .concept_process_data(process_data)
            .get_replacement_data();
        let replacement = if previous.is_some() {
            previous
        } else {
            let id = ctx
                .ontology_arenas_mut()
                .alloc_replacement_data(ReplacementData::new());
            ctx.ontology_arenas_mut()
                .concept_process_data_mut(process_data)
                .set_replacement_data(id);
            id
        };
        ctx.ontology_arenas_mut()
            .replacement_data_mut(replacement)
            .common_disjunct_concepts = common
            .iter()
            .map(|(concept, negated)| NegLink {
                target: *concept,
                negated: *negated,
            })
            .collect();
    }
    extracted.len()
}

/// Build the bridged terminology for `tin` into `ctx`'s ontology arenas.
///
/// The context must be freshly constructed (the bridge owns tag allocation
/// from [`TAG_BASE`]; the TOP sentinel at tag 1 is seeded by the caller
/// exactly as `classify_test::new_env` does).
pub fn bridge_tinput(ctx: &mut CalculationAlgorithmContextBase, tin: &TInput) -> Bridged {
    bridge_tinput_with_trigger_absorption(ctx, tin, std::env::var_os("KM_TRIGGER_ABSORB").is_some())
}

fn has_any_nominal_input(tin: &TInput) -> bool {
    !tin.nominals.is_empty() || !tin.nominal_abox.is_empty()
}

/// Select Konclude's conditional-full mixed number-restriction+ABox profile.
///
/// `number` is set by `cb_to_ht` only after an equality-head number clause was
/// converted without dropping an atom. It also remains set when
/// `KM_NO_HT_CARD=1` keeps that exact clausal encoding and leaves `card_defs`
/// empty. The typed nominal certificate and the bridge's normal
/// `unsupported == 0` fence independently remain mandatory, so this scheduling
/// choice cannot admit an unsupported ABox or number construct.
///
/// Konclude enables full completion only below its 10,000-individual
/// conditional threshold. Larger ABoxes use the lazy/batched precomputation
/// route and must not enter the retained all-root schedule (or its
/// definition-containment shortcut).
const CONDITIONAL_FULL_INDIVIDUAL_LIMIT: usize = 10_000;

fn native_cardinality_abox_profile(tin: &TInput, native_nominals: bool) -> bool {
    native_nominals
        && tin.number
        && tin.nominal_abox.individuals.len() < CONDITIONAL_FULL_INDIVIDUAL_LIMIT
}

/// Large conditional-nonfull ABoxes that can be consistency-checked by one
/// representative per asserted-type signature and then omitted from taxonomy
/// jobs. With no nominal occurrence, cross-individual edge, inequality, or
/// universal role, the logic is closed under disjoint unions: each independent
/// assertion signature needs one satisfiable root, while individual identity
/// cannot affect a TBox class subsumption.
fn independent_large_abox_profile(tin: &TInput, native_nominals: bool) -> bool {
    fn coupled(concept: &SourceConcept) -> bool {
        match concept {
            SourceConcept::Nominal(_) => true,
            SourceConcept::Not(inner) => coupled(inner),
            SourceConcept::And(operands) | SourceConcept::Or(operands) => {
                operands.iter().any(coupled)
            }
            SourceConcept::Exists(role, filler)
            | SourceConcept::Forall(role, filler)
            | SourceConcept::AtLeast(_, role, filler)
            | SourceConcept::AtMost(_, role, filler) => {
                matches!(role, SourceRole::Universal) || coupled(filler)
            }
            SourceConcept::HasSelf(role) => matches!(role, SourceRole::Universal),
            SourceConcept::Name(_) | SourceConcept::Top | SourceConcept::Bottom => false,
        }
    }

    native_nominals
        && tin.nominal_abox.individuals.len() >= CONDITIONAL_FULL_INDIVIDUAL_LIMIT
        && tin.nominal_abox.role_assertions.is_empty()
        && tin.nominal_abox.negative_role_assertions.is_empty()
        && tin.nominal_abox.different.is_empty()
        && tin.source_axioms.iter().all(|axiom| {
            !coupled(&axiom.left) && !coupled(&axiom.right)
        })
        && tin
            .nominal_abox
            .individuals
            .iter()
            .flat_map(|entry| entry.assertions.iter())
        .all(|assertion| !coupled(assertion))
}

/// Select one stable representative for each logical asserted-type set.
///
/// Frontend assertion order is not semantic, and duplicate assertions do not
/// distinguish two otherwise independent roots. Canonicalising the signature
/// avoids repeating the same completion task for differently ordered input.
fn independent_abox_representative_tags(bridged: &Bridged) -> HashSet<Cint64> {
    let mut signatures = HashSet::new();
    let mut selected_tags = HashSet::new();
    for seed in &bridged.nominal_seeds {
        let signature: BTreeSet<(Cint64, bool)> = seed
            .assertions
            .iter()
            .map(|(concept, negated)| (concept.raw, *negated))
            .collect();
        if signatures.insert(signature) {
            selected_tags.insert(seed.individual_tag);
        }
    }
    selected_tags
}

/// Independent bridge-side validation of the frontend coverage certificate.
/// This deliberately does not relax the legacy fast-tableau nominal fence.
fn native_nominal_metadata_covered(tin: &TInput, source_mode: bool) -> bool {
    let meta = &tin.nominal_abox;
    if !source_mode || !meta.complete || !meta.unsupported.is_empty() || meta.individuals.is_empty()
    {
        return false;
    }
    let concepts: BTreeSet<&str> = tin.concepts.iter().map(String::as_str).collect();
    let mut individuals = BTreeSet::new();
    let mut proxies = BTreeSet::new();
    for entry in &meta.individuals {
        if entry.individual.is_empty()
            || entry.proxies.is_empty()
            || !individuals.insert(entry.individual.as_str())
        {
            return false;
        }
        for proxy in &entry.proxies {
            if !concepts.contains(proxy.as_str()) || !proxies.insert(proxy.as_str()) {
                return false;
            }
        }
    }
    if meta.different.iter().any(|(left, right)| {
        !individuals.contains(left.as_str()) || !individuals.contains(right.as_str())
    }) {
        return false;
    }
    let roles: BTreeSet<&str> = tin.roles.iter().map(String::as_str).collect();
    if roles.len() != tin.roles.len() {
        return false;
    }
    if meta
        .role_assertions
        .iter()
        .chain(meta.negative_role_assertions.iter())
        .any(|assertion| {
            assertion.role.is_empty()
                || assertion.source.is_empty()
                || assertion.target.is_empty()
                || is_builtin_top_role_name(&assertion.role)
                || is_builtin_bottom_role_name(&assertion.role)
                || !roles.contains(assertion.role.as_str())
                || !individuals.contains(assertion.source.as_str())
                || !individuals.contains(assertion.target.as_str())
        })
    {
        return false;
    }
    // An inverse-free conversion retains the historical `nominals` ids; every
    // one must be accounted for by the typed proxy mapping. In the SHOI case
    // cb_to_ht clears that vector after recording its legacy fence, so the
    // source certificate remains the authoritative mapping.
    tin.nominals.iter().all(|&id| {
        tin.concepts
            .get(id)
            .is_some_and(|name| proxies.contains(name.as_str()))
    })
}

/// Environment-independent terminology builder used by focused absorber
/// tests. Production continues to select the same option in [`bridge_tinput`].
fn bridge_tinput_with_trigger_absorption(
    ctx: &mut CalculationAlgorithmContextBase,
    tin: &TInput,
    trigger_absorb: bool,
) -> Bridged {
    let source_mode = trigger_absorb
        && !tin.source_axioms.is_empty()
        && std::env::var_os("KM_NO_SOURCE_TBOX").is_none();
    // Konclude distinguishes every concept in the terminology vector from
    // the active OWL classes it classifies. Frontend Q_/definer concepts are
    // anonymous structural concepts in Konclude; assigning class-name linkers
    // to all TInput atoms made both saturation and KPSet treat 113,187 such
    // markers as classes on ore_ont_3215. `queries` is the frontend's active
    // named-class set; an empty list retains the legacy all-active test input.
    let mut active_class = vec![tin.queries.is_empty(); tin.concepts.len()];
    for &query in &tin.queries {
        if let Some(active) = active_class.get_mut(query) {
            *active = true;
        }
    }
    let bridge_phase_trace = std::env::var_os("KM_BRIDGE_PHASES").is_some();
    let bridge_started = std::time::Instant::now();
    let mut bridge_phase_started = bridge_started;
    macro_rules! bridge_phase {
        ($name:expr) => {
            if bridge_phase_trace {
                let now = std::time::Instant::now();
                eprintln!(
                    "BRIDGE-PHASE {} delta={:.3}s total={:.3}s",
                    $name,
                    now.duration_since(bridge_phase_started).as_secs_f64(),
                    now.duration_since(bridge_started).as_secs_f64(),
                );
                bridge_phase_started = now;
            }
        };
    }
    let mut b = Builder {
        ctx,
        next_tag: TAG_BASE + tin.concepts.len() as Cint64,
    };
    let named: Vec<ConceptId> = (0..tin.concepts.len())
        .map(|i| {
            let tag = TAG_BASE + i as Cint64;
            let concept = b.atom(tag);
            if active_class[i] {
                b.ctx
                    .ontology_arenas_mut()
                    .concept_mut(concept)
                    .add_class_name_linker(NameId::new(tag));
            }
            concept
        })
        .collect();
    bridge_phase!("named-and-roles");
    let roles: Vec<RoleId> = (0..tin.roles.len())
        .map(|i| {
            // distinct role tags (tag 1 is the TOP-role sentinel; see the
            // preprocess/automata port notes), offset clear of it.
            let mut r = Role::new();
            r.set_role_tag(100 + i as Cint64);
            b.ctx.ontology_arenas_mut().alloc_role(r)
        })
        .collect();
    if std::env::var_os("KM_SAT_ABSORB_DEBUG").is_some() {
        for (index, name) in tin.roles.iter().enumerate() {
            eprintln!("BRIDGE-ROLE tag={} name={name}", 100 + index as Cint64);
        }
        if let Ok(tags) = std::env::var("KM_BRIDGE_NAME_TAGS") {
            let tags: BTreeSet<Cint64> = tags
                .split(',')
                .filter_map(|tag| tag.parse::<Cint64>().ok())
                .collect();
            for (index, name) in tin.concepts.iter().enumerate() {
                let tag = TAG_BASE + index as Cint64;
                if tags.contains(&tag) {
                    eprintln!("BRIDGE-CONCEPT tag={tag} name={name}");
                }
            }
        }
    }
    // Every bridged role gets a wired inverse (both directions, the
    // `inverse_role_propagation` selftest pattern). Needed by the
    // absorption-shape rewrite below: a y-triggered guarded clause
    // `D(y) ∧ R(x,y) → E(x)` encodes as `D ⊑ ∀R⁻.E`.
    let inv_roles: Vec<RoleId> = (0..tin.roles.len())
        .map(|i| {
            let mut r = Role::new();
            r.set_role_tag(100 + (tin.roles.len() + i) as Cint64);
            r.set_inverse_role(roles[i]);
            let id = b.ctx.ontology_arenas_mut().alloc_role(r);
            b.ctx
                .ontology_arenas_mut()
                .role_mut(roles[i])
                .set_inverse_role(id);
            // CSubroleTransformationPreProcess represents inverse equivalence
            // as signed super-role links in both directions. Saturation uses
            // the negative entry to install the successor-to-predecessor
            // propagation link consumed by ALL/AQALL automata.
            b.ctx
                .ontology_arenas_mut()
                .role_mut(roles[i])
                .add_super_role_linker(super::model::substrate::NegLink {
                    target: id,
                    negated: true,
                })
                .add_equivalent_role_linker(super::model::substrate::NegLink {
                    target: id,
                    negated: true,
                });
            b.ctx
                .ontology_arenas_mut()
                .role_mut(id)
                .add_super_role_linker(super::model::substrate::NegLink {
                    target: roles[i],
                    negated: true,
                })
                .add_equivalent_role_linker(super::model::substrate::NegLink {
                    target: roles[i],
                    negated: true,
                });
            id
        })
        .collect();
    let role_inverses: HashMap<RoleId, RoleId> = roles
        .iter()
        .copied()
        .zip(inv_roles.iter().copied())
        .chain(inv_roles.iter().copied().zip(roles.iter().copied()))
        .collect();
    bridge_phase!("inverse-roles");

    // Native nominal construction is admitted only through the complete typed
    // source channel. The old `tin.nominals` spelling/fence remains untouched
    // for every other consumer.
    let native_nominal_covered = native_nominal_metadata_covered(tin, source_mode);
    // `TInput::number` is the semantic feature bit: it remains set when the
    // frontend keeps the clausal cardinality encoding and therefore emits no
    // `card_defs` (the production 9540 route uses `KM_NO_HT_CARD=1`).  The
    // side-channel's presence is an encoding choice, not a fragment test.
    let direct_native_role_assertions =
        native_cardinality_abox_profile(tin, native_nominal_covered);
    let nominal_concept_index: HashMap<&str, usize> = tin
        .concepts
        .iter()
        .enumerate()
        .map(|(index, name)| (name.as_str(), index))
        .collect();
    let mut nominal_by_name: HashMap<String, ConceptId> = HashMap::new();
    let mut nominal_tag_by_name: HashMap<String, Cint64> = HashMap::new();
    let mut nominal_seed_index_by_name: HashMap<String, usize> = HashMap::new();
    let mut nominal_seeds = Vec::new();
    let mut nominal_different = Vec::new();
    if native_nominal_covered {
        for entry in &tin.nominal_abox.individuals {
            let proxy_concepts: Vec<ConceptId> = entry
                .proxies
                .iter()
                .filter_map(|proxy| nominal_concept_index.get(proxy.as_str()).map(|&i| named[i]))
                .collect();
            // `native_nominal_metadata_covered` already checked nonempty and
            // exact lookup; keep this defensive guard for hand-authored JSON.
            let Some(&nominal_concept) = proxy_concepts.first() else {
                continue;
            };
            let individual_tag = b.ctx.ontology_arenas().individual_count();
            let mut individual = Individual::new(individual_tag);
            // Source ABox entries are named OWL individuals. Konclude's
            // saturation initializer selects its assertion-resolved-node path
            // through `CIndividual::hasIndividualName`; preserve that metadata
            // instead of leaving every bridged individual anonymous.
            individual
                .add_individual_name_linker(NameId::new(individual_tag))
                .set_individual_nominal_concept(nominal_concept);
            let individual = b.ctx.ontology_arenas_mut().alloc_individual(individual);
            b.ctx
                .ontology_arenas_mut()
                .insert_active_individual(individual);
            for concept in proxy_concepts {
                b.ctx
                    .ontology_arenas_mut()
                    .concept_mut(concept)
                    .set_operator_code(op::CCNOMINAL)
                    .set_nominal_individual(individual);
            }
            nominal_by_name.insert(entry.individual.clone(), nominal_concept);
            nominal_tag_by_name.insert(entry.individual.clone(), individual_tag);
            nominal_seed_index_by_name.insert(entry.individual.clone(), nominal_seeds.len());
            nominal_seeds.push(NominalSeed {
                individual,
                individual_tag,
                nominal_concept,
                assertions: Vec::new(),
                role_assertions: Vec::new(),
            });
        }
        for (left, right) in &tin.nominal_abox.different {
            if let (
                Some(&left_tag),
                Some(&right_tag),
                Some(&left_index),
                Some(&right_index),
                Some(&left_nominal),
                Some(&right_nominal),
            ) = (
                nominal_tag_by_name.get(left),
                nominal_tag_by_name.get(right),
                nominal_seed_index_by_name.get(left),
                nominal_seed_index_by_name.get(right),
                nominal_by_name.get(left),
                nominal_by_name.get(right),
            ) {
                nominal_different.push((left_tag, right_tag));
                // Konclude translates DifferentIndividuals(a,b) into the two
                // ordinary negative nominal assertions a:¬{b}, b:¬{a}.
                // Keeping them in the labels preserves component locality:
                // unrelated named nodes need not be materialised merely to
                // install a global pairwise edge.
                for (seed_index, distinct_nominal) in
                    [(left_index, right_nominal), (right_index, left_nominal)]
                {
                    let seed = &mut nominal_seeds[seed_index];
                    if !seed.assertions.contains(&(distinct_nominal, true)) {
                        seed.assertions.push((distinct_nominal, true));
                    }
                    let assertion = ConceptAssertion {
                        target: distinct_nominal,
                        negated: true,
                    };
                    let individual = b.ctx.ontology_arenas_mut().individual_mut(seed.individual);
                    if !individual
                        .get_assertion_concept_linker()
                        .contains(&assertion)
                    {
                        individual.add_assertion_concept_linker(assertion);
                    }
                }
            }
        }
    }
    bridge_phase!("native-nominals");
    // In source-TBox mode Konclude builds the terminology from the normalized
    // class expressions before clausification. The frontend `definers` are a
    // second, clausifier-generated representation of those same expressions;
    // materializing both duplicates the concept DAG and makes every downstream
    // preprocessor visit the duplicate. Keep them only for the legacy clause
    // bridge, where they are the sole structural representation.
    // Resolve internal frontend markers to native signed concepts before
    // building implications. Query concepts remain the atomic `named` vector;
    // only clause literals use `resolved`. Provenance is emitted in dependency
    // order (operand definers before their parent), so one forward pass is
    // sufficient.
    let mut resolved: Vec<(ConceptId, bool)> = named.iter().copied().map(|c| (c, false)).collect();
    if trigger_absorb && !source_mode {
        let concept_index: HashMap<&str, usize> = tin
            .concepts
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let role_index: HashMap<&str, usize> = tin
            .roles
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let card_markers: BTreeSet<usize> = tin.card_defs.iter().map(|d| d.marker).collect();
        for d in &tin.definers {
            let Some(&marker) = concept_index.get(d.marker.as_str()) else {
                continue;
            };
            if card_markers.contains(&marker) {
                continue;
            }
            let operands: Option<Vec<(ConceptId, bool)>> = d
                .operands
                .iter()
                .map(|n| concept_index.get(n.as_str()).map(|&i| resolved[i]))
                .collect();
            let Some(operands) = operands else {
                continue;
            };
            let role = d
                .role
                .as_deref()
                .and_then(|r| role_index.get(r).copied())
                .map(|r| roles[r]);
            let value = match d.kind {
                DefinerKind::Top => {
                    let top = b.ctx.processing_data_box().ontology_top_concept();
                    top.is_some().then_some((top, false))
                }
                DefinerKind::Bottom => Some((b.bottom(), false)),
                DefinerKind::Not if operands.len() == 1 => Some((operands[0].0, !operands[0].1)),
                DefinerKind::And if !operands.is_empty() => Some(b.and_of(&operands)),
                DefinerKind::Or if !operands.is_empty() => Some(b.or_of(&operands)),
                DefinerKind::Exists if operands.len() == 1 && role.is_some() => {
                    Some((b.some(role.unwrap(), operands[0]), false))
                }
                DefinerKind::Forall if operands.len() == 1 && role.is_some() => {
                    Some((b.all(role.unwrap(), operands[0]), false))
                }
                DefinerKind::SelfRestriction if role.is_some() => {
                    Some((b.self_restriction(role.unwrap()), false))
                }
                DefinerKind::NotSelf if role.is_some() => {
                    Some((b.self_restriction(role.unwrap()), true))
                }
                DefinerKind::AtLeast if operands.len() == 1 && role.is_some() => Some((
                    b.atleast_q(role.unwrap(), d.n.unwrap_or(0), operands[0]),
                    false,
                )),
                DefinerKind::AtMost if operands.len() == 1 && role.is_some() => Some((
                    b.atmost_q(role.unwrap(), d.n.unwrap_or(0), operands[0]),
                    false,
                )),
                DefinerKind::Not
                | DefinerKind::And
                | DefinerKind::Or
                | DefinerKind::Exists
                | DefinerKind::Forall
                | DefinerKind::SelfRestriction
                | DefinerKind::NotSelf
                | DefinerKind::AtLeast
                | DefinerKind::AtMost => None,
            };
            if let Some(value) = value {
                resolved[marker] = value;
            }
        }
    }
    bridge_phase!("definers");

    let mut tbox: Vec<ConceptId> = Vec::new();
    // Absorption bookkeeping (attached after the encode loop): an implication
    // with a positive concept trigger hangs off that trigger's concept; the
    // rest go to TOP.
    let mut absorbed_pairs: Vec<(ConceptId, ConceptId)> = Vec::new();
    let mut top_gcis: Vec<ConceptId> = Vec::new();
    let mut trigger_caches = TriggerCaches::default();
    let mut singleton_concepts: Vec<ConceptId> = Vec::new();
    let mut unsupported = 0usize;
    // Diagnostic (KM_BRIDGE_DUMP_UNSUP=N): record the shape of the first N
    // unsupported clauses so the next coverage wave can be scoped.
    let dump_unsup: usize = std::env::var("KM_BRIDGE_DUMP_UNSUP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut dumped = 0usize;
    let mut dump = |cl: &HtClause, why: &str| {
        if dumped < dump_unsup {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                }
            };
            let b: Vec<String> = cl.body.iter().map(show).collect();
            let h: Vec<String> = cl.head.iter().map(show).collect();
            eprintln!("UNSUP[{why}]: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            dumped += 1;
        }
    };
    // Diagnostic (KM_BRIDGE_DUMP_TOPGCI=N): record the shape of the first N
    // clauses that become TOP-attached GCIs (no positive absorption guard) —
    // these branch on EVERY node and are the disjunction-search cost centre.
    let dump_topgci: usize = std::env::var("KM_BRIDGE_DUMP_TOPGCI")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut dumped_top = 0usize;
    let topgci_names = &tin.concepts;
    let mut dump_top = |cl: &HtClause, why: &str| {
        if dumped_top < dump_topgci {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!(
                            "{}C{c}:{}({t})",
                            if *neg { "¬" } else { "" },
                            topgci_names.get(*c).map(String::as_str).unwrap_or("?")
                        )
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!(
                            "∃R{r}.{}C{c}:{}({t})",
                            if *neg { "¬" } else { "" },
                            topgci_names.get(*c).map(String::as_str).unwrap_or("?")
                        )
                    }
                }
            };
            let b: Vec<String> = cl.body.iter().map(show).collect();
            let h: Vec<String> = cl.head.iter().map(show).collect();
            eprintln!("TOPGCI[{why}]: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            dumped_top += 1;
        }
    };
    // Structures outside the v1 clause encoder count as unsupported input
    // (card_defs are ENCODED below — first-class ≥n/≤n via the ported
    // CCATLEAST/CCATMOST rules — so they are no longer counted here).
    if has_any_nominal_input(tin) && !native_nominal_covered {
        // One coverage failure is sufficient to force complete-or-DEFER. Keep
        // the historical id count in diagnostics without double-counting a
        // valid typed representation of those same singleton concepts.
        unsupported += tin.nominals.len().max(1);
    }

    // Konclude keeps source ObjectPropertyDomain/ObjectPropertyRange axioms
    // directly on CRole. In source-TBox mode use the converter's explicit
    // RBox provenance: a guarded clause shape is not sufficient, because the
    // clausifier emits the same shape for ordinary class-expression rules.
    // (ORE 9724 has no source domains/ranges but thousands of such rules.)
    if source_mode {
        for &(role, concept) in &tin.role_domains {
            let (Some(&role), Some(&concept)) = (roles.get(role), named.get(concept)) else {
                unsupported += 1;
                continue;
            };
            let inverse = role_inverses[&role];
            let link = super::model::substrate::NegLink {
                target: concept,
                negated: false,
            };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .domain_linker
                .push(link);
            b.ctx
                .ontology_arenas_mut()
                .role_mut(inverse)
                .range_linker
                .push(link);
        }
        for &(role, concept) in &tin.role_ranges {
            let (Some(&role), Some(&concept)) = (roles.get(role), named.get(concept)) else {
                unsupported += 1;
                continue;
            };
            let inverse = role_inverses[&role];
            let link = super::model::substrate::NegLink {
                target: concept,
                negated: false,
            };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .range_linker
                .push(link);
            b.ctx
                .ontology_arenas_mut()
                .role_mut(inverse)
                .domain_linker
                .push(link);
        }
    }

    // ---- pass 1: role hierarchy `R(x,y) → S(x,y)` --------------------------
    // Collected first and installed as direct and (transitively closed)
    // indirect-super-role linkers on the sub-role — the exact structures the
    // automata preprocessor, ∀/edge rules, and u08 hierarchy-resolved edge
    // reapply consume (see CSubroleTransformationPreProcess). Konclude seeds
    // every indirect list with the role itself before adding strict supers;
    // collectSubRoleChains relies on that reflexive entry to index a chain
    // under its own super role.
    // The closure runs over BOTH polarities (vertex = 2·role + inverted): a
    // plain `R ⊑ S` also yields `R⁻ ⊑ S⁻` (needed by the mirror inverse-edge
    // installs), and an inverse-hierarchy clause `R(x,y) → S(y,x)` (`R ⊑ S⁻`,
    // the clausal InverseObjectProperties half) crosses polarity. All entries
    // are installed with negated=false against the CONCRETE role object
    // (`roles[·]` / `inv_roles[·]`) — `has_indirect_super_role` (the u08
    // ∀-matcher) ignores the negated flag, so polarity must be resolved to
    // distinct role objects, never encoded in the flag.
    let n_r = tin.roles.len();
    let mut sub_super: Vec<Vec<usize>> = vec![Vec::new(); 2 * n_r];
    let is_hierarchy = |cl: &HtClause| -> Option<(usize, usize)> {
        if cl.body.len() != 1 || cl.head.len() != 1 {
            return None;
        }
        if let (
            HAtom::Role {
                r: sr,
                s: ss,
                t: st,
            },
            HAtom::Role {
                r: hr,
                s: hs,
                t: ht,
            },
        ) = (&cl.body[0], &cl.head[0])
        {
            if ss == hs && st == ht && ss != st && sr != hr {
                return Some((*sr, *hr));
            }
        }
        None
    };
    // `R(x,y) → S(y,x)` — `R ⊑ S⁻`; `sr == hr` allowed (a symmetric role).
    let is_inv_hierarchy = |cl: &HtClause| -> Option<(usize, usize)> {
        if cl.body.len() != 1 || cl.head.len() != 1 {
            return None;
        }
        if let (
            HAtom::Role {
                r: sr,
                s: ss,
                t: st,
            },
            HAtom::Role {
                r: hr,
                s: hs,
                t: ht,
            },
        ) = (&cl.body[0], &cl.head[0])
        {
            if ss == ht && st == hs && ss != st {
                return Some((*sr, *hr));
            }
        }
        None
    };
    for cl in &tin.clauses {
        if let Some((sub, sup)) = is_hierarchy(cl) {
            sub_super[2 * sub].push(2 * sup);
            sub_super[2 * sub + 1].push(2 * sup + 1);
        } else if let Some((sub, sup)) = is_inv_hierarchy(cl) {
            sub_super[2 * sub].push(2 * sup + 1);
            sub_super[2 * sub + 1].push(2 * sup);
        }
    }
    // Direct hierarchy plus reflexive-transitive closure per (role, polarity)
    // vertex (small role counts; DFS).
    for sub in 0..sub_super.len() {
        let sub_obj = if sub % 2 == 0 {
            roles[sub / 2]
        } else {
            inv_roles[sub / 2]
        };
        for &direct in &sub_super[sub] {
            let direct_obj = if direct % 2 == 0 {
                roles[direct / 2]
            } else {
                inv_roles[direct / 2]
            };
            let inverse_direct_obj = if direct % 2 == 0 {
                inv_roles[direct / 2]
            } else {
                roles[direct / 2]
            };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(sub_obj)
                .add_super_role_linker(super::model::substrate::NegLink {
                    target: direct_obj,
                    negated: false,
                })
                .add_super_role_linker(super::model::substrate::NegLink {
                    target: inverse_direct_obj,
                    negated: true,
                });
        }
        b.ctx
            .ontology_arenas_mut()
            .role_mut(sub_obj)
            .add_indirect_super_role_linker(super::model::substrate::NegLink {
                target: sub_obj,
                negated: false,
            })
            .add_indirect_super_role_linker(super::model::substrate::NegLink {
                target: if sub % 2 == 0 {
                    inv_roles[sub / 2]
                } else {
                    roles[sub / 2]
                },
                negated: true,
            });
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<usize> = sub_super[sub].clone();
        while let Some(s) = stack.pop() {
            if s != sub && seen.insert(s) {
                stack.extend(sub_super[s].iter().copied());
            }
        }
        for s in seen {
            let sup_obj = if s % 2 == 0 {
                roles[s / 2]
            } else {
                inv_roles[s / 2]
            };
            let inverse_sup_obj = if s % 2 == 0 {
                inv_roles[s / 2]
            } else {
                roles[s / 2]
            };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(sub_obj)
                .add_indirect_super_role_linker(super::model::substrate::NegLink {
                    target: sup_obj,
                    negated: false,
                })
                .add_indirect_super_role_linker(super::model::substrate::NegLink {
                    target: inverse_sup_obj,
                    negated: true,
                });
        }
    }
    bridge_phase!("role-hierarchy");

    // Production RBox: materialize every retained R1 o R2 <= R axiom as the
    // CRoleChain / super-sharing structure consumed by Konclude's role-
    // automata preprocessor. Transitivity is the special chain R o R <= R.
    let mut role_chains: Vec<(usize, usize, usize)> = tin.chains.clone();
    for &role in &tin.transitive {
        role_chains.push((role, role, role));
    }
    role_chains.sort_unstable();
    role_chains.dedup();
    let mut object_chains: Vec<(RoleId, RoleId, RoleId)> = Vec::new();
    for (left, right, super_role) in role_chains {
        if left >= roles.len() || right >= roles.len() || super_role >= roles.len() {
            unsupported += 1;
            continue;
        }
        object_chains.push((roles[left], roles[right], roles[super_role]));
        // The bridge uses concrete inverse role objects. Materialize the
        // reversed chain as well as the signed inverse view so saturation's
        // successor-extension construction has an explicit creation-role
        // path in both directions.
        object_chains.push((inv_roles[right], inv_roles[left], inv_roles[super_role]));
    }
    object_chains.sort_by_key(|(left, right, sup)| (left.raw, right.raw, sup.raw));
    object_chains.dedup();
    for (left, right, super_role) in object_chains {
        let mut chain = RoleChain::new();
        chain
            .append_role_chain_linker(left)
            .append_role_chain_linker(right);
        let chain_id = b.ctx.ontology_arenas_mut().alloc_role_chain(chain);
        b.ctx
            .ontology_arenas_mut()
            .role_chain_mut(chain_id)
            .set_role_chain_tag(chain_id.index() as Cint64);
        b.ctx
            .ontology_arenas_mut()
            .role_mut(super_role)
            .add_role_chain_super_sharing_linker(chain_id);
        let complex_roles: Vec<RoleId> = std::iter::once(super_role)
            .chain(
                b.ctx
                    .ontology_arenas()
                    .role(super_role)
                    .get_indirect_super_role_list()
                    .iter()
                    .map(|link| link.target),
            )
            .collect();
        for role in complex_roles {
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .set_role_complexity(true);
        }
    }
    bridge_phase!("role-chains");

    // ---- pass 2: functional roles `R(0,1) ∧ R(0,2) → eq(1,2)` --------------
    // The clausal form of `⊤ ⊑ ≤1 R.⊤` (a functional property / global at-most
    // 1). Detected here and later encoded as a `CCATMOST(R, 1)` on TOP so
    // every node enforces ≤1 R-successor through the ported merge rule
    // (`ht_apply_atmost_merge`). The clause itself is then consumed (not
    // unsupported).
    let is_functional = |cl: &HtClause| -> Option<usize> {
        if cl.body.len() != 2 || cl.head.len() != 1 {
            return None;
        }
        let (b0, b1) = (&cl.body[0], &cl.body[1]);
        if let (
            HAtom::Role {
                r: r0,
                s: s0,
                t: t0,
            },
            HAtom::Role {
                r: r1,
                s: s1,
                t: t1,
            },
            HAtom::Eq { s: es, t: et },
        ) = (b0, b1, &cl.head[0])
        {
            // same role, shared source 0, distinct targets, head equates them.
            if r0 == r1 && s0 == s1 && t0 != t1 {
                let (a, b) = (*t0.min(t1), *t0.max(t1));
                let (ea, eb) = (*es.min(et), *es.max(et));
                if (a, b) == (ea, eb) && *s0 != a && *s0 != b {
                    return Some(*r0);
                }
            }
        }
        None
    };
    let mut functional_roles: BTreeSet<usize> = BTreeSet::new();
    for cl in &tin.clauses {
        if let Some(r) = is_functional(cl) {
            functional_roles.insert(r);
        }
    }
    for &role in &functional_roles {
        b.ctx
            .ontology_arenas_mut()
            .role_mut(roles[role])
            .set_functional(true);
    }
    bridge_phase!("functional-scan");

    let mut certified_unsatisfiable = Vec::new();

    // Konclude builds the terminology before clausification: named-left
    // inclusions become CCSUB operands and only residual structural-left GCIs
    // reach CTriggeredImplicationBinaryAbsorberPreProcess. Use the normalized
    // source side channel when present, then ignore the frontend's derived
    // concept clauses below (role hierarchy/functionality clauses remain the
    // authoritative RBox representation).
    if source_mode {
        let concept_index: HashMap<&str, usize> = tin
            .concepts
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();
        let role_index: HashMap<&str, usize> = tin
            .roles
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();
        let mut concept_cache = HashMap::new();
        let mut direct = 0usize;
        let mut role_links = 0usize;
        let mut absorbed = 0usize;
        let mut residual = 0usize;
        let mut source_unsupported = 0usize;
        let mut equivalent_definitions = 0usize;
        let mut equivalent_definition_names = Vec::new();
        let mut absorbed_equivalent_definitions = 0usize;
        let mut seen_inclusions = std::collections::HashSet::new();
        let mut forced_subclass_names = std::collections::HashSet::new();
        let mut equivalence_name_counts: HashMap<&str, usize> = HashMap::new();
        for axiom in &tin.source_axioms {
            match axiom.kind {
                crate::json_io::SourceAxiomKind::SubClass => {
                    if let SourceConcept::Name(name) = &axiom.left {
                        forced_subclass_names.insert(name.as_str());
                    }
                }
                crate::json_io::SourceAxiomKind::Disjoint => {
                    for side in [&axiom.left, &axiom.right] {
                        if let SourceConcept::Name(name) = side {
                            forced_subclass_names.insert(name.as_str());
                        }
                    }
                }
                crate::json_io::SourceAxiomKind::Equivalent => {
                    for side in [&axiom.left, &axiom.right] {
                        if let SourceConcept::Name(name) = side {
                            *equivalence_name_counts.entry(name.as_str()).or_default() += 1;
                        }
                    }
                }
            }
        }
        bridge_phase!("source-prescan");
        macro_rules! encode {
            ($left:expr, $right:expr $(,)?) => {{
                let left = $left;
                let right = $right;
                if seen_inclusions.insert((left.clone(), right.clone())) {
                    let encoding = encode_source_subclass(
                        &mut b,
                        left,
                        right,
                        &concept_index,
                        &role_index,
                        &named,
                        &roles,
                        &inv_roles,
                        &nominal_by_name,
                        &role_inverses,
                        &mut concept_cache,
                        &mut trigger_caches,
                        &mut tbox,
                        &mut top_gcis,
                    );
                    match encoding {
                        SourceEncoding::Direct => direct += 1,
                        SourceEncoding::RoleLink => role_links += 1,
                        SourceEncoding::AbsorbedGci => absorbed += 1,
                        SourceEncoding::TopGci => residual += 1,
                        SourceEncoding::Unsupported => source_unsupported += 1,
                    }
                }
            }};
        }
        for (axiom_index, axiom) in tin.source_axioms.iter().enumerate() {
            match axiom.kind {
                crate::json_io::SourceAxiomKind::SubClass => {
                    encode!(&axiom.left, &axiom.right);
                }
                crate::json_io::SourceAxiomKind::Equivalent => {
                    // `buildPermutableConceptEquivalentClass` chooses a still
                    // undefined named side for a direct CCEQ definition.
                    let candidate = [(&axiom.left, &axiom.right), (&axiom.right, &axiom.left)]
                        .into_iter()
                        .find_map(|(named_side, definition)| {
                            let SourceConcept::Name(name) = named_side else {
                                return None;
                            };
                            if forced_subclass_names.contains(name.as_str())
                                || equivalence_name_counts.get(name.as_str()) != Some(&1)
                            {
                                return None;
                            }
                            let &index = concept_index.get(name.as_str())?;
                            (b.ctx
                                .ontology_arenas()
                                .concept(named[index])
                                .get_operator_code()
                                == op::CCATOM)
                                .then_some((named[index], definition, name.as_str()))
                        });
                    let defined = candidate.is_some_and(|(host, definition, name)| {
                        let Some(built) = build_source_concept(
                            &mut b,
                            definition,
                            &concept_index,
                            &role_index,
                            &named,
                            &roles,
                            &inv_roles,
                            &nominal_by_name,
                            &mut concept_cache,
                        ) else {
                            return false;
                        };
                        equivalent_definition_names.push(name.to_string());
                        // Port of the absorber's equivalence pre-pass. A fully
                        // triggerable definition is changed CCEQ -> CCSUB and
                        // gets the reverse direction as a binary implication.
                        let triggerable = full_absorption_trigger(
                            &mut b,
                            built,
                            &role_inverses,
                            &mut trigger_caches,
                        )
                        .is_some();
                        if triggerable {
                            let forward = b.add_unfolding(host, built.0, built.1);
                            let reverse = absorb_concept_disjunction(
                                &mut b,
                                &[built],
                                &[(host, false)],
                                &role_inverses,
                                &mut trigger_caches,
                            );
                            if forward && reverse {
                                absorbed_equivalent_definitions += 1;
                                true
                            } else {
                                false
                            }
                        } else {
                            let defined = b.add_equivalent_definition(host, built.0, built.1);
                            if defined {
                                // Exact non-candidate branch of
                                // `CTriggeredImplicationBinaryAbsorberPreProcess`
                                // (cpp 203-215). Konclude either builds the
                                // optional partial-equivalence candidate or
                                // inserts the still-CCEQ host into
                                // `mEquivConNonCandidateSet`. The bridge does
                                // not materialise that optional optimization,
                                // so it takes Konclude's non-candidate branch.
                                b.ctx
                                    .ontology_arenas_mut()
                                    .insert_equivalent_concept_non_candidate(host);
                            }
                            defined
                        }
                    });
                    if defined {
                        equivalent_definitions += 1;
                    } else {
                        encode!(&axiom.left, &axiom.right);
                        encode!(&axiom.right, &axiom.left);
                    }
                }
                crate::json_io::SourceAxiomKind::Disjoint => {
                    encode!(
                        &axiom.left,
                        &SourceConcept::Not(Box::new(axiom.right.clone())),
                    );
                    encode!(
                        &axiom.right,
                        &SourceConcept::Not(Box::new(axiom.left.clone())),
                    );
                }
            }
            if bridge_phase_trace && axiom_index > 0 && axiom_index % 4096 == 0 {
                let now = std::time::Instant::now();
                eprintln!(
                    "BRIDGE-PHASE source-progress axioms={}/{} delta={:.3}s total={:.3}s concepts={}",
                    axiom_index,
                    tin.source_axioms.len(),
                    now.duration_since(bridge_phase_started).as_secs_f64(),
                    now.duration_since(bridge_started).as_secs_f64(),
                    b.ctx.ontology_arenas().concept_count(),
                );
                bridge_phase_started = now;
            }
        }
        if native_nominal_covered {
            for (entry, seed) in tin
                .nominal_abox
                .individuals
                .iter()
                .zip(nominal_seeds.iter_mut())
            {
                for assertion in &entry.assertions {
                    let Some((concept, negated)) = build_source_concept(
                        &mut b,
                        assertion,
                        &concept_index,
                        &role_index,
                        &named,
                        &roles,
                        &inv_roles,
                        &nominal_by_name,
                        &mut concept_cache,
                    ) else {
                        source_unsupported += 1;
                        continue;
                    };
                    if !seed.assertions.contains(&(concept, negated)) {
                        seed.assertions.push((concept, negated));
                        b.ctx
                            .ontology_arenas_mut()
                            .individual_mut(seed.individual)
                            .add_assertion_concept_linker(ConceptAssertion {
                                target: concept,
                                negated,
                            });
                    }
                }
            }
            // Keep object-property assertions in the DL-equivalent class form
            // consumed by completion, and in the real named-edge form consumed
            // by individual saturation:
            //
            //   R(a,b)  ->  a : exists R.{b}
            //  !R(a,b) ->  a : forall R.not {b}
            //
            // The two views live in distinct seed fields, so saturation never
            // creates both a named edge and an anonymous existential witness.
            for (assertion, negative) in tin
                .nominal_abox
                .role_assertions
                .iter()
                .map(|assertion| (assertion, false))
                .chain(
                    tin.nominal_abox
                        .negative_role_assertions
                        .iter()
                        .map(|assertion| (assertion, true)),
                )
            {
                let Some(&seed_index) = nominal_seed_index_by_name.get(assertion.source.as_str())
                else {
                    source_unsupported += 1;
                    continue;
                };
                let nominal = SourceConcept::Nominal(assertion.target.clone());
                let filler = if negative {
                    SourceConcept::Not(Box::new(nominal))
                } else {
                    nominal
                };
                let source_assertion = if negative {
                    SourceConcept::Forall(
                        SourceRole::Name(assertion.role.clone()),
                        Box::new(filler),
                    )
                } else {
                    SourceConcept::Exists(
                        SourceRole::Name(assertion.role.clone()),
                        Box::new(filler),
                    )
                };
                let Some((concept, negated)) = build_source_concept(
                    &mut b,
                    &source_assertion,
                    &concept_index,
                    &role_index,
                    &named,
                    &roles,
                    &inv_roles,
                    &nominal_by_name,
                    &mut concept_cache,
                ) else {
                    source_unsupported += 1;
                    continue;
                };
                // Konclude copies positive assertion-role linkers directly
                // into mixed cardinality+ABox completion tasks. Keep the
                // historical existential encoding only outside that exact
                // profile. A genuine class assertion with the same syntax was
                // inserted above and remains in the journal.
                {
                    let seed = &mut nominal_seeds[seed_index];
                    if (negative || !direct_native_role_assertions)
                        && !seed.assertions.contains(&(concept, negated))
                    {
                        seed.assertions.push((concept, negated));
                    }
                }
                if negative {
                    let seed = &nominal_seeds[seed_index];
                    let individual = b.ctx.ontology_arenas_mut().individual_mut(seed.individual);
                    if !individual
                        .get_assertion_concept_linker()
                        .contains(&ConceptAssertion {
                            target: concept,
                            negated,
                        })
                    {
                        individual.add_assertion_concept_linker(ConceptAssertion {
                            target: concept,
                            negated,
                        });
                    }
                } else {
                    let Some(&role_index) = role_index.get(assertion.role.as_str()) else {
                        source_unsupported += 1;
                        continue;
                    };
                    let Some(&target_tag) = nominal_tag_by_name.get(assertion.target.as_str())
                    else {
                        source_unsupported += 1;
                        continue;
                    };
                    let Some(&target_seed_index) =
                        nominal_seed_index_by_name.get(assertion.target.as_str())
                    else {
                        source_unsupported += 1;
                        continue;
                    };
                    let edge = (roles[role_index], target_tag);
                    let source_individual = {
                        let seed = &mut nominal_seeds[seed_index];
                        if !seed.role_assertions.contains(&edge) {
                            seed.role_assertions.push(edge);
                        }
                        seed.individual
                    };
                    let target_individual = nominal_seeds[target_seed_index].individual;
                    let forward = RoleAssertion {
                        role: roles[role_index],
                        individual: target_individual,
                    };
                    let reverse = ReverseRoleAssertion {
                        individual: source_individual,
                        role: roles[role_index],
                        role_assertion: roles[role_index].raw,
                    };
                    {
                        let source = b
                            .ctx
                            .ontology_arenas_mut()
                            .individual_mut(source_individual);
                        if !source.get_assertion_role_linker().contains(&forward) {
                            source.add_assertion_role_linker(forward);
                        }
                    }
                    {
                        let target = b
                            .ctx
                            .ontology_arenas_mut()
                            .individual_mut(target_individual);
                        if !target
                            .get_reverse_assertion_role_linker()
                            .contains(&reverse)
                        {
                            target.add_reverse_assertion_role_linker(reverse);
                        }
                    }
                    // A separately asserted expression may be structurally
                    // identical to the generated `exists R.{b}`. The real edge
                    // already entails it, so remove that concept from the
                    // saturation-side model label to prevent a second witness.
                    b.ctx
                        .ontology_arenas_mut()
                        .individual_mut(source_individual)
                        .assertion_concept_linker
                        .retain(|assertion| {
                            assertion.target != concept || assertion.negated != negated
                        });
                }
            }
        }
        bridge_phase!("source-build");
        unsupported += source_unsupported;
        if std::env::var_os("KM_HT_STATS").is_some() {
            eprintln!(
                "bridge [source-tbox] axioms={} eq={}/{} {:?} direct={} role-links={} absorbed-gci={} top-gci={} unsupported={}",
                tin.source_axioms.len(),
                absorbed_equivalent_definitions,
                equivalent_definitions,
                equivalent_definition_names,
                direct,
                role_links,
                absorbed,
                residual,
                source_unsupported
            );
        }
    }

    'clause: for cl in &tin.clauses {
        // hierarchy clauses (plain + inverse) were consumed by pass 1
        if is_hierarchy(cl).is_some() || is_inv_hierarchy(cl).is_some() {
            continue;
        }
        // functional clauses were consumed by pass 2
        if is_functional(cl).is_some() {
            continue;
        }
        // An exact positive unit constraint proves that its named concept is
        // empty. In source mode this shape is not necessarily a duplicate:
        // the frontend bottom prepass appends newly certified consequences to
        // `clauses`, while `source_axioms` deliberately retains only source
        // provenance. Let the ordinary encoder below install the constraint
        // and retain its concept index for a proof-backed direct answer.
        let unit_bottom = match (cl.body.as_slice(), cl.head.as_slice()) {
            ([HAtom::Concept { neg: false, c, .. }], []) => Some(*c),
            _ => None,
        };
        if source_mode {
            if let Some(concept) = unit_bottom {
                certified_unsatisfiable.push(concept);
            }
        }
        // Source class axioms and RBox domain/range axioms have already been
        // installed from their provenance-bearing side channels. Suppress all
        // ordinary concept-bearing clausifier copies. Pure datatype-map
        // relation clauses are an exact derived theory absent from
        // `source_axioms`, so they continue through the ordinary encoder.
        if source_mode && source_mode_suppresses_ordinary_concept_clause(tin, cl) {
            continue;
        }
        // ---- classify the clause's variable/role shape -------------------
        let mut body_roles: Vec<(usize, usize, usize)> = Vec::new(); // (r, s, t)
        let mut body_bad = false;
        for a in &cl.body {
            match a {
                HAtom::Role { r, s, t } => body_roles.push((*r, *s, *t)),
                HAtom::Eq { .. } | HAtom::Exist { .. } => {
                    body_bad = true;
                }
                HAtom::Concept { .. } => {}
            }
        }
        if body_bad {
            unsupported += 1;
            dump(cl, "body-eq-or-exist");
            continue 'clause;
        }
        // ---- ≥k-recognition: guards(0) ∧ C(t_i) ∧ R(0,t_i) → D(0)… ∨ all-pairs eq ----
        // `⋀guards ⊓ ≥k R.C ⊑ ⋁D` ⟺ `implication(guards → ⋁D ∨ ≤(k−1) R.C)`:
        // k pairwise-distinct R.C-successors force some D, and the ≤(k−1)
        // qualified at-most (the ported CCATMOST merge rule) carries the
        // eq-head semantics exactly — so the clause is CONSUMED, not
        // unsupported. A shared-TARGET orientation (`R(t_i,0)`, e.g. inverse-
        // functional) encodes on the concrete inverse-role object.
        //
        // Recognition encoding: DEFAULT ON (`KM_HT_BRIDGE_NO_RECOG` opts
        // out). The early "3 spurious onto `Path`" measurement that kept this
        // arm opt-in was NOT this encoding's fault: the answers rode the
        // phantom card-def root re-seed (fixed 84e38bf) and the u29 DDB
        // leftover-poisoning wrong-cancel (fixed 7c521cb). With both fixed,
        // ore_ont_12653 classifies gold-clean (missing=0 spurious=0) with
        // this arm on, and the oracle suite is green in all 6 search-mode
        // combos. Without it every eq-head clause counts unsupported and the
        // production driver declines whole recognition-family ontologies.
        if !body_roles.is_empty()
            && cl.head.iter().any(|a| matches!(a, HAtom::Eq { .. }))
            && std::env::var_os("KM_HT_BRIDGE_NO_RECOG").is_none()
        {
            let recog = (|| -> Option<(RoleId, usize, Option<usize>, Vec<(usize, bool)>, Vec<usize>, usize)> {
                let r0 = body_roles[0].0;
                if body_roles.iter().any(|&(r, _, _)| r != r0) {
                    return None;
                }
                // orientation: all roles share the source var (hub) or all
                // share the target var (inverse orientation).
                let (role_obj, hub, mut targets): (RoleId, usize, Vec<usize>) =
                    if body_roles.iter().all(|&(_, s, _)| s == body_roles[0].1) {
                        (roles[r0], body_roles[0].1, body_roles.iter().map(|&(_, _, t)| t).collect())
                    } else if body_roles.iter().all(|&(_, _, t)| t == body_roles[0].2) {
                        (inv_roles[r0], body_roles[0].2, body_roles.iter().map(|&(_, s, _)| s).collect())
                    } else {
                        return None;
                    };
                targets.sort_unstable();
                let k = targets.len();
                if k < 2 {
                    return None;
                }
                targets.dedup();
                if targets.len() != k || targets.contains(&hub) {
                    return None;
                }
                let mut guards: Vec<(usize, bool)> = Vec::new();
                let mut per_target: HashMap<usize, Vec<usize>> = HashMap::new();
                for a in &cl.body {
                    if let HAtom::Concept { neg, c, t } = a {
                        if *t == hub {
                            guards.push((*c, *neg));
                        } else if targets.binary_search(t).is_ok() {
                            if *neg {
                                return None;
                            }
                            per_target.entry(*t).or_default().push(*c);
                        } else {
                            return None;
                        }
                    }
                }
                // the qualifier: the SAME (≤1-element) positive concept list
                // on every successor variable.
                let mut qual: Option<Vec<usize>> = None;
                for t in &targets {
                    let mut v = per_target.remove(t).unwrap_or_default();
                    v.sort_unstable();
                    match &qual {
                        None => qual = Some(v),
                        Some(q) if *q == v => {}
                        _ => return None,
                    }
                }
                let qual = qual.unwrap_or_default();
                if qual.len() > 1 {
                    return None;
                }
                let mut heads: Vec<usize> = Vec::new();
                let mut eqs: BTreeSet<(usize, usize)> = BTreeSet::new();
                for a in &cl.head {
                    match a {
                        HAtom::Concept { neg, c, t } => {
                            if *neg || *t != hub {
                                return None;
                            }
                            heads.push(*c);
                        }
                        HAtom::Eq { s, t } => {
                            eqs.insert((*s.min(t), *s.max(t)));
                        }
                        _ => return None,
                    }
                }
                let mut want: BTreeSet<(usize, usize)> = BTreeSet::new();
                for i in 0..k {
                    for j in (i + 1)..k {
                        want.insert((targets[i], targets[j]));
                    }
                }
                if eqs != want {
                    return None;
                }
                Some((role_obj, k, qual.first().copied(), guards, heads, r0))
            })();
            if let Some((role_obj, k, qual, guards, heads, _r0)) = recog {
                // KM_BRIDGE_DUMP_RECOG: print each recognized ≥k clause's
                // encoding parameters (spurious-subsumption hunts).
                if std::env::var_os("KM_BRIDGE_DUMP_RECOG").is_some() {
                    eprintln!(
                        "RECOG r={_r0} k={k} qual={qual:?} guards={guards:?} heads={heads:?} ({})",
                        if guards.is_empty() {
                            "TOP-ATTACHED"
                        } else {
                            "absorbed"
                        }
                    );
                }
                let am = match qual {
                    Some(c) => b.atmost_q(role_obj, (k - 1) as Cint64, resolved[c]),
                    None => b.atmost(role_obj, (k - 1) as Cint64),
                };
                let mut head_ops: Vec<(ConceptId, bool)> = heads
                    .iter()
                    .map(|&c| {
                        if trigger_absorb {
                            resolved[c]
                        } else {
                            (named[c], false)
                        }
                    })
                    .collect();
                head_ops.push((am, false));
                if trigger_absorb {
                    let body_ops: Vec<(ConceptId, bool)> = guards
                        .iter()
                        .map(|&(c, negated)| (resolved[c].0, resolved[c].1 ^ negated))
                        .collect();
                    if absorb_concept_disjunction(
                        &mut b,
                        &body_ops,
                        &head_ops,
                        &role_inverses,
                        &mut trigger_caches,
                    ) {
                        continue 'clause;
                    }
                }
                let head = b.or_of(&head_ops);
                let triggers: Vec<(ConceptId, bool)> =
                    guards.iter().map(|&(c, n)| (named[c], n)).collect();
                let imp = b.implication(head, &triggers);
                tbox.push(imp);
                match triggers.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => {
                        dump_top(cl, "recog");
                        top_gcis.push(imp)
                    }
                }
                continue 'clause;
            }
        }
        // ---- singleton-concept recognition: `C(v1) ∧ C(v2) → v1 = v2` ------
        // The clausal datatype value-identity shape (a literal value is one
        // semantic object, so any two carriers of `__dt__val__…` are equal;
        // Konclude gets this natively from its databox literal handling, the
        // clausal frontend surfaces it role-free). CONSUMED as a singleton
        // registration: the kernel's deterministic scan-at-fixpoint merge
        // (u02 `ht_apply_singleton_merges`) realises the eq head exactly —
        // deterministic (single-disjunct head), no branch point. General
        // structural rule: any concept in this shape is a singleton.
        // KM_HT_NO_SINGLETON: diagnostic A/B gate — count the shape
        // unsupported instead (the pre-d58c2b2 behaviour: the driver then
        // DECLINES, isolating the merge rule's effect on spuriousness).
        if body_roles.is_empty()
            && cl.body.len() == 2
            && cl.head.len() == 1
            && std::env::var_os("KM_HT_NO_SINGLETON").is_none()
        {
            if let (
                HAtom::Concept {
                    neg: false,
                    c: c0,
                    t: t0,
                },
                HAtom::Concept {
                    neg: false,
                    c: c1,
                    t: t1,
                },
                HAtom::Eq { s: es, t: et },
            ) = (&cl.body[0], &cl.body[1], &cl.head[0])
            {
                if c0 == c1 && t0 != t1 {
                    let (a, bb) = (*t0.min(t1), *t0.max(t1));
                    let (ea, eb) = (*es.min(et), *es.max(et));
                    if (a, bb) == (ea, eb) {
                        let sc = named[*c0];
                        if !singleton_concepts.contains(&sc) {
                            singleton_concepts.push(sc);
                        }
                        continue 'clause;
                    }
                }
            }
        }
        if cl
            .head
            .iter()
            .any(|a| matches!(a, HAtom::Role { .. } | HAtom::Eq { .. }))
        {
            unsupported += 1;
            dump(cl, "head-role-or-eq");
            continue 'clause;
        }
        let vars: BTreeSet<usize> = cl
            .body
            .iter()
            .chain(cl.head.iter())
            .flat_map(|a| match a {
                HAtom::Concept { t, .. } | HAtom::Exist { t, .. } => vec![*t],
                HAtom::Role { s, t, .. } => vec![*s, *t],
                HAtom::Eq { s, t } => vec![*s, *t],
            })
            .collect();

        // literal → (concept, negated), positively as written
        let lit = |b: &mut Builder, a: &HAtom| -> (ConceptId, bool) {
            match a {
                HAtom::Concept { neg, c, .. } => (named[*c], *neg),
                HAtom::Exist { r, neg, c, .. } => {
                    let filler = (named[*c], *neg);
                    (b.some(roles[*r], filler), false)
                }
                _ => unreachable!("filtered above"),
            }
        };

        if body_roles.is_empty() && vars.iter().all(|&v| v == 0) {
            // ---- pure concept clause over the root variable --------------
            if trigger_absorb {
                let body_ops: Vec<(ConceptId, bool)> = cl
                    .body
                    .iter()
                    .map(|a| match a {
                        HAtom::Concept { neg, c, .. } => (resolved[*c].0, resolved[*c].1 ^ *neg),
                        _ => unreachable!("role/eq bodies filtered"),
                    })
                    .collect();
                let mut head_ops = Vec::new();
                for a in &cl.head {
                    match a {
                        HAtom::Concept { neg, c, .. } => {
                            head_ops.push((resolved[*c].0, resolved[*c].1 ^ *neg));
                        }
                        HAtom::Exist { r, neg, c, .. } => {
                            let filler = (resolved[*c].0, resolved[*c].1 ^ *neg);
                            head_ops.push((b.some(roles[*r], filler), false));
                        }
                        _ => unreachable!("role/eq heads filtered"),
                    }
                }

                // Konclude `asorbForallsToRanges`: TOP -> ALL R.C is stored on
                // the role and removed from TOP after GCI absorption.
                if body_ops.is_empty() && head_ops.len() == 1 && !head_ops[0].1 {
                    let (op_code, role, operands) = {
                        let c = b.ctx.ontology_arenas().concept(head_ops[0].0);
                        (
                            c.get_operator_code(),
                            c.get_role(),
                            c.get_operand_list().to_vec(),
                        )
                    };
                    if op_code == op::CCTOP {
                        continue 'clause;
                    }
                    if op_code == op::CCALL && operands.len() == 1 {
                        let link = operands[0];
                        b.ctx
                            .ontology_arenas_mut()
                            .role_mut(role)
                            .range_linker
                            .push(link);
                        if let Some(&inverse) = role_inverses.get(&role) {
                            b.ctx
                                .ontology_arenas_mut()
                                .role_mut(inverse)
                                .domain_linker
                                .push(link);
                        }
                        continue 'clause;
                    }
                }

                if absorb_concept_disjunction(
                    &mut b,
                    &body_ops,
                    &head_ops,
                    &role_inverses,
                    &mut trigger_caches,
                ) {
                    continue 'clause;
                }
            }
            let raw_triggers: Vec<(ConceptId, bool)> = cl
                .body
                .iter()
                .map(|a| match a {
                    HAtom::Concept { neg, c, .. } => (named[*c], *neg),
                    _ => unreachable!("role/eq bodies filtered"),
                })
                .collect();
            let raw_heads: Vec<(ConceptId, bool)> =
                cl.head.iter().map(|a| lit(&mut b, a)).collect();
            let mut triggers = Vec::new();
            let mut heads = Vec::new();
            for (c, neg) in raw_triggers {
                if neg {
                    heads.push((c, false));
                } else {
                    triggers.push((c, false));
                }
            }
            for (c, neg) in raw_heads {
                if neg {
                    triggers.push((c, false));
                } else {
                    heads.push((c, false));
                }
            }
            triggers.sort_by_key(|(c, n)| (c.raw, *n));
            triggers.dedup();
            heads.sort_by_key(|(c, n)| (c.raw, *n));
            heads.dedup();
            let opposite =
                |ops: &[(ConceptId, bool)]| ops.iter().any(|&(c, n)| ops.contains(&(c, !n)));
            if opposite(&triggers)
                || opposite(&heads)
                || triggers.iter().any(|lit| heads.contains(lit))
            {
                continue 'clause;
            }
            let head = if heads.is_empty() {
                (b.bottom(), false)
            } else {
                b.or_of(&heads)
            };
            let imp = b.implication(head, &triggers);
            tbox.push(imp);
            match triggers.iter().find(|&&(_, neg)| !neg) {
                Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                None => {
                    dump_top(cl, "pure-concept");
                    top_gcis.push(imp)
                }
            }
            continue;
        }

        if body_roles.len() == 1 {
            // ---- guarded two-variable clause: R(x, y) --------------------
            let (r, s, t) = body_roles[0];
            if s != 0 || t == 0 || vars.iter().any(|&v| v != s && v != t) {
                unsupported += 1;
                dump(cl, "guarded-var-shape");
                continue;
            }
            let _ = r;
            let mut triggers: Vec<(ConceptId, bool)> = Vec::new(); // at x
            let mut succ_body: Vec<(ConceptId, bool)> = Vec::new(); // at y
            for a in &cl.body {
                if let HAtom::Concept { neg, c, t: at } = a {
                    if *at == 0 {
                        triggers.push((named[*c], *neg));
                    } else {
                        succ_body.push((named[*c], *neg));
                    }
                }
            }
            let mut head_x: Vec<(ConceptId, bool)> = Vec::new();
            let mut head_y: Vec<(ConceptId, bool)> = Vec::new();
            for a in &cl.head {
                let at = match a {
                    HAtom::Concept { t, .. } | HAtom::Exist { t, .. } => *t,
                    _ => unreachable!("filtered above"),
                };
                if at == 0 {
                    head_x.push(lit(&mut b, a));
                } else if matches!(a, HAtom::Exist { .. }) {
                    // nested ∃ under the ∀ — out of the v1 fragment
                    unsupported += 1;
                    dump(cl, "nested-exist-under-forall");
                    continue 'clause;
                } else {
                    head_y.push(lit(&mut b, a));
                }
            }
            let mut norm_triggers = Vec::new();
            let mut norm_head_x = Vec::new();
            for (c, neg) in triggers.drain(..) {
                if neg {
                    norm_head_x.push((c, false));
                } else {
                    norm_triggers.push((c, false));
                }
            }
            for (c, neg) in head_x.drain(..) {
                if neg {
                    norm_triggers.push((c, false));
                } else {
                    norm_head_x.push((c, false));
                }
            }
            triggers = norm_triggers;
            head_x = norm_head_x;

            let mut norm_succ_body = Vec::new();
            let mut norm_head_y = Vec::new();
            for (c, neg) in succ_body.drain(..) {
                if neg {
                    norm_head_y.push((c, false));
                } else {
                    norm_succ_body.push((c, false));
                }
            }
            for (c, neg) in head_y.drain(..) {
                if neg {
                    norm_succ_body.push((c, false));
                } else {
                    norm_head_y.push((c, false));
                }
            }
            succ_body = norm_succ_body;
            head_y = norm_head_y;
            if !triggers.is_empty() {
                // ---- x-triggered: C ⊑ … ∨ ∀R.(¬D ∨ …) ---------------------
                // ∀R.( ¬D1 ∨ … ∨ F1 ∨ … ) — the y-side residue
                let mut y_ops: Vec<(ConceptId, bool)> = succ_body
                    .iter()
                    .map(|&(c, n)| (c, !n)) // body atoms flip polarity
                    .collect();
                y_ops.extend(head_y.iter().copied());
                let y_disj = if y_ops.is_empty() {
                    (b.bottom(), false)
                } else {
                    b.or_of(&y_ops)
                };
                let all = (b.all(roles[r], y_disj), false);
                // KM_BRIDGE_DUMP_FORALL=<role_idx>: print the antecedent
                // (trigger tags) of every ∀<role>.… implication built here —
                // reveals whether a ∀ is concept-gated or global (all-negative
                // triggers ⇒ TOP-attached ⇒ fires on every node).
                if std::env::var("KM_BRIDGE_DUMP_FORALL")
                    .ok()
                    .and_then(|s| s.parse::<usize>().ok())
                    == Some(r)
                {
                    let tt: Vec<String> = triggers
                        .iter()
                        .map(|&(c, n)| {
                            format!(
                                "{}{}",
                                if n { "¬" } else { "" },
                                b.ctx.ontology_arenas().concept(c).get_concept_tag()
                            )
                        })
                        .collect();
                    let ft: Vec<String> = y_ops
                        .iter()
                        .map(|&(c, n)| {
                            format!(
                                "{}{}",
                                if n { "¬" } else { "" },
                                b.ctx.ontology_arenas().concept(c).get_concept_tag()
                            )
                        })
                        .collect();
                    let global = triggers.iter().all(|&(_, n)| n);
                    eprintln!(
                        "DUMP-FORALL role={r} triggers=[{}] fillers=[{}] GLOBAL={global}",
                        tt.join(" "),
                        ft.join(" ")
                    );
                }
                let head = if head_x.is_empty() {
                    all
                } else {
                    let mut ops = head_x;
                    ops.push(all);
                    b.or_of(&ops)
                };
                let imp = b.implication(head, &triggers);
                tbox.push(imp);
                match triggers.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => {
                        dump_top(cl, "forall-residue");
                        top_gcis.push(imp)
                    }
                }
            } else if !succ_body.is_empty() {
                // ---- y-triggered (the absorption shape): ------------------
                // `D(y) ∧ R(x,y) → E(x) ∨ F(y)`  ≡  `D ⊑ F ∨ ∀R⁻.E`
                // (the cb_to_ht definer RECOGNITION direction). Encoded
                // trigger-less it would be a covering disjunction branching
                // on EVERY node (measured: unbounded successor chains); the
                // inverse-∀ form fires only on D-nodes and rides the ported
                // inverse-edge propagation (`inverse_role_propagation`
                // selftest). Konclude reaches the same behaviour through
                // absorption's backward implication triggers.
                let x_disj = if head_x.is_empty() {
                    (b.bottom(), false)
                } else {
                    b.or_of(&head_x)
                };
                let all_inv = (b.all(inv_roles[r], x_disj), false);
                let head = if head_y.is_empty() {
                    all_inv
                } else {
                    let mut ops = head_y;
                    ops.push(all_inv);
                    b.or_of(&ops)
                };
                let imp = b.implication(head, &succ_body);
                tbox.push(imp);
                match succ_body.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => {
                        dump_top(cl, "inv-forall-residue");
                        top_gcis.push(imp)
                    }
                }
            } else if head_y.is_empty() && !head_x.is_empty() {
                // ---- domain axiom `R(x,y) → C(x) [∨ D(x) …]` ----------------
                // Konclude stores these on the role (CRole::domainLinker) and
                // applies them at every link install
                // (createNewIndividualsLink* cpp 22382–22395, ported in u08
                // ht_apply_role_domain_range) — node-count-independent, no
                // covering disjunction needed.
                let (c, neg) = b.or_of(&head_x);
                let nl = super::model::substrate::NegLink {
                    target: c,
                    negated: neg,
                };
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(roles[r])
                    .domain_linker
                    .push(nl);
                // domain(R) = range(R⁻): keep the inverse object consistent so
                // whichever edge direction is installed applies the concept.
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inv_roles[r])
                    .range_linker
                    .push(nl);
            } else if head_x.is_empty() && !head_y.is_empty() {
                // ---- range axiom `R(x,y) → C(y) [∨ D(y) …]` -----------------
                let (c, neg) = b.or_of(&head_y);
                let nl = super::model::substrate::NegLink {
                    target: c,
                    negated: neg,
                };
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(roles[r])
                    .range_linker
                    .push(nl);
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inv_roles[r])
                    .domain_linker
                    .push(nl);
            } else if head_x.is_empty() && head_y.is_empty() {
                // ---- `R(x,y) → ⊥` (empty role): domain ⊥ — any R-edge
                // immediately clashes its source, exactly the axiom's force.
                let bot = b.bottom();
                let nl = super::model::substrate::NegLink {
                    target: bot,
                    negated: false,
                };
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(roles[r])
                    .domain_linker
                    .push(nl);
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inv_roles[r])
                    .range_linker
                    .push(nl);
            } else {
                // mixed x/y disjunctive head over an edge with no concept
                // trigger (`R(x,y) → C(x) ∨ D(y)`) — out of the v1 fragment
                // (needs the covering-disjunction machinery Konclude gets from
                // absorption + branch triggers).
                unsupported += 1;
                dump(cl, "edge-no-concept-trigger");
            }
            continue;
        }

        if trigger_absorb
            && body_roles.len() > 1
            && absorb_role_tree_clause(
                &mut b,
                cl,
                &resolved,
                &roles,
                &inv_roles,
                &role_inverses,
                &mut trigger_caches,
            )
        {
            continue 'clause;
        }
        unsupported += 1;
        dump(cl, "multi-role-body");
    }
    bridge_phase!("clause-scan");

    // ---- functional roles → `≤1 R` on TOP (every node) ---------------------
    // Emitted while the Builder still holds the arena borrow. Each functional
    // role R contributes an unqualified `CCATMOST(R, 1)`; attaching it to TOP
    // makes every node enforce ≤1 R-successor via the ported merge rule. The
    // atmost is also seeded on the root each drive pass (it is a universal
    // constraint, not trigger-gated).
    let functional_count = functional_roles.len();
    let atmost_concepts: Vec<ConceptId> = functional_roles
        .iter()
        .map(|&r| b.atmost(roles[r], 1))
        .collect();
    for &a in &atmost_concepts {
        tbox.push(a);
        top_gcis.push(a);
    }

    // ---- first-class number restrictions (KM_HT_CARD `card_defs`) ----------
    // `marker ⊑ ≥n role.filler` / `marker ⊑ ≤n role.filler`, resolved to the
    // ported CCATLEAST / (qualified) CCATMOST concepts and hung off the
    // marker's absorption (CCSUB → AND rule asserts the restriction exactly
    // on marker-labelled nodes). The clausal `⋁ eq` pigeonhole for each
    // marker was already dropped by `cb_to_ht::convert(card_enabled=true)`.
    // NOT in `tbox`: the root re-seed loop dispatches every tbox concept on
    // the probe root QUEUE-ONLY (no label add). Implications self-gate on
    // their retained trigger linkers, but a raw CCATLEAST/CCATMOST enforces
    // UNCONDITIONALLY — seeding it applied the marker's number restriction
    // to every probe subject (measured: covering_atmost_cross_merge_sat,
    // the guard-less `≤2 r.E` armed on the root at branch depth 0 refuted
    // the SAT covering branch). The restriction reaches exactly the
    // marker-labelled nodes through the absorption unfold below.
    for cd in tin.card_defs.iter().filter(|_| !source_mode) {
        let filler = resolved[cd.filler];
        let c = if cd.min {
            b.atleast_q(roles[cd.role], cd.n as Cint64, filler)
        } else {
            b.atmost_q(roles[cd.role], cd.n as Cint64, filler)
        };
        absorbed_pairs.push((named[cd.marker], c));
    }

    // ---- attachment pass: absorption wiring (Konclude's CCSUB mechanism) ---
    // An implication with a positive concept trigger is attached as an
    // operand of that trigger's concept, whose opcode is promoted CCATOM →
    // CCSUB: positive CCSUB dispatches to the AND rule (mPosJumpFuncVec[CCSUB]
    // = applyANDRule; negated CCSUB is atomaric), so the implication is
    // unfolded ONLY in nodes whose label actually contains the trigger —
    // node-count-independent, exactly how absorbed GCIs hang off named
    // concepts in Konclude. This is what keeps per-node work flat: without it
    // every node scanned the whole TBox through TOP (measured on ore_ont_1016:
    // 388 nodes × 13k TOP impls = the 5M drive cap). Restricting assertion to
    // trigger-nodes is sound AND complete (in a trigger-free node the clause
    // is vacuous — the standard absorption argument; DL-clause bodies are
    // positive atoms). The retained ¬trigger linker inside the CCIMPL is then
    // trivially satisfied at unfold time and the remaining triggers ride the
    // condensed reapply queue (install-to-trigger).
    for &(host, imp) in &absorbed_pairs {
        let op_code = b.ctx.ontology_arenas().concept(host).get_operator_code();
        if !matches!(op_code, op::CCATOM | op::CCSUB | op::CCIMPLTRIG) {
            // Never mutate a restriction's operand list into an unfolding list.
            // This guard is the bridge equivalent of Konclude's
            // `addUnfoldingConceptForConcept` operator check.
            tbox.push(imp);
            top_gcis.push(imp);
            continue;
        }
        let c = b.ctx.ontology_arenas_mut().concept_mut(host);
        if op_code == op::CCATOM {
            c.set_operator_code(op::CCSUB);
        }
        c.add_operand_linker(imp, false);
        c.inc_operand_count(1);
    }
    bridge_phase!("attachments");

    // Trigger-less implications go to the ontology TOP concept (Konclude's
    // universal-constraint attachment): `CCTOP` dispatches to the AND rule,
    // and `create_new_individual` labels every fresh successor with TOP — so
    // these reach EVERY node. The probe driver still re-seeds the FULL tbox
    // list on the ROOT each pass (root nodes are not created through
    // `create_new_individual`, so they never receive TOP; the re-drive also
    // remains the cross-drive safety net).
    let top = b.ctx.processing_data_box().ontology_top_concept();
    if top.is_some() {
        let n = top_gcis.len() as i64;
        let top_concept = b.ctx.ontology_arenas_mut().concept_mut(top);
        for &g in &top_gcis {
            top_concept.add_operand_linker(g, false);
        }
        let count = top_concept.get_operand_count();
        top_concept.set_operand_count(count + n);
    }

    // Konclude's common-disjunct extraction feeds CReplacementData read by
    // initializeORProcessing.  The implication-replacement producer requires
    // Konclude's negative trigger-propagation substrate as well; it remains
    // disabled until that producer-to-trigger slice is complete.
    let common_disjunct_replacement_count = extract_common_disjunct_replacements(b.ctx);
    bridge_phase!("common-disjuncts");
    if std::env::var_os("KM_HT_STATS").is_some() {
        eprintln!(
            "bridge [or-replacements] implications=0 common={common_disjunct_replacement_count}"
        );
    }

    // Konclude runs this production preprocessor after the RBox and TBox are
    // built. It rewrites complex-role restrictions to AQCHOOSE/AQAND/AQALL
    // automata consumed by the ported completion and saturation rules.
    RoleChainAutomataTransformationPreProcess::new().preprocess(ctx.ontology_arenas_mut());
    bridge_phase!("role-automata");

    // Konclude's branch-trigger extractor runs after the terminology role
    // transformations. Installing its domain markers earlier would make the
    // automata pass incorrectly translate the diagnostic trigger concepts.
    let next_tag = (0..ctx.ontology_arenas().concept_count())
        .map(|index| {
            ctx.ontology_arenas()
                .concept(ConceptId::new(index as Cint64))
                .get_concept_tag()
        })
        .max()
        .unwrap_or(TAG_BASE)
        + 1;
    let branch_role_trigger_count = {
        let mut builder = Builder { ctx, next_tag };
        install_branch_role_domain_triggers(&mut builder, &mut trigger_caches)
    };
    bridge_phase!("branch-triggers");
    if std::env::var_os("KM_HT_STATS").is_some() {
        eprintln!("bridge [branch-triggers] role-markers={branch_role_trigger_count}");
    }

    // KONCLUDE-PORT-NOTE[terminology]: in Konclude every TBox concept carries
    // its owning CTerminology; several guards key on `getTerminology() !=
    // nullptr` — notably u22's unsat-cache write validation, which REJECTS
    // descriptors of terminology-less concepts (meant to exclude fresh
    // query/nominal concepts whose semantics are not ontology-stable).
    // Bridged concepts ARE the ontology (a deterministic function of `tin`,
    // stable across probes), so stamp them all — without this the unsat
    // cache silently never writes a line (measured on ore_ont_12653:
    // 0 written / 0 hits). The sweep covers every builder helper plus the
    // caller-created TOP.
    {
        let arenas = ctx.ontology_arenas_mut();
        let n = arenas.concept_count();
        for i in 0..n {
            arenas
                .concept_mut(ConceptId::new(i as Cint64))
                .set_terminology(1);
        }
    }
    bridge_phase!("terminology-stamp");

    // Konclude's preprocessors may add assertions after the source ABox was
    // materialized. In particular, nominal trigger absorption asserts a fresh
    // CCIMPLTRIG on the corresponding named individual. Saturation reads the
    // model individual directly; the completion bridge replays
    // `NominalSeed::assertions`, so carry every later model assertion into
    // that replay journal as well. Keep completion-only `exists R.{b}` entries
    // already in the seed: the saturation model deliberately represents those
    // positive role assertions as named edges instead.
    if native_nominal_covered {
        for seed in &mut nominal_seeds {
            let model_assertions = ctx
                .ontology_arenas()
                .individual(seed.individual)
                .get_assertion_concept_linker()
                .to_vec();
            for assertion in model_assertions {
                let literal = (assertion.target, assertion.negated);
                if !seed.assertions.contains(&literal) {
                    seed.assertions.push(literal);
                }
            }
        }
    }

    let _ = functional_count;
    certified_unsatisfiable.sort_unstable();
    certified_unsatisfiable.dedup();
    Bridged {
        named,
        roles,
        tbox,
        unsupported,
        absorbed: absorbed_pairs.len(),
        top_attached: top_gcis.len(),
        singleton_concepts,
        source_tbox: source_mode,
        certified_unsatisfiable,
        nominal_seeds,
        direct_native_role_assertions,
        nominal_different,
        native_representative_cache: RefCell::new(None),
        native_consistency_nominal_nondeterministic_prefix: RefCell::new(None),
    }
}

// ---------------------------------------------------------------------------
// Probe driver — the classify_test re-drive harness over a bridged TBox.
// ---------------------------------------------------------------------------

/// Konclude's DEFAULT blocking configuration for a probe algorithm — the
/// cpp-constructor (115-118, 157) + `readCalculationConfig` default branch
/// (u31): optimized subset blocking searched through the anywhere linked
/// candidate hash, with lazy exact hashing; `saveCoreBlockingConceptsCandidates`
/// is coupled to the linked search (cpp 741). Without a blocking search the
/// completion NEVER blocks (`get_blocking_individual_node` returns NONE when
/// every search flag is off) and any ∃-cycle or DAG-unrolled successor tree
/// runs into the drive cap — measured on ore_ont_1016's Abdomen probe.
pub fn configure_default_blocking(algo: &mut CompletionTaskHandleAlgorithm) {
    // KM_HT_DDB: opt-in dependency-directed backjumping (Konclude's
    // `clashedBacktracking`, u29). Turns the dependency spine ON (every rule
    // application then materializes its dependency node + track point, exactly
    // Konclude's default) and routes clashes through the tracked-clash analysis
    // so the in-process OR backtrack can SKIP branch points the clash does not
    // depend on. Target: the 541 family (deep chronological thrashing).
    if std::env::var_os("KM_HT_DDB").is_some() {
        algo.conf_build_dependencies = true;
        algo.conf_dependency_backjumping = true;
        // Konclude production defaults (CReasonerConfigurationGroup):
        // SemanticBranching=false, AtomicSemanticBranching=true — a new
        // alternative asserts the negation of every previously refuted ATOMIC
        // disjunct, so sibling subtrees cannot re-explore failed disjuncts.
        // KM_HT_NO_SEMB: diagnostic opt-out to isolate its effect on the
        // search shape (541: node growth appeared with semb on).
        if std::env::var_os("KM_HT_NO_SEMB").is_none() {
            algo.conf_atomic_semantic_branching = true;
        }
        // KM_HT_DDB_REFUTED_DISCARD: DIAGNOSTIC, DEFAULT OFF. Lets the DDB
        // stack walk discard a positionally-exhausted refuted decision with the
        // subtree above it (u02 `try_backtrack_or_branch_ddb`). UNSOUND — KM has
        // no per-alternative refutation record to justify it (12 spurious
        // `PathOfLength3 ⊑ X` on ore_ont_12653); read here so the unsafe escape
        // is opt-in from ONE place and a probe reset (which re-runs this
        // function) cannot silently acquire it. No inverse switch exists.
        algo.conf_ddb_refuted_discard = std::env::var_os("KM_HT_DDB_REFUTED_DISCARD").is_some();
    }
    // Complete-state restore per alternative via arena journals. The per-node
    // localization landed
    // 2026-07-09: the heavy per-node satellites (label sets, processing
    // queues) are Arc-COW in the process context — a journal save is an O(1)
    // Arc clone and the deep copy happens only for objects the alternative
    // actually writes (Konclude's task-fork copy-on-first-write shape). That
    // removed the uniform-journal whale (12653 DDB classify 0.9s → 260s was
    // the old cost), but COW remains NON-default: measured 2026-07-09
    // (cowddb-48445184), 12653's probes under COW and under COW+DDB both
    // exceed 600s where plain DEFERS in 10s — with complete restores the
    // search must genuinely explore the alternatives that plain-mode
    // leftovers (unsoundly, hence the poison discipline) prune, so the
    // residual gap was SEARCH VOLUME in the old post-clausal terminology. The
    // source-level absorber removes that generated search space; complete COW
    // is therefore the default under KM_TRIGGER_ABSORB and is required for
    // sound sibling isolation (PathOfLength4 in ore_ont_12653 is the oracle).
    // KM_HT_COW also enables it independently; KM_NO_TRIGGER_COW is diagnostic.
    if std::env::var_os("KM_HT_COW").is_some()
        || (std::env::var_os("KM_TRIGGER_ABSORB").is_some()
            && std::env::var_os("KM_NO_TRIGGER_COW").is_none())
    {
        algo.conf_inprocess_cow = true;
    }
    // KM_HT_UNSATCACHE (opt-in, composable with DDB/COW): Konclude's
    // unsatisfiable-cache LEARNING — the search-volume lever the 2026-07-09
    // COW+DDB measurement demands. The write side is u29's clashedBacktracking
    // (`writeClashDescriptorsToCache`, cpp 6844/7009/7056/7332 — already
    // ported and called; it no-ops without an installed handler), validated by
    // u22's guards (single node level, terminology concepts only, no nominals,
    // no atomic clash) so an entry is a self-contained label subset that is
    // unsatisfiable wrt the TBox — a learned nogood, valid across probes. The
    // read side is `testIndividualNodeUnsatisfiableCached` (u21, cpp
    // 4363–4392) probed at Konclude's rule points (OR disjunct addition,
    // SOME/ATLEAST successor generation, at-most init/merge — the constant
    // `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy`).
    // Konclude runs both ON by default (u31 cpp 604–697). The write side only
    // fires inside DDB's tracked-clash analysis, so this is inert without
    // KM_HT_DDB; the intended production combo is COW+DDB+UNSATCACHE.
    if std::env::var_os("KM_HT_UNSATCACHE").is_some() {
        algo.conf_write_unsat_caching = true;
        algo.conf_test_occur_unsat_cached = true;
    }
    // KM_BRIDGE_NO_BLOCKING: diagnostic knob — run the probe with blocking OFF
    // (∃-cycles then hit the drive cap ⇒ Stop/None). If a verdict that flips
    // WITH blocking becomes stable WITHOUT it, the blocking establish/review
    // path is the order-sensitive mechanism.
    if std::env::var_os("KM_BRIDGE_NO_BLOCKING").is_some() {
        return;
    }
    algo.conf_optimized_sub_set_blocking = true;
    algo.conf_anywhere_blocking_linked_candidate_hash_search = true;
    algo.conf_anywhere_blocking_lazy_exact_hashing = true;
    algo.conf_save_core_blocking_concepts_candidates = true;
    // Konclude's production default. The generic u20 backend-association path
    // remains fail-closed; the native ABox bridge activates this only after
    // its explicit representative-cache predicate and concept-sync test.
    algo.conf_allow_backend_successor_expansion_blocking = true;
    algo.conf_allow_backend_neighbour_expansion_blocking = true;
    // Decline the cache-backed selective neighbour expansion per NEIGHBOUR VALUE,
    // never per NODE: one unjustifiable neighbour value must not drop the whole
    // node's association block and raw-replay both assertion chains. See
    // `conf_native_selective_neighbour_per_value_decline`.
    algo.conf_native_selective_neighbour_per_value_decline = true;
}

/// Seed `concept` onto `root`'s concept-processing queue at the immediate
/// priority (8) — the classify_test `seed_concept_on_queue`.
fn seed_concept_on_queue(
    ctx: &mut CalculationAlgorithmContextBase,
    root: NodeId,
    concept: ConceptId,
) {
    // TBox seeds carry the INDEPENDENT base dependency track point (Konclude:
    // base assertions are never untracked; an untracked descriptor is a
    // tracking ERROR that aborts the whole clashedBacktracking analysis).
    let base_tp = ctx.get_or_create_base_dependency_track_point();
    let queue = ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let cd = ctx.process_context_mut().con_desc_mut(con_des);
        cd.concept = concept;
        cd.dep_track_point = base_tp;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.priority = ConceptProcessPriority::new(8.0);
    cpd_val.dep_track_point = base_tp;
    let cpd = ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        ctx.process_context_mut(),
    );
}

/// A per-probe root/verdict driver over a bridged TBox. `seeds` are the probe
/// concepts (e.g. `[(A, false), (B, true)]` for the `A ⊑ B` unsat test).
/// Returns `Some(true)` iff the probe is UNSATISFIABLE (a genuine Clash),
/// `Some(false)` iff a saturated fixpoint was reached with no clash, and
/// `None` if the drive raised a STOP (e.g. the iteration safety cap) — an
/// UNKNOWN verdict a caller must never fold into either answer.
///
/// Mirrors `classify_test::is_unsatisfiable`: re-seeds the TBox implications
/// each pass (the stand-in for the unported condensed reapply queue) and
/// breaks only on a stable concept count with NO disjunction backtrack in the
/// pass (see `or_backtrack_count`).
pub fn bridged_unsat(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    seeds: &[(ConceptId, bool)],
) -> Option<bool> {
    ctx.clear_pending_signal();
    algo.or_branch_stack.clear();
    algo.completeness_poisoned = false;

    // fresh root node (the classify_test `make_root`)
    let id = *next_indi_id;
    *next_indi_id += 1;
    let next_reserved = ctx
        .processing_data_box_mut()
        .next_individual_node_id(false)
        .max(id.saturating_add(1));
    ctx.processing_data_box_mut()
        .set_first_possible_individual_node_id(next_reserved);
    let mut root = ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    ctx.process_context_mut()
        .node_mut(root)
        .set_individual_node_id(id);
    ctx.processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(id, root);

    // Probe seeds are BASE assertions — track them on the independent base
    // dependency (a NONE would read as an unported rule path downstream).
    let seed_tp = ctx.get_or_create_base_dependency_track_point();
    // KONCLUDE-PORT-NOTE[root-top]: see `bridged_classify_subject` — every node
    // carries ⊤ in Konclude; a bare root swallowed derived ⊥ (¬⊤ met no ⊤).
    let top = ctx.processing_data_box().ontology_top_concept;
    if top.is_some() && std::env::var_os("KM_HT_NO_ROOT_TOP").is_none() {
        algo.add_concept_to_individual(top, false, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            return Some(true);
        }
    }
    let mut seed_start = 0usize;
    if algo.conf_expand_created_successors_from_saturation {
        if let Some(&(concept, negated)) = seeds.first() {
            if algo.try_initializing_concept_from_saturated_data(
                &mut root, concept, negated, seed_tp, true, ctx,
            ) {
                seed_start = 1;
                if ctx.has_pending_signal() {
                    return Some(true);
                }
            }
        }
    }
    for &(concept, negated) in &seeds[seed_start..] {
        algo.add_concept_to_individual(concept, negated, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                eprintln!("UNSAT-EXIT seed-insert");
            }
            return Some(true);
        }
    }

    // GLOBAL fixpoint on total insertions (see `bridged_classify_subject`):
    // root-label-count-stable is order-dependent and declared a false fixpoint.
    let trace = std::env::var_os("KM_BRIDGE_TRACE").is_some();
    // KM_BRIDGE_PROBE_BUDGET_S: wall-clock budget per probe. On overrun the
    // probe returns None (STOP — an UNKNOWN verdict the caller must treat as
    // a DEFER). A single pathological probe must never wedge a classify run.
    // `algo.probe_budget` (set by `bridged_classify`'s retry rounds) takes
    // precedence over the env so escalation needs no env mutation.
    let budget: Option<std::time::Duration> = algo.probe_budget.or_else(|| {
        std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .map(std::time::Duration::from_secs)
    });
    let probe_t0 = std::time::Instant::now();
    // Thread the deadline INTO the drive loop: one `run_completion_on` call
    // owns the whole backtracking search, so the between-passes check below
    // cannot bound it on its own.
    algo.drive_deadline = budget.map(|b| probe_t0 + b);
    let mut prev_inserts: i64 = -1;
    for pass in 0..256 {
        if let Some(b) = budget {
            if probe_t0.elapsed() > b {
                return None;
            }
        }
        for &g in &bridged.tbox {
            seed_concept_on_queue(ctx, root, g);
        }
        // Plain-mode completeness repair: reprocess every label concept each
        // pass, so the insertion-stable break below certifies genuine closure
        // under ALL rules (see `requeue_all_node_labels`).
        algo.requeue_all_node_labels(ctx);
        let iq = ctx.get_individual_immediately_processing_queue(true);
        ctx.process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
        let backtracks_before = algo.or_backtrack_count;
        let consistent = algo.run_completion_on(ctx);
        if trace {
            eprintln!(
                "TRACE pass={pass} consistent={consistent} inserts={} backtracks={} nodes={}",
                algo.stat_con_des_insertion_count,
                algo.or_backtrack_count,
                ctx.process_context().node_count(),
            );
        }
        if !consistent {
            // A Clash is a genuine UNSAT; a Stop (iteration cap / task fork)
            // is an UNKNOWN — folding it into unsat would be UNSOUND, folding
            // it into sat would be INCOMPLETE.
            if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                eprintln!(
                    "UNSAT-EXIT pass={pass} signal={:?}",
                    matches!(
                        ctx.pending_signal(),
                        super::completion::clash::CalcSignal::Clash(_)
                    )
                );
            }
            return match ctx.pending_signal() {
                super::completion::clash::CalcSignal::Clash(clash) => {
                    if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                        eprintln!(
                            "UNSAT-EXIT probe-clash: ddb={} cow={} root_cancelled={} backtracks={} dumps_used={}",
                            algo.conf_dependency_backjumping,
                            algo.conf_inprocess_cow,
                            algo.ddb_root_cancelled,
                            algo.or_backtrack_count,
                            algo.ddb_analysis_dumps
                        );
                    }
                    if trace {
                        // walk the clash descriptor chain: which concepts on
                        // which nodes clashed (diff a clash run vs a SAT run).
                        let mut c = clash;
                        while c.is_some() {
                            let d = ctx.process_context().clash_desc(c);
                            let next = d.next;
                            if let super::process::descriptor::ClashDescriptorKind::Concept {
                                concept_descriptor,
                                individual_node,
                            } = &d.kind
                            {
                                let concept_descriptor = *concept_descriptor;
                                let individual_node = *individual_node;
                                let (tag, neg, node_id) = {
                                    let pc = ctx.process_context();
                                    let con = if concept_descriptor.is_some() {
                                        pc.con_desc(concept_descriptor).get_concept()
                                    } else {
                                        Id::NONE
                                    };
                                    (
                                        if con.is_some() {
                                            ctx.ontology_arenas().concept(con).get_concept_tag()
                                        } else {
                                            -1
                                        },
                                        concept_descriptor.is_some()
                                            && pc.con_desc(concept_descriptor).is_negated(),
                                        if individual_node.is_some() {
                                            pc.node(individual_node).individual_node_id()
                                        } else {
                                            -1
                                        },
                                    )
                                };
                                eprintln!("TRACE CLASH concept tag={tag} neg={neg} node={node_id}");
                                // full label of the clash node: which class was
                                // wrongly pushed is usually visible here (its
                                // disjointness supplies the negation).
                                if individual_node.is_some() {
                                    let ls = ctx
                                        .process_context_mut()
                                        .node_reapply_concept_label_set(individual_node);
                                    let mut parts: Vec<String> = ctx
                                        .process_context()
                                        .label_set(ls)
                                        .concept_des_dep_map
                                        .iter()
                                        .map(|(t, data)| {
                                            let n = if data.concept_descriptor.is_some()
                                                && ctx
                                                    .process_context()
                                                    .con_desc(data.concept_descriptor)
                                                    .is_negated()
                                            {
                                                "¬"
                                            } else {
                                                ""
                                            };
                                            format!("{n}{t}")
                                        })
                                        .collect();
                                    parts.sort();
                                    eprintln!("TRACE CLASH-NODE-LABEL {}", parts.join(" "));
                                }
                            } else {
                                use super::process::descriptor::ClashDescriptorKind as K;
                                match &d.kind {
                                    K::Dependency => eprintln!("TRACE CLASH dependency"),
                                    K::IndividualLink { link_edge } => {
                                        let pc = ctx.process_context();
                                        let (s, t, r) = if link_edge.is_some() {
                                            let e = pc.edge(*link_edge);
                                            (
                                                pc.node(e.get_source_individual())
                                                    .individual_node_id(),
                                                pc.node(e.get_destination_individual())
                                                    .individual_node_id(),
                                                e.get_link_role().index() as i64,
                                            )
                                        } else {
                                            (-1, -1, -1)
                                        };
                                        eprintln!("TRACE CLASH link {s}--role{r}-->{t}");
                                    }
                                    K::IndividualDistinct { distinct_edge } => {
                                        let pc = ctx.process_context();
                                        let (s, t) = if distinct_edge.is_some() {
                                            let e = pc.distinct_edge(*distinct_edge);
                                            (
                                                pc.node(e.source).individual_node_id(),
                                                pc.node(e.destination).individual_node_id(),
                                            )
                                        } else {
                                            (-1, -1)
                                        };
                                        eprintln!("TRACE CLASH distinct {s} != {t}");
                                    }
                                    _ => eprintln!("TRACE CLASH other-kind"),
                                }
                            }
                            c = next;
                        }
                    }
                    Some(true)
                }
                _ => None,
            };
        }
        let inserts = algo.stat_con_des_insertion_count;
        if inserts == prev_inserts && algo.or_backtrack_count == backtracks_before {
            break;
        }
        prev_inserts = inserts;
    }
    if trace {
        // Dump the final root label (sorted tags) so a SAT run can be diffed
        // against a clash run of the same probe.
        let ls = ctx
            .process_context_mut()
            .node_reapply_concept_label_set(root);
        let mut tags: Vec<(Cint64, bool)> = ctx
            .process_context()
            .label_set(ls)
            .concept_des_dep_map
            .iter()
            .filter_map(|(tag, data)| {
                let cd = data.concept_descriptor;
                if cd.is_none() {
                    return None;
                }
                Some((*tag, ctx.process_context().con_desc(cd).is_negated()))
            })
            .collect();
        tags.sort_unstable();
        eprintln!("TRACE root-label {tags:?}");

        // BLOCKING INVARIANT: at a claimed fixpoint every DIRECTBLOCKED node's
        // label must still be a SUBSET of its blocker's label (subset blocking).
        // A violation = the retest-on-modification chain failed for that node —
        // the order-dependent false-model mechanism.
        // Walk CURRENT nodes via the id→node vector (raw arena slots include
        // stale pre-localization copies whose old flags would false-positive).
        let max_id = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_max_index();
        let mut blocked_count = 0usize;
        for indi_id in 0..=max_id.max(-1) {
            let nid = ctx
                .processing_data_box()
                .individual_process_node_vector()
                .get_data(indi_id);
            if nid.is_none() {
                continue;
            }
            let nid_idx = nid.index();
            let node = ctx.process_context().node(nid);
            if !node
                .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED)
            {
                continue;
            }
            blocked_count += 1;
            let blocker_raw = node.blocker_individual_node();
            let bls = node.use_reapply_con_label_set;
            if blocker_raw.is_none() || bls.is_none() {
                eprintln!("TRACE BLOCKVIOLATION node={nid_idx} blocker=NONE");
                continue;
            }
            // map the (possibly stale pre-localization) blocker NodeId to the
            // CURRENT node for its individual id.
            let blocker = {
                let blocker_id = ctx.process_context().node(blocker_raw).individual_node_id();
                let cur = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(blocker_id);
                if cur.is_some() {
                    cur
                } else {
                    blocker_raw
                }
            };
            let blocker_ls = ctx
                .process_context()
                .node(blocker)
                .use_reapply_con_label_set;
            if blocker_ls.is_none() {
                eprintln!("TRACE BLOCKVIOLATION node={nid_idx} blocker-label=NONE");
                continue;
            }
            let pc = ctx.process_context();
            let mut missing: Vec<(Cint64, bool)> = Vec::new();
            for (tag, data) in pc.label_set(bls).concept_des_dep_map.iter() {
                let cd = data.concept_descriptor;
                if cd.is_none() {
                    continue;
                }
                let neg = pc.con_desc(cd).is_negated();
                // by-tag probe (the map IS keyed by real concept tags) + explicit
                // polarity compare — ls1::has_concept is a W2-DEFER stub (raw-index
                // key + always-false negation) and must not be used here.
                let present = pc
                    .label_set(blocker_ls)
                    .concept_des_dep_map
                    .get(tag)
                    .map_or(false, |d| {
                        d.concept_descriptor.is_some()
                            && pc.con_desc(d.concept_descriptor).is_negated() == neg
                    });
                if !present {
                    missing.push((*tag, neg));
                }
            }
            if !missing.is_empty() {
                missing.sort_unstable();
                eprintln!(
                    "TRACE BLOCKVIOLATION node={nid_idx} blocker={} missing={missing:?}",
                    blocker.index()
                );
            }
        }
        eprintln!("TRACE blocked-nodes={blocked_count}");

        // KM_BRIDGE_DUMP_EDGES=<indi>[,<indi>...]: dump the outgoing edges of
        // the listed CURRENT nodes (role tag, destination id, ghost status).
        if let Some(spec) = std::env::var_os("KM_BRIDGE_DUMP_EDGES") {
            let ids: Vec<Cint64> = spec
                .to_string_lossy()
                .split(',')
                .filter_map(|s| s.trim().parse().ok())
                .collect();
            for indi_id in ids {
                let nid = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(indi_id);
                if nid.is_none() {
                    eprintln!("TRACE EDGES indi={indi_id} <no node>");
                    continue;
                }
                let pc = ctx.process_context();
                let mut it = pc.node_successor_iterator(nid);
                while it.has_next() {
                    let link = it.next_link(false);
                    let succ_id = it.next_individual_id(true);
                    if link.is_none() {
                        continue;
                    }
                    let role_tag = {
                        let r = pc.edge(link).get_link_role();
                        if r.is_some() {
                            ctx.ontology_arenas().role(r).get_role_tag()
                        } else {
                            -1
                        }
                    };
                    let succ = ctx
                        .processing_data_box()
                        .individual_process_node_vector()
                        .get_data(succ_id);
                    let ghost = succ.is_some() && {
                        let n = pc.node(succ);
                        n.has_merged_into_individual_node_id()
                            || n.has_purged_blocked_processing_restriction_flags()
                    };
                    eprintln!(
                        "TRACE EDGES indi={indi_id} --role{role_tag}--> {succ_id} ghost={ghost}"
                    );
                }
            }
        }

        // KM_BRIDGE_FIND_TAG=<tag>[,<tag>...]: list every current node whose
        // label carries the tag (either polarity) + its blocking flags — used
        // to locate the clash region of a TRUE run inside a FALSE run's model.
        if let Some(spec) = std::env::var_os("KM_BRIDGE_FIND_TAG") {
            let tags: Vec<Cint64> = spec
                .to_string_lossy()
                .split(',')
                .filter_map(|s| s.trim().parse().ok())
                .collect();
            for indi_id in 0..=max_id.max(-1) {
                let nid = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(indi_id);
                if nid.is_none() {
                    continue;
                }
                let pc = ctx.process_context();
                let node = pc.node(nid);
                let ls = node.use_reapply_con_label_set;
                if ls.is_none() {
                    continue;
                }
                for &t in &tags {
                    if let Some(d) = pc.label_set(ls).concept_des_dep_map.get(&t) {
                        if d.concept_descriptor.is_some() {
                            let neg = pc.con_desc(d.concept_descriptor).is_negated();
                            let flags = node.processing_restriction_flags();
                            let blocked = node.has_partial_processing_restriction_flags(
                                IndividualProcessNode::PRF_DIRECTBLOCKED
                                    | IndividualProcessNode::PRF_INDIRECTBLOCKED
                                    | IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                            );
                            eprintln!(
                                "TRACE FINDTAG tag={t} neg={neg} indi={indi_id} blocked={blocked} flags={flags:#x} label-size={}",
                                pc.label_set(ls).get_concept_count()
                            );
                        }
                    }
                }
            }
        }
    }
    // A clash-free fixpoint after a cross-branch WIPE (see
    // `completeness_poisoned`) is not a model certificate — the graph may be
    // missing branch-independent consequences whose clash would have proved
    // UNSAT. Answer UNKNOWN (defer); clash exits above remain sound.
    if algo.completeness_poisoned {
        return None;
    }
    // Konclude calls `cacheSatisfiableIndividualNodes` at every successful
    // task fixpoint; that routine itself enters when either the signature
    // satisfiable-expander writer or the saturation-node writer is active.
    // The bridge drives completion directly, so it must reproduce the same OR
    // gate before committing both handlers' pending messages.
    if algo.conf_sat_exp_cache_writing
        || algo.conf_saturation_satisfiabilitiy_expansion_cache_writing
    {
        let wrote = algo.cache_satisfiable_individual_nodes(ctx);
        algo.commit_cache_messages(ctx);
        if wrote && std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
            eprintln!("BRIDGE-SAT-EXPANSION-CACHE-WRITE");
        }
    }
    Some(false)
}

/// Model READ-OFF classification of one named concept.
///
/// Saturates `{named[subject]}` on a fresh root and reads the root label's
/// positive NAMED tags as `subject`'s subsumers — O(1) saturation per
/// concept instead of O(concepts) pairwise probes. VALID only when the
/// saturation is deterministic (`or_backtrack_count` unchanged): one
/// canonical model then captures every consequence, so a named concept in
/// the label IS a subsumer (Horn/EL read-off). On a NON-deterministic
/// subject the single branch is not authoritative — the caller must fall
/// back to pairwise `bridged_unsat` probes over the candidate set.
///
/// Returns `Some((subsumer_indices, authoritative))` (indices into
/// `bridged.named`, INCLUDING `subject` itself), `None` if the drive
/// STOPped (no verdict at all). `authoritative = true` ⇔ the saturation made
/// NO nondeterministic choice (no OR branch point opened, no backtrack): the
/// canonical model captures every consequence and the read-off IS the
/// subsumer set. `authoritative = false` ⇔ the label is one branch's model —
/// the positives are CANDIDATE subsumers (Konclude's possible-subsumer
/// extraction) the caller must verify individually via `bridged_unsat`
/// pairwise probes. A clash means the subject is unsatisfiable — every
/// concept subsumes it — reported as the full index range, authoritative.
fn bridged_classify_subject_with_root(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    subject: usize,
    n_named: usize,
) -> Option<(Vec<usize>, bool, NodeId)> {
    ctx.clear_pending_signal();
    algo.or_branch_stack.clear();
    algo.completeness_poisoned = false;
    // KM_BRIDGE_PROBE_BUDGET_S also bounds the READ-OFF search: before the
    // DDB taint fix (2a869e8) heavy subjects' read-offs looked fast only
    // because wrong root-cancels cut them short; the genuine search is
    // unbounded without a deadline (measured: SUBJ PathOfLength3 read-off ran
    // 10 min to 126 GB). On overrun the drive raises a STOP → verdict None →
    // the caller records NO derivations for the subject (sound; shows as
    // missing vs gold, never spurious).
    algo.drive_deadline = algo
        .probe_budget
        .or_else(|| {
            std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
                .ok()
                .and_then(|s| s.parse::<u64>().ok())
                .map(std::time::Duration::from_secs)
        })
        .map(|b| std::time::Instant::now() + b);

    let id = *next_indi_id;
    *next_indi_id += 1;
    let next_reserved = ctx
        .processing_data_box_mut()
        .next_individual_node_id(false)
        .max(id.saturating_add(1));
    ctx.processing_data_box_mut()
        .set_first_possible_individual_node_id(next_reserved);
    let mut root = ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    ctx.process_context_mut()
        .node_mut(root)
        .set_individual_node_id(id);
    ctx.processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(id, root);

    // The subject seed is a BASE assertion — independent base dependency.
    let seed_tp = ctx.get_or_create_base_dependency_track_point();
    // KONCLUDE-PORT-NOTE[root-top]: Konclude's node initialization labels EVERY
    // node with ⊤ (`create_new_individual` does it for successors); bridge roots
    // were created bare, so the bottom rule's faithful ¬⊤ insert (u08) met no ⊤
    // and a derived ⊥ on the ROOT was silently satisfiable — an under-detected
    // unsat (found by the saturation-first oracle tests: A ⊑ B, A ⊓ B ⊑ ⊥ was
    // classified SAT). Labeling the root with ⊤ arms the ⊤/¬⊤ clash pair and,
    // via the CCTOP AND-unfold, delivers the top-attached GCIs exactly like the
    // per-pass re-seed already did (idempotent).
    let top = ctx.processing_data_box().ontology_top_concept;
    if top.is_some() && std::env::var_os("KM_HT_NO_ROOT_TOP").is_none() {
        algo.add_concept_to_individual(top, false, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            return Some(((0..n_named).collect(), true, root));
        }
    }
    let initialized_from_saturation = algo.conf_expand_created_successors_from_saturation
        && algo.try_initializing_concept_from_saturated_data(
            &mut root,
            bridged.named[subject],
            false,
            seed_tp,
            true,
            ctx,
        );
    if !initialized_from_saturation {
        algo.add_concept_to_individual(
            bridged.named[subject],
            false,
            &mut root,
            seed_tp,
            false,
            true,
            ctx,
        );
    }
    if ctx.has_pending_signal() {
        // seed alone clashed ⇒ subject unsatisfiable
        return Some(((0..n_named).collect(), true, root));
    }

    let backtracks_before = algo.or_backtrack_count;
    let branch_opens_before = algo.or_branch_open_count;
    // GLOBAL fixpoint: break only when a full re-drive pass inserts NO concept
    // on ANY node. Breaking on the root-label COUNT (the earlier criterion) is
    // order-dependent — a pass can add nothing to the root while reapply /
    // successor→root propagation is still pending, so it declared a fixpoint
    // at an INCOMPLETE, HashMap-order-dependent closure (identical runs gave
    // different subsumer sets). `stat_con_des_insertion_count` is the total
    // insertions across every node; unchanged over a pass ⇒ true fixpoint.
    let mut prev_inserts: i64 = -1;
    for _ in 0..256 {
        for &g in &bridged.tbox {
            seed_concept_on_queue(ctx, root, g);
        }
        // Plain-mode completeness repair: reprocess every label concept each
        // pass, so the insertion-stable break below certifies genuine closure
        // under ALL rules (see `requeue_all_node_labels`).
        if !bridged.source_tbox {
            algo.requeue_all_node_labels(ctx);
        }
        let iq = ctx.get_individual_immediately_processing_queue(true);
        ctx.process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
        let consistent = algo.run_completion_on(ctx);
        if !consistent {
            return match ctx.pending_signal() {
                super::completion::clash::CalcSignal::Clash(_) => {
                    Some(((0..n_named).collect(), true, root))
                }
                _ => None, // STOP: no verdict
            };
        }
        if bridged.source_tbox {
            break;
        }
        let inserts = algo.stat_con_des_insertion_count;
        if inserts == prev_inserts {
            break;
        }
        prev_inserts = inserts;
    }
    // A cross-branch WIPE (see `completeness_poisoned`) invalidates BOTH
    // read-off directions: the label may miss branch-independent positives
    // (candidate set no longer ⊇ true subsumers) AND absences are no longer
    // countermodels. No usable verdict — defer the subject.
    if algo.completeness_poisoned {
        return None;
    }
    if algo.conf_sat_exp_cache_writing
        || algo.conf_saturation_satisfiabilitiy_expansion_cache_writing
    {
        let wrote = algo.cache_satisfiable_individual_nodes(ctx);
        algo.commit_cache_messages(ctx);
        if wrote && std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
            eprintln!("BRIDGE-SAT-EXPANSION-CACHE-WRITE");
        }
    }
    // Non-deterministic saturation ⇒ single branch is not authoritative.
    // Opened branch points count even without backtracks: a drive committing
    // to first disjuncts pollutes the root label with branch-dependent
    // concepts (measured on ore_ont_3215: 86 SPURIOUS subsumptions under the
    // backtrack-only gate). The read-off still runs — its positives become
    // the CANDIDATE set for pairwise verification.
    let authoritative = algo.or_backtrack_count == backtracks_before
        && algo.or_branch_open_count == branch_opens_before;

    // Read off positive named tags from the root label.
    let ls = ctx
        .process_context_mut()
        .node_reapply_concept_label_set(root);
    let mut subsumers: Vec<usize> = Vec::new();
    let entries: Vec<(Cint64, super::process::ConDescId)> = ctx
        .process_context()
        .label_set(ls)
        .concept_des_dep_map
        .iter()
        .map(|(tag, data)| (*tag, data.concept_descriptor))
        .collect();
    for (tag, cd) in entries {
        if tag < TAG_BASE || tag >= TAG_BASE + n_named as Cint64 {
            continue;
        }
        if cd.is_none() {
            continue;
        }
        if ctx.process_context().con_desc(cd).is_negated() {
            continue;
        }
        subsumers.push((tag - TAG_BASE) as usize);
    }
    subsumers.sort_unstable();
    subsumers.dedup();
    Some((subsumers, authoritative, root))
}

pub fn bridged_classify_subject(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    subject: usize,
    n_named: usize,
) -> Option<(Vec<usize>, bool)> {
    bridged_classify_subject_with_root(algo, ctx, bridged, next_indi_id, subject, n_named)
        .map(|(subsumers, authoritative, _)| (subsumers, authoritative))
}

/// Run Konclude's already-ported classification-message analyser over a
/// completed bridge model and feed the resulting subsumer, possible-subsumer,
/// and pseudo-model messages into the persistent KPSet item.
fn analyse_kpset_completion_model(
    classifier: &mut OptimizedKPSetClassSubsumptionClassifierThread,
    state: &mut SynchronousKPSetClassState,
    subject: usize,
    root: NodeId,
    ctx: &mut CalculationAlgorithmContextBase,
) {
    let analyser = SatisfiableTaskClassificationMessageAnalyser::default();
    let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
        state
            .ontology_item
            .get_concept_satisfiable_test_item_container()[state.item_ids[subject].index()]
        .get_testing_concept(),
        0,
        0,
        state
            .ontology_item
            .get_concept_reference_linking_data_hash()
            .clone(),
        EFEXTRACTALL,
    );
    let individual_vector = ctx
        .processing_data_box()
        .individual_process_node_vector()
        .clone();
    let max_branch_tag = ctx.processing_data_box().maximum_deterministic_branch_tag();
    let mut observer = RecordingClassificationMessageDataObserver::new();
    let testing_items = state
        .ontology_item
        .get_concept_satisfiable_test_item_container();
    // `mEquivConNonCandidateSet` belongs to the live TBox in Konclude. Split
    // the two disjoint context fields so the analyser can update completion
    // bookkeeping while reading that ontology-owned set.
    let base = &mut ctx.base;
    let process_context = &mut base.used_process_context;
    let ontology = &base.ontology_arenas;
    let analysed = analyser.analyse_satisfiable_task_classification_messages_with_live_other_nodes_and_live_equivalent_non_candidates(
        &adapter,
        process_context,
        ontology,
        root,
        &individual_vector,
        max_branch_tag,
        ontology.concepts(),
        ontology.concept_process_datas(),
        ontology.concept_saturation_reference_linking_datas(),
        ontology.saturation_concept_reference_linkings(),
        testing_items,
        ontology.roles(),
        false,
        0,
        Some(&mut observer),
    );
    let Some(analysed) = analysed else { return };
    if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
        let message_count: usize = observer
            .get_told_messages()
            .iter()
            .map(|(_, messages, _)| messages.len())
            .sum();
        eprintln!(
            "BRIDGE-KPSET-MESSAGES subject {subject}: visits={} messages={message_count}",
            analysed.other_node_visit_count,
        );
    }
    for (_, messages, _) in observer.get_told_messages() {
        classifier.process_classification_message_data_linker(
            &mut state.ontology_item,
            messages,
            ontology.concepts(),
        );
    }
}

/// The production classification result: index pairs into `TInput.concepts`.
pub struct BridgedClassification {
    /// False only when the exact nominal/ABox consistency task clashes.
    pub consistent: bool,
    /// Indices of unsatisfiable named concepts.
    pub unsatisfiable: Vec<usize>,
    /// `(sub, sup)` subsumption pairs (self-pairs excluded).
    pub subsumptions: Vec<(usize, usize)>,
}

/// Fresh per-subject probe environment: algorithm + context + bridged
/// terminology. Konclude isolates probes via per-task databox COW (the
/// unported Task layer); the v1 driver rebuilds — same verdicts, O(TBox)
/// per subject/probe.
/// Install a live `CUnsatisfiableCacheHandler` (occurrence unsat cache +
/// reader/writer) into the probe context — the store `KM_HT_UNSATCACHE`'s
/// write/read paths use. One cache per bridge env; `reset_probe_env` carries
/// it across probe resets so nogoods learned in probe k prune probe k+1
/// (Konclude shares the cache across ALL tests of an ontology).
fn install_bridge_unsat_cache(ctx: &mut CalculationAlgorithmContextBase) {
    use super::cache::context::CacheContext;
    use super::cache::unsat::OccurrenceUnsatisfiableCache;
    use super::completion::unsat_handler::UnsatisfiableCacheHandler;
    let mut cache_context = CacheContext::new();
    // KONCLUDE-PORT-NOTE[slots]: Konclude sizes the write-slot ring as
    // `workControllerCount + 2` (CExperimentalReasonerManager cpp 58). With
    // ONE slot the ring deadlocks after the first write: the activation pins
    // the slot through the reader's next-pointer, and the release needs a
    // SECOND slot to displace it — `wait_cache_write_prepared` then spins
    // forever (measured: the tiny warm-probes test hung at 100% CPU). The
    // bridge is single-threaded ⇒ 1 worker + 2 = 3.
    let cache = cache_context.alloc_unsat_cache(OccurrenceUnsatisfiableCache::new(3, "", 0));
    {
        let CacheContext {
            unsat_caches,
            unsat_cache_entries,
            unsat_cache_update_slot_items,
            ..
        } = &mut cache_context;
        unsat_caches
            .get_mut(cache)
            .thread_started(unsat_cache_entries, unsat_cache_update_slot_items);
    }
    let reader = {
        let CacheContext {
            unsat_caches,
            unsat_cache_readers,
            ..
        } = &mut cache_context;
        unsat_caches
            .get_mut(cache)
            .get_cache_reader(cache, unsat_cache_readers)
    };
    let writer = {
        let CacheContext {
            unsat_caches,
            unsat_cache_writers,
            ..
        } = &mut cache_context;
        unsat_caches
            .get_mut(cache)
            .get_cache_writer(cache, unsat_cache_writers)
    };
    ctx.base.install_used_unsatisfiable_cache_handler(
        UnsatisfiableCacheHandler::new(reader, writer),
        cache_context,
    );
}

/// Install Konclude's ontology-wide saturation-node associated-expansion
/// cache. Successful classification jobs extend this cache; later roots and
/// successors replay its deterministic expansions before tableau search.
fn install_bridge_saturation_node_expansion_cache(ctx: &mut CalculationAlgorithmContextBase) {
    use super::cache::context::CacheContext;
    use super::cache::satnode::{
        SaturationNodeAssociatedExpansionCache, SaturationNodeAssociatedExpansionCacheWriter,
    };
    use super::completion::sat_node_exp_handler::SaturationNodeExpansionCacheHandler;
    use super::model::substrate::Id;

    let mut cache_context = CacheContext::new();
    let cache =
        cache_context.alloc_sat_expansion_cache(SaturationNodeAssociatedExpansionCache::new());
    let writer = SaturationNodeAssociatedExpansionCacheWriter::new(cache);
    let handler = SaturationNodeExpansionCacheHandler::new(Id::NONE, writer);
    ctx.install_used_saturation_node_expansion_cache_handler(handler, cache_context);
}

/// Install Konclude's ontology-wide signature satisfiable-expander cache. Its
/// reader/writer state is shared by every classification job and survives the
/// bridge's per-probe databox reset, exactly like the reasoner-manager cache in
/// Konclude.
fn install_bridge_satisfiable_expander_cache(ctx: &mut CalculationAlgorithmContextBase) {
    use super::completion::stubs::SatisfiableExpanderCacheHandler;
    ctx.install_used_satisfiable_expander_cache_handler(SatisfiableExpanderCacheHandler::new());
}

fn log_bridge_satisfiable_expander_cache_stats(
    ctx: &CalculationAlgorithmContextBase,
    phase: &str,
    subject: usize,
) {
    if std::env::var_os("KM_HT_SATEXP_STATS").is_none() {
        return;
    }
    if let Some(state) = ctx.base.used_sat_exp_cache_handler_state.as_ref() {
        let handler = &state.handler;
        let mut direct_cached = 0usize;
        let mut ancestor_cached = 0usize;
        for index in 0..ctx.process_context().node_count() {
            let node = ctx.process_context().node(NodeId::new(index as Cint64));
            direct_cached += usize::from(node.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SATISFIABLECACHED,
            ));
            ancestor_cached += usize::from(node.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED,
            ));
        }
        eprintln!(
            "SATEXP-STATS phase={phase} subject={subject} entries={} read={}/{}/{} sat={} sat-compat={}/{}/{} cached-nodes={}/{} write-requests={}/{} writes={}/{} commits={}",
            handler.cache.sig_item_hash.len(),
            handler.stat_retrieval_requests,
            handler.stat_signature_hits,
            handler.stat_compatible_hits,
            handler.stat_satisfiable_hits,
            handler.stat_satisfiable_compatibility_tests,
            handler.stat_compatible_satisfiable_hits,
            handler.stat_incompatible_satisfiable_hits,
            direct_cached,
            ancestor_cached,
            handler.stat_expansion_write_requests,
            handler.stat_satisfiable_write_requests,
            handler.stat_expansion_writes,
            handler.stat_satisfiable_writes,
            handler.stat_commit_batches,
        );
    }
}

fn fresh_bridge_env(
    tin: &TInput,
) -> (
    CompletionTaskHandleAlgorithm,
    CalculationAlgorithmContextBase,
    Bridged,
) {
    fresh_bridge_env_with_trigger_absorption(tin, std::env::var_os("KM_TRIGGER_ABSORB").is_some())
}

fn fresh_bridge_env_with_trigger_absorption(
    tin: &TInput,
    trigger_absorb: bool,
) -> (
    CompletionTaskHandleAlgorithm,
    CalculationAlgorithmContextBase,
    Bridged,
) {
    use super::completion::strategy::ConceptProcessingPriorityStrategy;
    let mut algo = CompletionTaskHandleAlgorithm::new();
    configure_default_blocking(&mut algo);
    let mut ctx = CalculationAlgorithmContextBase::new();
    ctx.base.used_concept_priority_strategy =
        Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
    if std::env::var_os("KM_HT_UNSATCACHE").is_some() {
        install_bridge_unsat_cache(&mut ctx);
    }
    let top = {
        let mut c = Concept::new();
        c.set_concept_tag(1);
        c.set_operator_code(op::CCTOP);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };
    ctx.processing_data_box_mut().ontology_top_concept = top;
    let bridged = bridge_tinput_with_trigger_absorption(&mut ctx, tin, trigger_absorb);
    algo.singleton_concepts = bridged.singleton_concepts.clone();
    // `CCalculationConfigurationExtension` enables direct rule preprocessing
    // in Konclude's production completion tasks. In particular, a freshly
    // added OR is immediately lowered from priority 13 to the delayed queue
    // before a task fork snapshots the processing queue. The bridge bypasses
    // `readCalculationConfig`, so install that exact scheduling profile for
    // the native cardinality+ABox route that needs representative tasks.
    //
    // Keep the accompanying cache-oriented alternative learning on the same
    // semantic profile. Nominal-only 10621 and cardinality-only 7914 retain
    // their validated legacy scheduling.
    let card_nominal_profile = native_cardinality_abox_profile(tin, bridged.has_native_nominals());
    let independent_abox_elided =
        independent_large_abox_profile(tin, bridged.has_native_nominals());
    algo.conf_direct_rule_preprocessing = card_nominal_profile;
    algo.conf_cache_oriented_or_ordering = card_nominal_profile;
    if card_nominal_profile {
        // Konclude's null-configuration production defaults allow eager
        // preprocessing to recurse through 300 nested rule applications. A
        // zero limit only preprocesses the first descriptor and then silently
        // falls back to ordinary queueing for every conclusion it produces.
        algo.current_rec_proc_depth_limit = 300;
        algo.conf_atomic_semantic_branching = true;
        // This is also Konclude's production dependency profile. The
        // cardinality+ABox route has complete branch epochs and now preserves
        // the real dependencies of failed nominal merges, so dependency-
        // directed backtracking can safely skip choices absent from a clash.
        algo.conf_build_dependencies = true;
        algo.conf_dependency_backtracking = true;
        algo.conf_dependency_backjumping = true;
    }
    if bridged.has_native_nominals() && !independent_abox_elided {
        // Forced singleton merges can cross an OR alternative. Full in-process
        // COW is the existing complete restore mechanism for those writes.
        algo.conf_inprocess_cow = true;
        if !initialize_native_nominal_state(&mut algo, &mut ctx, &bridged) {
            ctx.raise_stop(false);
        }
    }
    (algo, ctx, bridged)
}

/// Recreate all ontology individuals in a fresh per-probe process context and
/// seed their exact asserted types. Explicit inequalities are already present
/// as ordinary negative nominal assertions, exactly as in Konclude.
/// Returns false solely for an impossible typed-id/materialization mismatch;
/// semantic clashes remain pending for the consistency drive to decide.
fn initialize_native_nominal_state(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
) -> bool {
    initialize_native_nominal_state_for_tags(algo, ctx, bridged, None)
}

fn install_native_nominal_backend_replay(
    algo: &mut CompletionTaskHandleAlgorithm,
    bridged: &Bridged,
) {
    use super::completion::algorithm::NativeNominalBackendReplay;

    algo.native_nominal_backend_replay.clear();
    // A new association set is a new set of reuse decisions: the per-job
    // one-shot record (`u25::activate_backend_individual_expansion_reuse`) must
    // not carry a decision taken against the previous associations. Every
    // caller that replaces the algorithm wholesale resets it anyway; this covers
    // the callers that only re-install the replay.
    algo.native_reuse_activated_individuals.clear();
    let cache = bridged.native_representative_cache.borrow();
    for seed in &bridged.nominal_seeds {
        let association_entry = cache
            .as_ref()
            .filter(|cache| !cache.association_write_aborted)
            .and_then(|cache| cache.entries.get(&seed.individual_tag));
        // An incomplete association may not yet cover every asserted edge,
        // so its labels cannot drive blocking. The task still consumed that
        // association header and version, however, and writeback must compare
        // against it exactly.
        let replay_entry =
            association_entry.filter(|entry| native_cache_entry_covers_seed(entry, seed));
        let deterministic_cached_concepts = replay_entry
            .and_then(|entry| entry.concept_values.as_ref())
            .into_iter()
            .flatten()
            .filter(|value| value.deterministic)
            .map(|value| (value.concept, value.negated))
            .collect();
        let cached_concept_values = replay_entry
            .and_then(|entry| entry.concept_values.as_ref())
            .into_iter()
            .flatten()
            .map(|value| (value.concept, value.negated, value.deterministic))
            .collect();
        let mut cached_neighbour_roles: Vec<(Cint64, RoleId, bool, bool)> = replay_entry
            .into_iter()
            .flat_map(|entry| entry.neighbour_role_combinations.iter())
            .flat_map(|combination| {
                combination.role_values.iter().flatten().map(move |value| {
                    (
                        combination.neighbour_tag,
                        value.role,
                        value.inversed,
                        value.deterministic,
                    )
                })
            })
            .collect();
        cached_neighbour_roles.sort_unstable_by_key(
            |(neighbour, role, inversed, deterministic)| {
                (*neighbour, role.raw, *inversed, *deterministic)
            },
        );
        algo.native_nominal_backend_replay.insert(
            seed.individual_tag,
            NativeNominalBackendReplay {
                asserted_concepts: seed.assertions.clone(),
                deterministic_cached_concepts,
                cached_concept_values,
                own_nominal_concept: seed.nominal_concept,
                role_assertions: if bridged.direct_native_role_assertions {
                    seed.role_assertions.clone()
                } else {
                    Vec::new()
                },
                cached_neighbour_roles,
                cached_existential_max_cardinalities: replay_entry
                    .map(|entry| entry.existential_max_cardinalities.clone())
                    .unwrap_or_default(),
                cached_at_most_cardinalities: replay_entry
                    .map(|entry| entry.at_most_cardinalities.clone())
                    .unwrap_or_default(),
                completely_propagated: replay_entry
                    .is_some_and(|entry| entry.completely_propagated),
                association_update_id: association_entry.map(|entry| entry.association_update_id),
                expansion_blocking_candidate: replay_entry.is_some_and(|entry| {
                    entry.reusable_for_full_completion()
                        && native_cache_entry_covers_seed(entry, seed)
                }),
                // Konclude's independent-neighbour block requires only a non-null
                // backend association, because its representative cache is
                // authoritative: the association's neighbour-role-set labels are
                // always a superset of the individual's raw assertion linkers, so
                // blocking the raw expansion never loses an edge. The bridge's
                // typed replay record is such a superset exactly when
                // `native_cache_entry_covers_seed` holds (it checks that every
                // asserted edge of the seed occurs in a neighbour-role-set label),
                // so that is the exact equivalent condition here — an association
                // that does NOT cover the seed must keep the raw replay.
                // Completeness, representative-same, deterministic-same identity
                // and concept-sync remain mandatory only for the stronger
                // successor/indirect block above.
                neighbour_expansion_blocking_candidate: replay_entry.is_some(),
                association_present: association_entry.is_some(),
                // The four reuse slots (`hasReuseableElements`, cpp 22711-22735)
                // plus the merge target seed. These are read ONLY by
                // `u25::reuse_individual_backend_expansion`, under the
                // non-deterministic reuse branch track point — never by
                // `replay_native_representative_cache`, which stays
                // deterministic-only at the base dependency.
                cached_nondeterministic_same_individuals: replay_entry
                    .and_then(|entry| entry.nondeterministic_same_individuals.clone())
                    .unwrap_or_default(),
                cached_deterministic_same_individuals: replay_entry
                    .and_then(|entry| entry.deterministic_same_individuals.clone())
                    .unwrap_or_default(),
                cached_nondeterministic_different_individuals: replay_entry
                    .and_then(|entry| entry.nondeterministic_different_individuals.clone())
                    .unwrap_or_default(),
                cached_representative_same_individual_id: replay_entry
                    .and_then(|entry| entry.representative_same_individual_id),
                reuse_replay_representable: replay_entry
                    .is_some_and(NativeAboxRepresentativeEntry::reuse_replay_representable),
                has_reusable_elements: replay_entry
                    .is_some_and(NativeAboxRepresentativeEntry::has_reusable_elements),
            },
        );
    }
}

fn initialize_native_nominal_state_for_tags(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    selected_tags: Option<&HashSet<Cint64>>,
) -> bool {
    if !bridged.has_native_nominals() {
        return true;
    }
    let base_tp = ctx.get_or_create_base_dependency_track_point();
    let top = ctx.processing_data_box().ontology_top_concept();
    for seed in &bridged.nominal_seeds {
        if selected_tags.is_some_and(|tags| !tags.contains(&seed.individual_tag)) {
            continue;
        }
        let mut node = algo.get_up_to_date_individual_by_id(-seed.individual_tag, ctx);
        if node.is_none()
            || ctx.process_context().node(node).nominal_individual() != seed.individual
        {
            return false;
        }
        // Ordinary legacy tasks have no representative-backend adapter.
        // Konclude only consults the association reader for tasks whose
        // generator installed that adapter; applying replay unconditionally
        // made a large legacy ABox scan every association during pristine
        // construction. The retained/full and representative-task paths call
        // `install_native_nominal_backend_replay` before reaching here.
        if algo
            .native_nominal_backend_replay
            .contains_key(&seed.individual_tag)
        {
            if !replay_native_representative_cache(algo, ctx, bridged, seed, node, base_tp) {
                return false;
            }
            if ctx.has_pending_signal() {
                return true;
            }
        }
        // The materializer normally adds the canonical nominal concept; repeat
        // it idempotently so this helper is independent of backend-cache gates.
        algo.add_concept_to_individual(
            seed.nominal_concept,
            false,
            &mut node,
            base_tp,
            true,
            true,
            ctx,
        );
        if ctx.has_pending_signal() {
            return true;
        }
        if top.is_some() {
            algo.add_concept_to_individual(top, false, &mut node, base_tp, false, true, ctx);
            if ctx.has_pending_signal() {
                return true;
            }
        }
        for &(concept, negated) in &seed.assertions {
            algo.add_concept_to_individual(concept, negated, &mut node, base_tp, false, true, ctx);
            if ctx.has_pending_signal() {
                return true;
            }
        }
        // No eager named-edge installation once a replay journal exists: the typed
        // lazy loader (`get_up_to_date_individual_by_id`) already decided, per
        // individual, whether the cached association blocks the raw expansion or
        // whether `materialize_native_role_assertion_vectors` must replay it. This
        // path only covers the FIRST graph, built before any association exists
        // (Konclude's own individual-saturation input), where every named edge is
        // installed because nothing can be cache-backed yet.
        if bridged.direct_native_role_assertions
            && !algo
                .native_nominal_backend_replay
                .contains_key(&seed.individual_tag)
        {
            for &(role, target_tag) in &seed.role_assertions {
                if !algo.install_native_role_assertion_edge(node, role, target_tag, base_tp, ctx) {
                    return false;
                }
                if ctx.has_pending_signal() {
                    return true;
                }
            }
        }
        // Keep the synchronization hook after every asserted/base concept has
        // been inserted, but only for a task that actually carries the
        // representative adapter. Ordinary tasks have no backend association
        // reader upstream and retain the historical initializer.
        if algo
            .native_nominal_backend_replay
            .contains_key(&seed.individual_tag)
        {
            let _ =
                try_establish_native_backend_expansion_blocking(algo, ctx, bridged, seed, node);
        }
    }
    true
}

/// Reset the probe environment to its post-`bridge_tinput` pristine state
/// WITHOUT rebuilding the bridged terminology. Sound because the ontology
/// arenas are READ-ONLY during bridge probes: native nominal individuals are
/// preallocated in the terminology and every process node is recreated below;
/// a missing id makes the route defer instead of allocating a temporary
/// individual. Keeping the arenas and replacing every piece of per-probe state reproduces
/// `fresh_bridge_env`'s output exactly — the arena content is a
/// deterministic function of `tin` alone. This is the v2 stand-in for
/// Konclude's per-task databox COW: O(processing state) per probe instead
/// of O(TBox) (measured ~seconds + hundreds of MB per probe on the 3215
/// family).
fn reset_probe_env(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    preserve_saturation: bool,
) {
    reset_probe_env_impl(algo, ctx, bridged, preserve_saturation, true);
}

/// Recreate one legacy classification calculation task after ontology
/// consistency. The conditional-full profile does not use this reconstruction:
/// it retains the exact successful all-root consistency graph and restores that
/// graph before each class job.
fn reset_classification_probe_env(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    preserve_saturation: bool,
    independent_abox_elided: bool,
) {
    reset_probe_env_impl(
        algo,
        ctx,
        bridged,
        preserve_saturation,
        !independent_abox_elided,
    );
}

/// Reset only calculation-job-local algorithm state while leaving a retained
/// consistency completion graph untouched. The surrounding branch epoch owns
/// exact graph restoration; this mirrors a class task COW-referencing
/// Konclude's deterministic consistency base.
fn reset_classification_algorithm_on_retained_base(
    algo: &mut CompletionTaskHandleAlgorithm,
    bridged: &Bridged,
) {
    let budget = algo.probe_budget;
    let branch_learning = std::mem::take(&mut algo.or_branch_learning_stats);
    let mut fresh = CompletionTaskHandleAlgorithm::new();
    configure_default_blocking(&mut fresh);
    fresh.singleton_concepts = bridged.singleton_concepts.clone();
    fresh.probe_budget = budget;
    fresh.conf_direct_rule_preprocessing = true;
    fresh.conf_cache_oriented_or_ordering = true;
    fresh.conf_dependency_backtracking = algo.conf_dependency_backtracking;
    fresh.conf_dependency_backjumping = algo.conf_dependency_backjumping;
    fresh.conf_build_dependencies = algo.conf_build_dependencies;
    fresh.conf_atomic_semantic_branching = algo.conf_atomic_semantic_branching;
    fresh.current_rec_proc_depth_limit = algo.current_rec_proc_depth_limit;
    fresh.or_branch_learning_stats = branch_learning;
    *algo = fresh;
    install_native_nominal_backend_replay(algo, bridged);
}

/// Restore the retained deterministic consistency base before the next class
/// job, and open that job's own branch epoch on top of it.
///
/// This is the reset side of Konclude's
/// `CSatisfiableCalculationTaskFromCalculationJobGenerator` base continuation:
/// every class job starts from `getDeterministicSatisfiableTask()` — the
/// depth-0 consistency root with all individual processing queues cleared — and
/// from the fresh-node id reserved off the successful leaf. Nothing of the
/// PREVIOUS job may survive into the next one.
///
/// The previous job is rolled back in FULL, not one alternative deep. A
/// satisfiable probe returns with its OR stack still open (the model IS the set
/// of open alternatives); `bridged_unsat` and
/// `bridged_classify_subject_with_root` only `clear()` that stack on entry and
/// [`reset_classification_algorithm_on_retained_base`] replaces the whole
/// algorithm, so nothing else ever pops the branch epochs those alternatives
/// pushed (`u03.rs` under `conf_inprocess_cow`, and the at-most/qualify family
/// in `u08.rs` unconditionally). Popping a single epoch per job leaked one
/// journal level per surviving fork AND restored only the innermost
/// alternative, so from the second job on the search ran on the previous job's
/// committed disjuncts instead of on the retained base. That is what defeats
/// cheap reuse: the ABox roots keep the previous job's
/// `PRF_INVALIDBLOCKINGORCACHING` and cleared backend-synchronisation bits, so
/// neither [`try_establish_native_backend_expansion_blocking`] nor the
/// `native_*_blocked` gates in `u36::get_up_to_date_individual_by_id` can
/// re-establish the neighbour-expansion block, and every later probe falls
/// through to the raw assertion replay of the whole ABox.
///
/// Returns `None` — defer, never a verdict — if the epoch accounting cannot be
/// justified; a state that is not provably the retained base is never reused.
fn restore_retained_classification_base(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    base_databox: &super::process::databox::ProcessingDataBox,
    base_branch_node: super::process::BranchNodeId,
    base_next_id: Cint64,
) -> Option<()> {
    let owned_epoch_count = algo
        .or_branch_stack
        .iter()
        .filter(|branch| branch.own_epoch)
        .count();
    // One base epoch (the class-job epoch opened at the bottom of this
    // function, or at the retained-base snapshot for the first job) plus
    // exactly one per surviving owned alternative.
    if ctx.process_context().branch_epoch_depth() != owned_epoch_count + 1 {
        return None;
    }
    while let Some(branch) = algo.or_branch_stack.pop() {
        if branch.own_epoch {
            ctx.pop_branch_epoch();
        }
    }
    ctx.pop_branch_epoch();
    if ctx.process_context().branch_epoch_depth() != 0 || !algo.or_branch_stack.is_empty() {
        return None;
    }
    // The dependency/branch-tree cursor is watermark-only memory and is NOT
    // journaled, exactly as at the consistency-phase rollback.
    ctx.base.used_branch_tree_node = base_branch_node;
    ctx.branch_tree_node = base_branch_node;
    ctx.clear_pending_signal();
    ctx.push_branch_epoch();
    initialize_retained_classification_databox(ctx, base_databox, base_next_id);
    reset_classification_algorithm_on_retained_base(algo, bridged);
    // Stage-8 read-off watermark. Every node already in the arena belongs to
    // the retained deterministic consistency base; Konclude hands that base to
    // a class task with all individual processing queues cleared, so a branch
    // point opened below this watermark is work its class task never scheduled.
    algo.retained_base_node_count = ctx.process_context().node_count();
    Some(())
}

/// Materialize the class-job databox from the retained consistency parent.
/// DB-1 is the exact port of `initProcessingDataBox(parent)`: it COW-references
/// the individual vector and graph state while clearing inherited processing
/// queues and task-local review sets. Blocking candidate hashes and node-switch
/// history remain inherited because they index the retained graph.
///
/// `parent` is passed explicitly, and is always the databox captured at the
/// retained deterministic consistency base. Konclude derives every class job
/// from `consTaskData->getDeterministicSatisfiableTask()`, never from the
/// preceding class job; reading the live context here instead would chain job
/// N onto job N-1 whenever the branch-epoch rollback is not exact.
fn initialize_retained_classification_databox(
    ctx: &mut CalculationAlgorithmContextBase,
    parent: &super::process::databox::ProcessingDataBox,
    final_leaf_next_id: Cint64,
) {
    use super::process::databox::ProcessingDataBox;

    let mut child = ProcessingDataBox::new();
    child.init_processing_data_box_parent_with_process_context(
        Some(parent),
        ctx.process_context_mut(),
    );
    child.set_first_possible_individual_node_id(final_leaf_next_id);
    child
        .clear_individual_processing_queue()
        .clear_individual_depth_first_processing_queue()
        .clear_individual_immediately_processing_queue()
        .clear_role_assertion_processing_queue()
        .clear_backend_cache_synchronization_processing_queue()
        .clear_backend_direct_influence_expansion_queue()
        .clear_backend_indirect_compatibility_expansion_queue()
        .clear_backend_individual_reuse_expansion_queue()
        .clear_backend_late_individual_neighbour_expansion_queue()
        .clear_backend_individual_neighbour_expansion_queue()
        .clear_delaying_nominal_processing_queue()
        .clear_nominal_caching_loss_reactivation_processing_queue()
        .clear_variable_binding_concept_batch_processing_queue()
        .clear_individual_depth_processing_queue()
        .clear_nominal_deterministic_processing_queue()
        .clear_nominal_processing_queue()
        .clear_incremental_expansion_initializing_processing_queue()
        .clear_incremental_expansion_i_processing_queue()
        .clear_incremental_compatibility_checking_queue()
        .clear_individual_depth_first_deterministic_expansion_processing_queue()
        .clear_individual_depth_deterministic_expansion_preprocessing_queue()
        .clear_blocking_update_review_processing_queue()
        .clear_blocked_reactivation_processing_queue()
        .clear_value_space_triggering_processing_queue()
        .clear_distinct_value_space_satisfiability_checking_queue();
    child
        .clear_early_individual_reactivation_processing_queue()
        .clear_late_individual_reactivation_processing_queue()
        .clear_signature_blocking_review_set()
        .clear_reusing_review_data()
        .clear_delayed_backend_concept_set_label_processing_initialization_queue()
        .clear_backend_neighbour_expansion_queue();
    ctx.base.used_processing_data_box = child;
}

fn reset_probe_env_impl(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    preserve_saturation: bool,
    initialize_all_nominals: bool,
) {
    use super::model::ontology::OntologyArenas;
    // Fresh algorithm: search state (OR stack, DDB marks, blocking caches,
    // deadlines) must not leak between probes. Konclude's per-disjunct
    // ontology statistics are the deliberate exception: representative
    // component tasks teach the later consistency/classification tasks.
    let budget = algo.probe_budget;
    let card_nominal_profile =
        algo.conf_direct_rule_preprocessing && algo.conf_cache_oriented_or_ordering;
    let direct_rule_preprocessing = algo.conf_direct_rule_preprocessing;
    let cache_oriented_or_ordering = algo.conf_cache_oriented_or_ordering;
    let current_rec_proc_depth_limit = algo.current_rec_proc_depth_limit;
    let dependency_backtracking = algo.conf_dependency_backtracking;
    let dependency_backjumping = algo.conf_dependency_backjumping;
    let build_dependencies = algo.conf_build_dependencies;
    let atomic_semantic_branching = algo.conf_atomic_semantic_branching;
    let branch_learning = if card_nominal_profile {
        std::mem::take(&mut algo.or_branch_learning_stats)
    } else {
        HashMap::new()
    };
    let mut a = CompletionTaskHandleAlgorithm::new();
    configure_default_blocking(&mut a);
    a.singleton_concepts = bridged.singleton_concepts.clone();
    a.probe_budget = budget;
    if card_nominal_profile {
        a.conf_direct_rule_preprocessing = direct_rule_preprocessing;
        a.conf_cache_oriented_or_ordering = cache_oriented_or_ordering;
        a.current_rec_proc_depth_limit = current_rec_proc_depth_limit;
        a.conf_dependency_backtracking = dependency_backtracking;
        a.conf_dependency_backjumping = dependency_backjumping;
        a.conf_build_dependencies = build_dependencies;
        a.conf_atomic_semantic_branching = atomic_semantic_branching;
        a.or_branch_learning_stats = branch_learning;
    }
    *algo = a;
    if card_nominal_profile {
        install_native_nominal_backend_replay(algo, bridged);
    }
    // Fresh context EXCEPT the shared read-only terminology: rebuild through
    // the same ctor as `fresh_bridge_env`, then graft the arenas back. This
    // resets EVERY per-probe field (process context, databox, dependency
    // factory ids, epoch stack, pending signal) by construction rather than
    // by enumeration.
    let arenas = std::mem::replace(&mut ctx.base.ontology_arenas, OntologyArenas::new());
    let strategy = ctx.base.used_concept_priority_strategy.take();
    let top = ctx.base.used_processing_data_box.ontology_top_concept;
    // KM_HT_UNSATCACHE: the learned-nogood store DELIBERATELY survives the
    // probe reset (Konclude shares its unsatisfiable cache across all tests
    // of an ontology). Sound: each entry is a label subset validated by the
    // u22 write guards to be unsatisfiable wrt the shared TBox alone, so it
    // prunes any later probe identically. Note the cache write path also
    // stamps caching tags into the ontology arenas' concept process data — a
    // monotone cache-metadata mutation; with the flag OFF the arenas stay
    // read-only and the reset reproduces `fresh_bridge_env` exactly, with it
    // ON later probes are deliberately order-dependent (they prune using
    // earlier probes' nogoods) while verdicts stay sound+complete.
    let unsat_cache = ctx.base.take_used_unsatisfiable_cache_handler();
    let satisfiable_expander_cache = ctx.take_used_satisfiable_expander_cache_handler();
    let sat_node_expansion_cache = ctx.take_used_saturation_node_expansion_cache_handler();
    // KM_HT_SATURATION: the saturation-side arenas DELIBERATELY survive the
    // probe reset when a saturation pass ran on this env — the ontology
    // arenas (kept above) hold concept→saturation reference linkings whose
    // node ids point into these arenas, and the saturation-node coupling
    // (u08/u17/u22, Konclude's expand-from-saturation + caching-blocking)
    // reads them during every probe. Probes never write them, so the carry
    // reproduces Konclude's stable saturation-task pointers. Carried even
    // when the coupling is off (budget-aborted pass) so the linkings never
    // dangle.
    let mut fresh = CalculationAlgorithmContextBase::new();
    if preserve_saturation {
        fresh
            .process_context_mut()
            .adopt_saturation_state_from(ctx.process_context_mut());
    }
    *ctx = fresh;
    ctx.base.ontology_arenas = arenas;
    ctx.base.used_concept_priority_strategy = strategy;
    ctx.base.used_processing_data_box.ontology_top_concept = top;
    if let Some(state) = unsat_cache {
        ctx.base.restore_used_unsatisfiable_cache_handler(state);
    }
    if let Some(state) = satisfiable_expander_cache {
        ctx.restore_used_satisfiable_expander_cache_handler(state);
    }
    if let Some(state) = sat_node_expansion_cache {
        ctx.restore_used_saturation_node_expansion_cache_handler(state);
    }
    if bridged.has_native_nominals() && initialize_all_nominals {
        algo.conf_inprocess_cow = true;
        if !initialize_native_nominal_state(algo, ctx, bridged) {
            ctx.raise_stop(false);
        }
    }
}

/// Production search configuration for `bridged_classify`. KPSet's message
/// analyser distinguishes deterministic subsumers and pseudo-model entries by
/// dependency branch tag, so classifier jobs must build the dependency spine
/// even when dependency-directed backjumping itself remains opt-in.
fn configure_production_search(algo: &mut CompletionTaskHandleAlgorithm) {
    algo.conf_build_dependencies = true;
    if algo.conf_cache_oriented_or_ordering {
        // The representative-batch profile replays learned disjunct
        // priorities. Its alternatives must therefore remain disjoint. Keep
        // the legacy nominal-only and cardinality-only schedules unchanged.
        algo.conf_atomic_semantic_branching = true;
    }
}

/// Konclude's representative-computation scheduler takes only entries whose
/// association is not completely handled. Its default 1500-individual batch
/// multiplied by the 0.005 scheduling factor yields seven roots.
const NATIVE_REPRESENTATIVE_BATCH_SIZE: usize = 7;

fn native_incomplete_abox_seed_batch(
    bridged: &Bridged,
    batch_size: usize,
) -> Option<HashSet<Cint64>> {
    if batch_size == 0 {
        return None;
    }
    let cache = bridged.native_representative_cache.borrow();
    let cache = cache.as_ref()?;
    if cache.association_write_aborted
        || !bridged
            .nominal_seeds
            .iter()
            .all(|seed| cache.entries.contains_key(&seed.individual_tag))
    {
        return None;
    }
    let mut incomplete: Vec<Cint64> = bridged
        .nominal_seeds
        .iter()
        .filter_map(|seed| {
            cache
                .entries
                .get(&seed.individual_tag)
                .filter(|entry| !entry.complete_for_precomputation())
                .map(|_| seed.individual_tag)
        })
        .collect();
    incomplete.sort_unstable();
    incomplete.truncate(batch_size);
    Some(incomplete.into_iter().collect())
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct NativeRepresentativeCoordinationState {
    running_tasks: usize,
    failed_tasks: usize,
    writeback_failed: bool,
    clashed: bool,
}

fn native_representative_coordination_complete(
    bridged: &Bridged,
    coordination: NativeRepresentativeCoordinationState,
) -> bool {
    if coordination.running_tasks != 0
        || coordination.failed_tasks != 0
        || coordination.writeback_failed
        || coordination.clashed
    {
        return false;
    }
    let cache = bridged.native_representative_cache.borrow();
    cache.as_ref().is_some_and(|cache| {
        !cache.association_write_aborted
            && bridged.nominal_seeds.iter().all(|seed| {
                cache
                    .entries
                    .get(&seed.individual_tag)
                    .is_some_and(NativeAboxRepresentativeEntry::complete_for_precomputation)
            })
    })
}

fn native_completion_dependency_is_deterministic(
    ctx: &CalculationAlgorithmContextBase,
    dependency_track_point: super::process::TrackPointId,
) -> bool {
    dependency_track_point.is_some()
        && ctx
            .process_context()
            .track_point(dependency_track_point)
            .get_branching_tag()
            <= ctx.processing_data_box().maximum_deterministic_branch_tag()
}

fn native_completion_merge_target(
    ctx: &CalculationAlgorithmContextBase,
    mut node: NodeId,
    deterministic_only: bool,
) -> Option<NodeId> {
    let mut walked = 0usize;
    while node.is_some()
        && node.index() < ctx.process_context().node_count()
        && ctx
            .process_context()
            .node(node)
            .has_merged_into_individual_node_id()
    {
        if walked > ctx.process_context().node_count() {
            return None;
        }
        let node_ref = ctx.process_context().node(node);
        if deterministic_only
            && !native_completion_dependency_is_deterministic(
                ctx,
                node_ref.merged_dependency_track_point(),
            )
        {
            break;
        }
        node = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(node_ref.merged_into_individual_node_id());
        walked += 1;
    }
    (node.is_some() && node.index() < ctx.process_context().node_count()).then_some(node)
}

fn native_completion_nominal_tag(
    ctx: &CalculationAlgorithmContextBase,
    node: NodeId,
) -> Option<Cint64> {
    if node.is_none() || node.index() >= ctx.process_context().node_count() {
        return None;
    }
    let individual = ctx.process_context().node(node).nominal_individual();
    if individual.is_none()
        || individual.index() >= ctx.ontology_arenas().individual_count() as usize
    {
        return None;
    }
    Some(
        ctx.ontology_arenas()
            .individual(individual)
            .get_individual_id(),
    )
}

/// Return the process node stored for one ontology individual only when the
/// vector slot still denotes that exact individual. Individual tag zero uses
/// key zero (`-0 == 0`), which is also in the generated-node half of
/// Konclude's double-dynamic vector. Sparse representative tasks can therefore
/// expose an unrelated generated node in the unmaterialized tag-zero slot.
/// Such a node is not a touched backend association.
fn native_exact_nominal_process_node(
    ctx: &CalculationAlgorithmContextBase,
    individual_tag: Cint64,
) -> Option<NodeId> {
    let node = ctx
        .processing_data_box()
        .individual_process_node_vector()
        .get_data(-individual_tag);
    (node.is_some()
        && node.index() < ctx.process_context().node_count()
        && native_completion_nominal_tag(ctx, node) == Some(individual_tag))
        .then_some(node)
}

/// Exact value set produced by
/// `determineSameIndividualSetLabelAssociationBackendItem`. With a merging
/// hash, Konclude includes the representative itself and either deterministic
/// merged members or all merged members. KM's merge primitive preserves the
/// same information as `merged_into + dependency` on every original node but
/// does not yet populate Konclude's phase-6 survivor merging hash. Therefore
/// the current nominal vector is also scanned and the exact merge-chain
/// equivalence class is unioned with any live hash values.
fn native_completion_same_individuals(
    ctx: &CalculationAlgorithmContextBase,
    node: NodeId,
    deterministic_only: bool,
) -> Option<Vec<Cint64>> {
    let own_tag = native_completion_nominal_tag(ctx, node)?;
    let merging_hash = ctx.process_context().node(node).use_individual_merging_hash;
    let mut values = vec![own_tag];
    if merging_hash.is_some() {
        for (&individual_tag, data) in ctx
            .process_context()
            .individual_merging_hash(merging_hash)
            .iter()
        {
            if individual_tag < 0
                || individual_tag == own_tag
                || !data.is_merged_with_individual()
                || (deterministic_only
                    && !native_completion_dependency_is_deterministic(
                        ctx,
                        data.get_dependency_track_point(),
                    ))
            {
                continue;
            }
            values.push(individual_tag);
        }
    }
    for individual in ctx.ontology_arenas().individual_iter() {
        let individual_tag = individual.get_individual_id();
        if individual_tag < 0 {
            return None;
        }
        let Some(original) = native_exact_nominal_process_node(ctx, individual_tag) else {
            continue;
        };
        let representative = native_completion_merge_target(ctx, original, deterministic_only)?;
        if representative == node {
            values.push(individual_tag);
        }
    }
    values.sort_unstable();
    values.dedup();
    if values.len() > 1 {
        Some(values)
    } else {
        // Konclude does not install a SAME-INDIVIDUAL-SET label for a
        // singleton association.
        Some(Vec::new())
    }
}

fn native_completion_label_values(
    ctx: &CalculationAlgorithmContextBase,
    extraction_node: NodeId,
    deterministic_node: NodeId,
) -> Option<(Vec<NativeAboxConceptValue>, usize)> {
    let label = ctx
        .process_context()
        .node(extraction_node)
        .reapply_con_label_set;
    if label.is_none() {
        return None;
    }
    let deterministic_label = ctx
        .process_context()
        .node(deterministic_node)
        .reapply_con_label_set;
    if deterministic_label.is_none() {
        return None;
    }
    let deterministic_membership = |concept: ConceptId, negated: bool| {
        let tag = ctx.ontology_arenas().concept(concept).get_concept_tag();
        ctx.process_context()
            .label_set(deterministic_label)
            .concept_des_dep_map
            .get(&tag)
            .filter(|data| data.concept_descriptor.is_some())
            .is_some_and(|data| {
                let descriptor = ctx.process_context().con_desc(data.concept_descriptor);
                descriptor.get_concept() == concept
                    && descriptor.is_negated() == negated
                    && native_completion_dependency_is_deterministic(
                        ctx,
                        descriptor.get_dependency_track_point(),
                    )
            })
    };

    let mut descriptor = ctx
        .process_context()
        .label_set(label)
        .get_adding_sorted_concept_description_linker();
    let mut values = Vec::new();
    let mut descriptor_count = 0usize;
    while descriptor.is_some() {
        if descriptor.index() >= ctx.process_context().con_desc_count()
            || descriptor_count > ctx.process_context().con_desc_count()
        {
            return None;
        }
        let descriptor_ref = ctx.process_context().con_desc(descriptor);
        let concept = descriptor_ref.get_concept();
        let negated = descriptor_ref.is_negated();
        if concept.is_none() || concept.index() >= ctx.ontology_arenas().concept_count() as usize {
            return None;
        }
        let positive_nominal =
            !negated && ctx.ontology_arenas().concept(concept).get_operator_code() == op::CCNOMINAL;
        if !positive_nominal {
            let deterministic = if extraction_node == deterministic_node {
                native_completion_dependency_is_deterministic(
                    ctx,
                    descriptor_ref.get_dependency_track_point(),
                )
            } else {
                deterministic_membership(concept, negated)
            };
            values.push(NativeAboxConceptValue {
                concept,
                negated,
                deterministic,
            });
        }
        descriptor = descriptor_ref.get_next_concept_descriptor();
        descriptor_count += 1;
    }
    values.sort_unstable_by_key(|value| (value.concept.raw, value.negated, value.deterministic));
    values.dedup();
    Some((values, descriptor_count))
}

struct NativeCompletionRoleMetadata {
    instantiated_roles: Vec<RoleId>,
    instantiated_role_values: Vec<NativeAboxRoleValue>,
    existential_roles: Vec<RoleId>,
    existential_role_values: Vec<NativeAboxRoleValue>,
    at_most_cardinalities: Vec<(RoleId, Cint64)>,
    existential_max_cardinalities: Vec<(RoleId, Cint64)>,
    indirect_nominal_connections: Vec<Cint64>,
    neighbour_role_combinations: Vec<NativeAboxNeighbourRoleSet>,
}

fn native_completion_merge_chain_is_deterministic(
    ctx: &CalculationAlgorithmContextBase,
    original: NodeId,
    merged: NodeId,
) -> Option<bool> {
    let final_node = native_completion_merge_target(ctx, original, false)?;
    if final_node != merged {
        return None;
    }
    Some(native_completion_merge_target(ctx, original, true)? == merged)
}

/// Return the nominal ids represented by one completion-graph connection
/// node, together with Konclude's `connIndiDetMerged` bit for each id.
fn native_completion_connection_aliases(
    ctx: &CalculationAlgorithmContextBase,
    connection_node: NodeId,
) -> Option<BTreeMap<Cint64, bool>> {
    let mut aliases = BTreeMap::new();
    aliases.insert(native_completion_nominal_tag(ctx, connection_node)?, true);
    let merging_hash = ctx
        .process_context()
        .node(connection_node)
        .use_individual_merging_hash;
    if merging_hash.is_some() {
        for (&individual_tag, data) in ctx
            .process_context()
            .individual_merging_hash(merging_hash)
            .iter()
        {
            if individual_tag < 0 || !data.is_merged_with_individual() {
                continue;
            }
            let deterministic = native_completion_dependency_is_deterministic(
                ctx,
                data.get_dependency_track_point(),
            );
            aliases
                .entry(individual_tag)
                .and_modify(|current| *current |= deterministic)
                .or_insert(deterministic);
        }
    }
    Some(aliases)
}

fn native_record_completion_neighbour_role(
    instantiated_values: &mut BTreeMap<(Cint64, bool), bool>,
    neighbour_values: &mut BTreeMap<Cint64, BTreeMap<(Cint64, bool), bool>>,
    neighbour_alias_determinism: &mut BTreeMap<Cint64, bool>,
    indirect_nominals: &mut BTreeSet<Cint64>,
    role: RoleId,
    inversed: bool,
    edge_deterministic: bool,
    aliases: &BTreeMap<Cint64, bool>,
) {
    let any_deterministic = aliases
        .values()
        .any(|alias_deterministic| edge_deterministic && *alias_deterministic);
    instantiated_values
        .entry((role.raw, inversed))
        .and_modify(|current| *current |= any_deterministic)
        .or_insert(any_deterministic);
    for (&neighbour_tag, &alias_deterministic) in aliases {
        indirect_nominals.insert(neighbour_tag);
        neighbour_alias_determinism
            .entry(neighbour_tag)
            .and_modify(|current| *current |= alias_deterministic)
            .or_insert(alias_deterministic);
        neighbour_values
            .entry(neighbour_tag)
            .or_default()
            .entry((role.raw, inversed))
            .and_modify(|current| {
                *current |= edge_deterministic && alias_deterministic;
            })
            .or_insert(edge_deterministic && alias_deterministic);
    }
}

fn native_completion_role_metadata(
    ctx: &CalculationAlgorithmContextBase,
    node: NodeId,
    concept_values: &[NativeAboxConceptValue],
    bridged: &Bridged,
    seed: &NominalSeed,
) -> Option<NativeCompletionRoleMetadata> {
    use super::model::op::{
        CCALL, CCAQALL, CCAQSOME, CCATLEAST, CCATMOST, CCSELF, CCSOME, CCVALUE,
    };

    let previous_entry = bridged
        .native_representative_cache
        .borrow()
        .as_ref()
        .and_then(|cache| cache.entries.get(&seed.individual_tag))
        .cloned();
    let mut existential_values: BTreeMap<Cint64, bool> = previous_entry
        .as_ref()
        .and_then(|entry| entry.existential_role_values.as_ref())
        .into_iter()
        .flatten()
        .map(|value| (value.role.raw, value.deterministic))
        .collect();
    let mut existential_max: BTreeMap<Cint64, Cint64> = previous_entry
        .as_ref()
        .into_iter()
        .flat_map(|entry| entry.existential_max_cardinalities.iter())
        .map(|(role, cardinality)| (role.raw, *cardinality))
        .collect();
    let mut at_most: BTreeMap<Cint64, Cint64> = previous_entry
        .as_ref()
        .into_iter()
        .flat_map(|entry| entry.at_most_cardinalities.iter())
        .map(|(role, cardinality)| (role.raw, *cardinality))
        .collect();
    for value in concept_values {
        let concept_ref = ctx.ontology_arenas().concept(value.concept);
        let operator = concept_ref.get_operator_code();
        let role = concept_ref.get_role();
        if role.is_some()
            && ((!value.negated
                && matches!(operator, CCSOME | CCAQSOME | CCVALUE | CCSELF | CCATLEAST))
                || (value.negated && matches!(operator, CCALL | CCAQALL | CCATMOST)))
        {
            existential_values
                .entry(role.raw)
                .and_modify(|deterministic| *deterministic |= value.deterministic)
                .or_insert(value.deterministic);
            let cardinality = if (!value.negated
                && matches!(operator, CCSOME | CCAQSOME | CCVALUE | CCSELF))
                || (value.negated && matches!(operator, CCALL | CCAQALL))
            {
                1
            } else if !value.negated && operator == CCATLEAST {
                concept_ref.get_parameter().max(0)
            } else {
                concept_ref.get_parameter().saturating_add(1).max(0)
            };
            existential_max
                .entry(role.raw)
                .and_modify(|current| *current = (*current).max(cardinality))
                .or_insert(cardinality);
        }
        let bound = if !value.negated && operator == CCATMOST {
            Some(concept_ref.get_parameter())
        } else if value.negated && operator == CCATLEAST {
            Some(concept_ref.get_parameter().saturating_sub(1))
        } else {
            None
        };
        if let (Some(bound), true) = (bound, role.is_some()) {
            at_most
                .entry(role.raw)
                .and_modify(|current| *current = (*current).min(bound))
                .or_insert(bound);
        }
    }

    let mut instantiated_values: BTreeMap<(Cint64, bool), bool> = previous_entry
        .as_ref()
        .and_then(|entry| entry.instantiated_role_values.as_ref())
        .into_iter()
        .flatten()
        .map(|value| ((value.role.raw, value.inversed), value.deterministic))
        .collect();
    let mut neighbour_values: BTreeMap<Cint64, BTreeMap<(Cint64, bool), bool>> =
        BTreeMap::new();
    let mut neighbour_alias_determinism: BTreeMap<Cint64, bool> = BTreeMap::new();
    if let Some(entry) = previous_entry.as_ref() {
        for combination in &entry.neighbour_role_combinations {
            if native_exact_nominal_process_node(ctx, combination.neighbour_tag).is_some() {
                // Konclude reuses the previous neighbour-role-set label only
                // when that neighbour was not collected in the current
                // completion task. A materialized neighbour is touched: its
                // current connection node and merging data replace the old
                // label. In particular, retaining the old deterministic bit
                // here would hide a branch-local at-most merge.
                continue;
            }
            neighbour_alias_determinism.insert(
                combination.neighbour_tag,
                combination.merged_alias_deterministic?,
            );
            let values = combination.role_values.as_ref()?;
            neighbour_values.insert(
                combination.neighbour_tag,
                values
                    .iter()
                    .map(|value| {
                        (
                            (value.role.raw, value.inversed),
                            value.deterministic,
                        )
                    })
                    .collect(),
            );
        }
    }
    let mut indirect_nominals: BTreeSet<Cint64> = previous_entry
        .as_ref()
        .into_iter()
        .flat_map(|entry| entry.indirect_nominal_connections.iter().copied())
        .chain(
            ctx
        .process_context()
        .node_successor_connected_nominals(node)
        .into_iter()
        )
        .collect();
    let mut successor_iterator = ctx.process_context().node_successor_iterator(node);
    while successor_iterator.has_next() {
        let successor_id = successor_iterator.next_individual_id(true);
        let successor = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(successor_id);
        if successor.is_none() || successor.index() >= ctx.process_context().node_count() {
            return None;
        }
        if ctx
            .process_context()
            .node(successor)
            .has_purged_blocked_processing_restriction_flags()
        {
            continue;
        }
        // `determineRoleInstantiatedSetLabelAssociationBackendItems` retains
        // the connection node's original nominal id and then iterates every
        // merged id in its merging hash. Resolving the node first collapses
        // R(a,b), R(a,c) to only one neighbour after an at-most merge and makes
        // the association fail to cover the original ABox assertions.
        let mut neighbour_tags =
            native_completion_connection_aliases(ctx, successor).unwrap_or_default();
        if neighbour_tags.is_empty() {
            let merged = native_completion_merge_target(ctx, successor, false)?;
            if let Some(tag) = native_completion_nominal_tag(ctx, merged) {
                neighbour_tags.insert(tag, false);
            }
        }
        indirect_nominals.extend(neighbour_tags.keys().copied());
        for (&neighbour_tag, &deterministic) in &neighbour_tags {
            neighbour_alias_determinism
                .entry(neighbour_tag)
                .and_modify(|current| *current |= deterministic)
                .or_insert(deterministic);
        }
        let mut role_iterator = ctx
            .process_context()
            .node_successor_role_iterator(node, successor_id);
        while role_iterator.has_next() {
            let edge = role_iterator.next(true);
            if edge.is_none() || edge.index() >= ctx.process_context().edges().len() {
                return None;
            }
            let edge_ref = ctx.process_context().edge(edge);
            let role = edge_ref.get_link_role();
            if role.is_none() || role.index() >= ctx.ontology_arenas().role_count() as usize {
                return None;
            }
            let deterministic = native_completion_dependency_is_deterministic(
                ctx,
                edge_ref.get_dependency_track_point(),
            );
            if neighbour_tags.is_empty() {
                instantiated_values
                    .entry((role.raw, false))
                    .and_modify(|current| *current |= deterministic)
                    .or_insert(deterministic);
            } else {
                native_record_completion_neighbour_role(
                    &mut instantiated_values,
                    &mut neighbour_values,
                    &mut neighbour_alias_determinism,
                    &mut indirect_nominals,
                    role,
                    false,
                    deterministic,
                    &neighbour_tags,
                );
            }
        }
    }

    // `merge_individuals` prunes successor edges from the merged-away node.
    // Konclude does not lose the original ABox connection: its separate
    // connection-successor set and role-assertion dependency chain survive
    // the merge and are consumed by
    // `determineRoleInstantiatedSetLabelAssociationBackendItems`. The Rust
    // process graph has no equivalent connection-successor set, so replay the
    // immutable assertion journal separately from inferred graph edges. For
    // each endpoint, the final representative and every alias in its merging
    // hash are retained; a nondeterministic endpoint merge makes only that
    // moved link contribution nondeterministic.
    for source_seed in &bridged.nominal_seeds {
        let Some(source_original) =
            native_exact_nominal_process_node(ctx, source_seed.individual_tag)
        else {
            // Sparse representative jobs materialize only their selected
            // roots and on-demand neighbours. An absent source cannot have
            // contributed a link to this task graph.
            continue;
        };
        let source_final = native_completion_merge_target(ctx, source_original, false)?;
        let source_merge_deterministic =
            native_completion_merge_chain_is_deterministic(ctx, source_original, source_final)?;
        for &(role, target_tag) in &source_seed.role_assertions {
            let Some(target_original) = native_exact_nominal_process_node(ctx, target_tag) else {
                // A successful backend-neighbour expansion deliberately keeps
                // uninfluenced neighbours unmaterialized. Their canonical
                // neighbour-role label was copied from the consumed
                // association above, exactly as Konclude's writer reuses
                // previous label items when all links were not collected.
                continue;
            };
            let target_final = native_completion_merge_target(ctx, target_original, false)?;
            let target_merge_deterministic =
                native_completion_merge_chain_is_deterministic(ctx, target_original, target_final)?;
            let edge_deterministic = source_merge_deterministic && target_merge_deterministic;
            if source_final == node {
                let mut aliases = native_completion_connection_aliases(ctx, target_final)?;
                aliases
                    .entry(target_tag)
                    .and_modify(|current| *current |= target_merge_deterministic)
                    .or_insert(target_merge_deterministic);
                native_record_completion_neighbour_role(
                    &mut instantiated_values,
                    &mut neighbour_values,
                    &mut neighbour_alias_determinism,
                    &mut indirect_nominals,
                    role,
                    false,
                    edge_deterministic,
                    &aliases,
                );
            }
            if target_final == node {
                let mut aliases = native_completion_connection_aliases(ctx, source_final)?;
                aliases
                    .entry(source_seed.individual_tag)
                    .and_modify(|current| *current |= source_merge_deterministic)
                    .or_insert(source_merge_deterministic);
                native_record_completion_neighbour_role(
                    &mut instantiated_values,
                    &mut neighbour_values,
                    &mut neighbour_alias_determinism,
                    &mut indirect_nominals,
                    role,
                    true,
                    edge_deterministic,
                    &aliases,
                );
            }
        }
    }

    let instantiated_role_values: Vec<NativeAboxRoleValue> = instantiated_values
        .into_iter()
        .map(|((role, inversed), deterministic)| NativeAboxRoleValue {
            role: RoleId::new(role),
            inversed,
            deterministic,
        })
        .collect();
    let instantiated_roles: Vec<RoleId> = instantiated_role_values
        .iter()
        .map(|value| value.role)
        .collect();
    let existential_role_values: Vec<NativeAboxRoleValue> = existential_values
        .into_iter()
        .map(|(role, deterministic)| NativeAboxRoleValue {
            role: RoleId::new(role),
            inversed: false,
            deterministic,
        })
        .collect();
    let existential_roles: Vec<RoleId> = existential_role_values
        .iter()
        .map(|value| value.role)
        .collect();
    let neighbour_role_combinations = neighbour_values
        .into_iter()
        .map(|(neighbour_tag, roles)| {
            let role_values: Vec<NativeAboxRoleValue> = roles
                .into_iter()
                .map(|((role, inversed), deterministic)| NativeAboxRoleValue {
                    role: RoleId::new(role),
                    inversed,
                    deterministic,
                })
                .collect();
            NativeAboxNeighbourRoleSet {
                neighbour_tag,
                roles: role_values
                    .iter()
                    .map(|value| (value.role, value.inversed))
                    .collect(),
                role_values: Some(role_values),
                merged_alias_deterministic: neighbour_alias_determinism
                    .get(&neighbour_tag)
                    .copied(),
            }
        })
        .collect();

    Some(NativeCompletionRoleMetadata {
        instantiated_roles,
        instantiated_role_values,
        existential_roles,
        existential_role_values,
        at_most_cardinalities: at_most
            .into_iter()
            .map(|(role, cardinality)| (RoleId::new(role), cardinality))
            .collect(),
        existential_max_cardinalities: existential_max
            .into_iter()
            .map(|(role, cardinality)| (RoleId::new(role), cardinality))
            .collect(),
        indirect_nominal_connections: indirect_nominals.into_iter().collect(),
        neighbour_role_combinations,
    })
}

fn native_completion_different_individuals(
    ctx: &CalculationAlgorithmContextBase,
    node: NodeId,
    deterministic_only: bool,
    own_tag: Cint64,
) -> Option<Vec<Cint64>> {
    let distinct_hash = ctx.process_context().node_distinct_hash_existing(node);
    if distinct_hash.is_none() {
        return Some(Vec::new());
    }
    let mut iterator = ctx
        .process_context()
        .distinct_hash(distinct_hash)
        .get_distinct_iterator();
    let mut values = Vec::new();
    while iterator.has_next() {
        let (process_id, dependency_track_point) =
            iterator.next_distinct_individual_id_dep(ctx.process_context().distinct_edges(), true);
        if deterministic_only
            && !native_completion_dependency_is_deterministic(ctx, dependency_track_point)
        {
            continue;
        }
        let individual_tag = -process_id;
        if individual_tag >= 0 && individual_tag != own_tag {
            values.push(individual_tag);
        }
    }
    if !values.is_empty() {
        values.push(own_tag);
        values.sort_unstable();
        values.dedup();
    }
    Some(values)
}

/// Capability produced only by the `Some(true)` arm of a fully driven
/// representative-computation task. Requiring this token keeps cache
/// publication structurally separate from stopped, clashed, or merely
/// initialized task graphs.
struct NativeSuccessfulRepresentativeTask<'a> {
    selected_individuals: &'a HashSet<Cint64>,
    /// Immutable `usedAssociationUpdateId` values captured when the task was
    /// created. Completion branching may localize or merge process nodes, but
    /// it must not change which backend association version the task read.
    used_association_update_ids: &'a HashMap<Cint64, u64>,
}

fn freeze_native_representative_association_versions(
    algo: &CompletionTaskHandleAlgorithm,
) -> HashMap<Cint64, u64> {
    algo.native_nominal_backend_replay
        .iter()
        .filter_map(|(&tag, replay)| {
            replay
                .association_update_id
                .map(|association_update_id| (tag, association_update_id))
        })
        .collect()
}

/// Publish a prepared representative batch atomically. Every association
/// version is validated before the first cache mutation, matching Konclude's
/// `usedAssociationUpdateId` transaction guard.
fn commit_native_representative_association_batch(
    cache: &mut NativeAboxRepresentativeCache,
    prepared: Vec<(Cint64, NativeAboxRepresentativeEntry)>,
    selected_individuals: &HashSet<Cint64>,
) -> Option<HashSet<Cint64>> {
    if prepared.is_empty()
        || selected_individuals.is_empty()
        || !selected_individuals
            .iter()
            .all(|tag| prepared.iter().any(|(prepared_tag, _)| prepared_tag == tag))
    {
        return None;
    }
    let mut seen = HashSet::with_capacity(prepared.len());
    for (tag, entry) in &prepared {
        if !seen.insert(*tag)
            || entry.individual_tag != *tag
            || entry.used_association_update_id
                != cache
                    .entries
                    .get(tag)
                    .map(|current| current.association_update_id)
            || !entry.complete_for_precomputation()
        {
            return None;
        }
    }

    let mut updated = HashSet::with_capacity(prepared.len());
    for (tag, mut entry) in prepared {
        cache.next_association_update_id = cache.next_association_update_id.saturating_add(1);
        entry.association_update_id = cache.next_association_update_id;
        cache.entries.insert(tag, entry);
        updated.insert(tag);
    }
    Some(updated)
}

fn write_completed_native_representative_associations(
    ctx: &CalculationAlgorithmContextBase,
    bridged: &Bridged,
    completed_task: NativeSuccessfulRepresentativeTask<'_>,
) -> Option<HashSet<Cint64>> {
    let selected_individuals = completed_task.selected_individuals;
    if selected_individuals.is_empty() || ctx.has_pending_signal() {
        return None;
    }
    let consumed_updates = completed_task.used_association_update_ids;
    let mut prepared = Vec::new();
    for seed in &bridged.nominal_seeds {
        let Some(original) = native_exact_nominal_process_node(ctx, seed.individual_tag) else {
            if selected_individuals.contains(&seed.individual_tag) {
                return None;
            }
            // Konclude's association writer visits only individuals collected
            // by this completion task. Preserve every unselected,
            // unmaterialized association byte-for-byte, including its update
            // id. In particular, the generated-node value at vector key zero
            // is not a touched association for nominal tag zero.
            continue;
        };
        let deterministic_node = native_completion_merge_target(ctx, original, true)?;
        let extraction_node = native_completion_merge_target(ctx, deterministic_node, false)?;
        let deterministic_representative_tag =
            native_completion_nominal_tag(ctx, deterministic_node)?;
        let extraction_representative_tag = native_completion_nominal_tag(ctx, extraction_node)?;
        let representative_same_individual_merging =
            deterministic_representative_tag != seed.individual_tag;
        let (concept_values, descriptor_count) =
            native_completion_label_values(ctx, extraction_node, deterministic_node)?;
        let concepts = concept_values
            .iter()
            .map(|value| (value.concept, value.negated))
            .collect();
        let role_metadata = native_completion_role_metadata(
            ctx,
            extraction_node,
            &concept_values,
            bridged,
            seed,
        )?;
        let deterministic_different_individuals = native_completion_different_individuals(
            ctx,
            deterministic_node,
            true,
            deterministic_representative_tag,
        )?;
        let nondeterministic_different_individuals = native_completion_different_individuals(
            ctx,
            extraction_node,
            false,
            extraction_representative_tag,
        )?;
        let deterministic_same_individuals =
            native_completion_same_individuals(ctx, deterministic_node, true)?;
        let nondeterministic_same_individuals =
            native_completion_same_individuals(ctx, extraction_node, false)?;
        let deterministic_same_label_identity =
            native_individual_label_identity(&deterministic_same_individuals);
        // The immutable replay journal is the task's
        // `usedAssociationUpdateId`. A branch-local merge/localization can
        // replace the original process node and thereby lose its convenience
        // `backend_data_loaded` bit, but it cannot change the journal version.
        // Presence of a materialized original node plus a consumed version is
        // therefore the exact synchronization proof used for transactional
        // publication.
        let synchronization_metadata_complete = consumed_updates.contains_key(&seed.individual_tag);
        // Konclude installs a deterministically merged association only after
        // its representative's deterministic-same label explicitly contains
        // the source id. Nondeterministic model merges do not change the
        // representative id; they are carried by the separate all-mergings
        // label and remain replay choices rather than asserted equalities.
        let merge_identity_metadata_complete = !representative_same_individual_merging
            || deterministic_same_individuals.contains(&seed.individual_tag);
        let entry = NativeAboxRepresentativeEntry {
            individual_tag: seed.individual_tag,
            concepts,
            concept_values: Some(concept_values),
            instantiated_roles: role_metadata.instantiated_roles,
            instantiated_role_values: Some(role_metadata.instantiated_role_values),
            existential_roles: role_metadata.existential_roles,
            existential_role_values: Some(role_metadata.existential_role_values),
            at_most_cardinalities: role_metadata.at_most_cardinalities,
            existential_max_cardinalities: role_metadata.existential_max_cardinalities,
            indirect_nominal_connections: role_metadata.indirect_nominal_connections,
            neighbour_role_combinations: role_metadata.neighbour_role_combinations,
            completely_saturated: true,
            completely_handled: true,
            completely_propagated: true,
            insufficient: false,
            representative_same_individual_merging: Some(representative_same_individual_merging),
            deterministic_same_individual_label_identity: merge_identity_metadata_complete
                .then_some(deterministic_same_label_identity),
            deterministic_merged_same_considered_label_identity: merge_identity_metadata_complete
                .then_some(deterministic_same_label_identity),
            deterministic_same_individuals: merge_identity_metadata_complete
                .then_some(deterministic_same_individuals.clone()),
            deterministic_merged_same_considered_individuals: merge_identity_metadata_complete
                .then_some(deterministic_same_individuals),
            nondeterministic_same_individuals: merge_identity_metadata_complete
                .then_some(nondeterministic_same_individuals),
            deterministic_different_individuals: Some(deterministic_different_individuals),
            nondeterministic_different_individuals: Some(nondeterministic_different_individuals),
            representative_same_individual_id: Some(deterministic_representative_tag),
            deterministic_same_individual_id: Some(deterministic_representative_tag),
            completion_processing_restriction_flags: Some(
                ctx.process_context()
                    .node(extraction_node)
                    .processing_restriction_flags(),
            ),
            completion_label_descriptor_count: Some(descriptor_count),
            association_update_id: 0,
            used_association_update_id: consumed_updates.get(&seed.individual_tag).copied(),
            scheduled_individual: Some(selected_individuals.contains(&seed.individual_tag)),
            association_origin: Some(NativeAboxAssociationOrigin::CompletionWriteback),
            merge_identity_metadata_complete,
            role_metadata_complete: true,
            synchronization_metadata_complete,
        };
        // Transactional writeback: validate the complete typed association
        // before touching the shared cache. Unsupported merge/synchronization
        // shapes keep the prior incomplete entry intact. A scheduled
        // individual cannot be skipped because its task would otherwise be
        // falsely reported as having discharged the association.
        let typed_complete = entry.complete_for_precomputation();
        let seed_covered = native_cache_entry_covers_seed(&entry, seed);
        let complete = typed_complete && seed_covered;
        if !complete {
            if selected_individuals.contains(&seed.individual_tag) {
                return None;
            }
            continue;
        }
        prepared.push((seed.individual_tag, entry));
    }
    let mut cache = bridged.native_representative_cache.borrow_mut();
    let cache = cache.as_mut()?;
    commit_native_representative_association_batch(cache, prepared, selected_individuals)
}

/// Direct port of Konclude's representative-cache computation lifecycle:
/// select at most seven incomplete associations, run a fresh satisfiability
/// task, atomically publish every touched association, then reschedule until
/// no incomplete association remains. A failed task or writeback is unknown,
/// never a consistency claim.
fn precompute_native_representative_batches(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    preserve_saturation: bool,
    task_budget_seconds: u64,
) -> Option<bool> {
    {
        let cache = bridged.native_representative_cache.borrow();
        let cache = cache.as_ref()?;
        if cache.association_write_aborted {
            // The writer aborts only after observing a clashed representative
            // saturation node. Saturation is an under-approximation, so such a
            // clash is a sound ontology clash; this is Konclude's
            // `hasIndividualPrecomputationClashed()` path.
            return Some(false);
        }
    }
    if bridged.nominal_seeds.is_empty() {
        return None;
    }
    let mut coordination = NativeRepresentativeCoordinationState::default();
    loop {
        let selected =
            native_incomplete_abox_seed_batch(bridged, NATIVE_REPRESENTATIVE_BATCH_SIZE)?;
        if selected.is_empty() {
            break;
        }
        let previous_versions: HashMap<Cint64, u64> = {
            let cache = bridged.native_representative_cache.borrow();
            let cache = cache.as_ref()?;
            selected
                .iter()
                .map(|tag| {
                    cache
                        .entries
                        .get(tag)
                        .map(|entry| (*tag, entry.association_update_id))
                })
                .collect::<Option<HashMap<_, _>>>()?
        };
        coordination.running_tasks += 1;
        reset_probe_env_impl(algo, ctx, bridged, preserve_saturation, false);
        // Representative computation always has a backend association task
        // adapter. Do not infer that lifecycle from `card_defs`: cardinality
        // can occur inside a named assertion while that compatibility field is
        // empty. Install the typed journal for every representative task and
        // freeze the versions before completion can branch, merge, or localize
        // any process node.
        install_native_nominal_backend_replay(algo, bridged);
        let used_association_update_ids = freeze_native_representative_association_versions(algo);
        if !selected
            .iter()
            .all(|tag| used_association_update_ids.contains_key(tag))
        {
            coordination.running_tasks -= 1;
            coordination.failed_tasks += 1;
            return None;
        }
        algo.conf_inprocess_cow = true;
        configure_production_search(algo);
        algo.probe_budget = Some(std::time::Duration::from_secs(task_budget_seconds.max(1)));
        if !initialize_native_nominal_state_for_tags(algo, ctx, bridged, Some(&selected)) {
            coordination.running_tasks -= 1;
            coordination.failed_tasks += 1;
            return None;
        }
        match native_nominal_consistency(algo, ctx, bridged) {
            Some(false) => {
                coordination.running_tasks -= 1;
                coordination.clashed = true;
                return Some(false);
            }
            None => {
                coordination.running_tasks -= 1;
                coordination.failed_tasks += 1;
                return None;
            }
            Some(true) => {}
        }
        let Some(updated) = write_completed_native_representative_associations(
            ctx,
            bridged,
            NativeSuccessfulRepresentativeTask {
                selected_individuals: &selected,
                used_association_update_ids: &used_association_update_ids,
            },
        ) else {
            coordination.running_tasks -= 1;
            coordination.writeback_failed = true;
            return None;
        };
        coordination.running_tasks -= 1;
        let selected_advanced = {
            let cache = bridged.native_representative_cache.borrow();
            let cache = cache.as_ref()?;
            selected.iter().all(|tag| {
                updated.contains(tag)
                    && cache.entries.get(tag).is_some_and(|entry| {
                        entry.complete_for_precomputation()
                            && entry.association_update_id
                                > previous_versions.get(tag).copied().unwrap_or(u64::MAX)
                    })
            })
        };
        if !selected_advanced {
            coordination.writeback_failed = true;
            return None;
        }
    }
    native_representative_coordination_complete(bridged, coordination).then_some(true)
}

fn empty_role_nominal_model_certificate(tin: &TInput, bridged: &Bridged) -> bool {
    if !bridged.source_tbox
        || !bridged.has_native_nominals()
        || !tin.nominal_abox.complete
        || !tin.nominal_abox.unsupported.is_empty()
        || tin.nominal_abox.individuals.is_empty()
        || !tin.nominal_abox.role_assertions.is_empty()
    {
        return false;
    }

    // Built-in top roles cannot be assigned the empty relation used by this
    // witness.  The route-level gate rejects them as well; retain this local
    // condition so the helper remains independently fail closed in tests.
    if has_builtin_top_role(tin) {
        return false;
    }

    // `DatatypeDefinition` is represented in the source side channel as an
    // equivalence with fixed `__dt__*` abstractions in object position.  These
    // do not denote freely interpretable OWL classes and therefore cannot be
    // set empty by this object-model witness.  Datatype fillers nested under
    // an ordinary (empty) data role remain harmless and need not reject 10621.
    if has_fixed_datatype_object_position(tin) {
        return false;
    }

    // Empty ordinary roles satisfy role inclusions, chains, transitivity,
    // (inverse-)functionality, symmetry, asymmetry, irreflexivity and role
    // disjointness.  A role head without a role guard can instead require an
    // edge (notably reflexivity or a ground assertion), so decline rather than
    // trying to infer its source provenance from the clausal shape.
    if tin.clauses.iter().any(|clause| {
        clause
            .head
            .iter()
            .any(|atom| matches!(atom, HAtom::Role { .. }))
            && !clause
                .body
                .iter()
                .any(|atom| matches!(atom, HAtom::Role { .. }))
    }) {
        return false;
    }

    let individuals: HashMap<&str, usize> = tin
        .nominal_abox
        .individuals
        .iter()
        .enumerate()
        .map(|(index, entry)| (entry.individual.as_str(), index))
        .collect();
    if individuals.len() != tin.nominal_abox.individuals.len() {
        return false;
    }
    let domain_size = individuals.len();

    fn holds(
        concept: &SourceConcept,
        element: usize,
        domain_size: usize,
        individuals: &HashMap<&str, usize>,
    ) -> Option<bool> {
        let role_successor_count = |filler: &SourceConcept| -> Option<i64> {
            let mut count = 0i64;
            for successor in 0..domain_size {
                if holds(filler, successor, domain_size, individuals)? {
                    count += 1;
                }
            }
            Some(count)
        };
        Some(match concept {
            SourceConcept::Name(_) | SourceConcept::Bottom => false,
            SourceConcept::Top => true,
            SourceConcept::Nominal(individual) => *individuals.get(individual.as_str())? == element,
            SourceConcept::Not(operand) => !holds(operand, element, domain_size, individuals)?,
            SourceConcept::And(operands) => {
                for operand in operands {
                    if !holds(operand, element, domain_size, individuals)? {
                        return Some(false);
                    }
                }
                true
            }
            SourceConcept::Or(operands) => {
                for operand in operands {
                    if holds(operand, element, domain_size, individuals)? {
                        return Some(true);
                    }
                }
                false
            }
            SourceConcept::Exists(role, filler) => match role {
                SourceRole::Universal => role_successor_count(filler)? > 0,
                SourceRole::Name(_) | SourceRole::Inverse(_) => false,
            },
            SourceConcept::Forall(role, filler) => match role {
                SourceRole::Universal => role_successor_count(filler)? == domain_size as i64,
                SourceRole::Name(_) | SourceRole::Inverse(_) => true,
            },
            SourceConcept::AtLeast(cardinality, role, filler) => {
                let successors = match role {
                    SourceRole::Universal => role_successor_count(filler)?,
                    SourceRole::Name(_) | SourceRole::Inverse(_) => 0,
                };
                successors >= *cardinality
            }
            SourceConcept::AtMost(cardinality, role, filler) => {
                let successors = match role {
                    SourceRole::Universal => role_successor_count(filler)?,
                    SourceRole::Name(_) | SourceRole::Inverse(_) => 0,
                };
                successors <= *cardinality
            }
            SourceConcept::HasSelf(role) => matches!(role, SourceRole::Universal),
        })
    }

    // Assertions are usually the cheapest way to refute this deliberately
    // sparse witness. Check them before the potentially domain-wide TBox
    // validation: a large ABox with an ordinary named type otherwise evaluates
    // every source axiom for every individual only to reject the same witness
    // at the end. This is a pure reordering of conjunction checks.
    for (element, entry) in tin.nominal_abox.individuals.iter().enumerate() {
        for assertion in &entry.assertions {
            if holds(assertion, element, domain_size, &individuals) != Some(true) {
                return false;
            }
        }
    }
    for axiom in &tin.source_axioms {
        for element in 0..domain_size {
            let Some(left) = holds(&axiom.left, element, domain_size, &individuals) else {
                return false;
            };
            let Some(right) = holds(&axiom.right, element, domain_size, &individuals) else {
                return false;
            };
            let satisfied = match axiom.kind {
                crate::json_io::SourceAxiomKind::SubClass => !left || right,
                crate::json_io::SourceAxiomKind::Equivalent => left == right,
                crate::json_io::SourceAxiomKind::Disjoint => !(left && right),
            };
            if !satisfied {
                return false;
            }
        }
    }
    tin.nominal_abox.different.iter().all(|(left, right)| {
        let (Some(&left), Some(&right)) = (
            individuals.get(left.as_str()),
            individuals.get(right.as_str()),
        ) else {
            return false;
        };
        left != right
    })
}

/// Decide the ontology-level nominal/ABox consistency before taxonomy probes.
/// `Some(false)` is a genuine clash, `Some(true)` a complete model, and `None`
/// remains DEFER on STOP or a tainted incomplete search.
fn native_nominal_consistency(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
) -> Option<bool> {
    if !bridged.has_native_nominals() {
        return Some(true);
    }
    if bridged
        .nominal_different
        .iter()
        .any(|(left, right)| left == right)
    {
        return Some(false);
    }
    if ctx.has_pending_signal() {
        return match ctx.pending_signal() {
            super::completion::clash::CalcSignal::Clash(_) => Some(false),
            _ => None,
        };
    }
    algo.drive_deadline = algo
        .probe_budget
        .map(|budget| std::time::Instant::now() + budget);
    let consistent = algo.run_completion_on(ctx);
    if !consistent {
        return match ctx.pending_signal() {
            super::completion::clash::CalcSignal::Clash(_) => Some(false),
            _ => None,
        };
    }
    (!algo.completeness_poisoned).then_some(true)
}

/// Copy the non-deterministic prefix of every nominal label from the completed
/// ontology-consistency graph. Konclude keeps a deterministic task and a
/// completion-graph-cached task whose label tails share the deterministic
/// head; in the in-process bridge, dependency branch tags identify that same
/// prefix before the first deterministic descriptor.
fn snapshot_native_consistency_nominal_nondeterministic_prefix(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
) -> Option<HashMap<Cint64, Vec<(ConceptId, bool)>>> {
    let mut snapshot = HashMap::with_capacity(bridged.nominal_seeds.len());
    for seed in &bridged.nominal_seeds {
        let node = algo.get_up_to_date_individual_by_id(-seed.individual_tag, ctx);
        if node.is_none() {
            return None;
        }
        let node = algo.get_corrected_merged_into_individual_node(node, ctx);
        if node.is_none() || node.index() >= ctx.process_context().node_count() {
            return None;
        }
        let label = ctx.process_context().node(node).reapply_con_label_set;
        if label.is_none() {
            snapshot.insert(seed.individual_tag, Vec::new());
            continue;
        }
        let mut descriptor = ctx
            .process_context()
            .label_set(label)
            .get_adding_sorted_concept_description_linker();
        let mut prefix = Vec::new();
        let mut walked = 0usize;
        while descriptor.is_some() {
            if descriptor.index() >= ctx.process_context().con_desc_count()
                || walked > ctx.process_context().con_desc_count()
            {
                return None;
            }
            let (concept, negated, dependency_track_point, next) = {
                let descriptor_ref = ctx.process_context().con_desc(descriptor);
                (
                    descriptor_ref.get_concept(),
                    descriptor_ref.is_negated(),
                    descriptor_ref.get_dependency_track_point(),
                    descriptor_ref.get_next_concept_descriptor(),
                )
            };
            if !algo.has_nondeterministic_dependency(dependency_track_point, ctx) {
                break;
            }
            prefix.push((concept, negated));
            descriptor = next;
            walked += 1;
        }
        prefix.sort_unstable_by_key(|(concept, negated)| (concept.raw, *negated));
        prefix.dedup();
        snapshot.insert(seed.individual_tag, prefix);
    }
    Some(snapshot)
}

/// Verify a sparse batch of positive conjunctions against one source-mode
/// bridge terminology. `true` means every concept in one seed row cannot hold
/// at the same root. Every row gets fresh process state, while the expensive
/// read-only terminology and sound ontology-level caches are shared across
/// the batch. Invalid/empty rows, unsupported input, or any probe that remains
/// deferred after the normal escalating budgets makes the whole batch defer.
/// Konclude's completion-side coupling to the precomputed saturation graph.
/// These are the flags used by classification jobs after saturation data has
/// been installed. In particular, cache reading is required to revalidate a
/// saturation-cached node after direct modification; without it the retest
/// path drops successor-creation blocking and expands the cached subtree.
fn configure_production_completion_saturation_coupling(algo: &mut CompletionTaskHandleAlgorithm) {
    // The `KM_HT_NO_*` switches are diagnostic cuts through Konclude's
    // completion-side saturation coupling. They leave production unchanged
    // unless explicitly set and let ontology traces isolate the first
    // divergent half without disabling the saturation pre-pass itself.
    algo.conf_expand_created_successors_from_saturation =
        std::env::var_os("KM_HT_NO_SAT_SUCCESSOR_EXPANSION").is_none();
    algo.conf_caching_blocking_from_saturation =
        std::env::var_os("KM_HT_NO_SAT_CACHING_BLOCKING").is_none();
    // CCalculationTableauCompletionTaskHandleAlgorithm.cpp ctor lines
    // 226-229 deliberately leave this OFF: the dependency for a resolved
    // successor must include the resolved universal restrictions, which that
    // path does not yet construct.  Do not enable the otherwise ported u22
    // resolver in production completion until Konclude does.
    algo.conf_successor_saturation_expansion_restrictions_resolving = false;
    // CCalculationTableauCompletionTaskHandleAlgorithm ctor lines 188-190.
    // These three absorption switches are independent of cache establishment:
    // they park rules while the corresponding cache flag remains valid and the
    // u10/u21 reapply paths restore them if that flag is later abolished.
    let cached_absorption = std::env::var_os("KM_HT_NO_SAT_CACHED_ABSORPTION").is_none();
    algo.conf_sat_exp_cached_disj_absorp = cached_absorption;
    algo.conf_sat_exp_cached_merg_absorp = cached_absorption;
    algo.conf_sat_exp_cached_succ_absorp = cached_absorption;
    // CCalculationTableauCompletionTaskHandleAlgorithm.cpp ctor line 237.
    algo.conf_saturation_expansion_cache_reading =
        std::env::var_os("KM_HT_NO_SAT_CACHE_READING").is_none();
    // CCalculationTableauCompletionTaskHandleAlgorithm.cpp ctor line 236
    // (`mConfSaturationCachingTestingDuringBlockingTests = true`). Konclude
    // re-runs `detectIndividualNodeSaturationCached` on every localized ancestor
    // it walks during a blocking test (cpp 19101), which is what keeps the
    // saturation block and the `skipBlockerSearch` short-circuit (cpp 19106,
    // ported at u19.rs:1153) in agreement on a node the blocking walk reaches
    // before the processing queue does. The KM ctor default is FALSE and no
    // other writer exists, so the port ran every blocking test with the retest
    // suppressed; this restores the upstream default.
    algo.conf_saturation_caching_testing_during_blocking_tests = true;
}

/// The native-nominal variant of the completion-side coupling: the same
/// Konclude flags, plus the fail-closed nominal-connection decline.
///
/// Konclude additionally sets `mConfSaturationCachingWithNominals`
/// (u31.rs:153); the bridge deliberately leaves it FALSE. That is the guard
/// `try_establish_saturation_caching` (u22.rs:993-1011) reads: a saturation node
/// carrying `INDSATFLAGNOMINALCONNECTION` then cannot establish
/// `PRF_SATURATIONBLOCKINGCACHED`, because the release condition Konclude relies
/// on — `tryInstallSaturationCachingReactivation` over the node's
/// successor-connected-nominal set — needs the exact per-nominal dependency
/// record the bridge does not keep (`conf_exact_nominal_dependency_tracking`
/// is false). `conf_saturation_coupling_declines_nominal_connected` closes the
/// matching hole on the expansion side (u17).
///
/// Nominal-connected saturation nodes are therefore inert on this route in BOTH
/// directions, and every remaining node is nominal-free, i.e. a pure TBox
/// consequence set. The `is_critical_nominal_concept_descriptor_insufficient`
/// port (`saturation/s09.rs:1394-1507`) already forces a saturation node that
/// reaches a nominal without a consistency-prefix witness to INSUFFICIENT, which
/// is a second, independent fail-closed layer on the caching side.
fn configure_native_nominal_completion_saturation_coupling(
    algo: &mut CompletionTaskHandleAlgorithm,
) {
    configure_production_completion_saturation_coupling(algo);
    // Konclude u31.rs:153 sets this true; the bridge must not. Set explicitly
    // (not merely left at the ctor default) so the decision is local to this
    // function and cannot be inherited from a previously configured algorithm.
    algo.conf_saturation_caching_with_nominals = false;
    algo.conf_saturation_coupling_declines_nominal_connected = true;
    configure_native_backend_expansion_reuse(algo);
}

/// Backend-expansion reuse (`u25::reuse_individual_backend_expansion`), the
/// mechanism by which a derived task adopts the consistency model's recorded
/// non-deterministic ABox state in ONE non-deterministic step instead of
/// re-deriving it disjunct by disjunct.
///
/// `mConfBackendExpansionReuse` is a Konclude ctor `true`
/// (`CCalculationTableauCompletionTaskHandleAlgorithm.cpp` 478, re-asserted at
/// 680); KM's `CompletionTaskHandleAlgorithm::new` seeds the whole config block
/// to `false` by port convention and the bridge never runs `read_calculation_config`
/// (that lives on the unported `handle_task` spine), so the flag has to be set
/// here to reach the upstream default.
///
/// This only ARMS the mechanism. An individual is queued for reuse
/// (`u36::get_up_to_date_individual_by_id`, Konclude cpp 22765-22771) exclusively
/// when its association is completely handled, carries at least one of the four
/// non-deterministic labels (`has_reusable_elements`), and is fully representable
/// in the typed replay record (`reuse_replay_representable`). An ontology whose
/// associations record no branch choices therefore sees no change at all.
///
/// Konclude's LATE-DYNAMIC activation arms
/// (`mConfBackendExpansionLateDynamicReuseActivation` plus the
/// neighbour-/same-individual COUNT thresholds, cpp 22738-22764) are label-size
/// heuristics and are deliberately NOT ported: they would make the mechanism fire
/// as a function of how big a particular ontology's labels happen to be.
fn configure_native_backend_expansion_reuse(algo: &mut CompletionTaskHandleAlgorithm) {
    algo.conf_backend_expansion_reuse = true;
    // The count-threshold arms stay off (see the doc comment); with them off
    // `conf_backend_expansion_late_dynamic_reuse_activation` has nothing to gate.
    algo.conf_backend_expansion_late_dynamic_reuse_activation = false;
    algo.conf_backend_expansion_neighbour_individual_count_reuse_activation = 0;
    algo.conf_backend_expansion_same_individual_count_reuse_activation = 0;
}

/// Fail-closed precondition for arming the completion↔saturation coupling on a
/// native-nominal ontology.
///
/// The coupling dereferences ontology-side concept→saturation reference
/// linkings into the process context's saturation-node arena. Three things must
/// hold before a completion probe may follow one of those pointers, and none of
/// them is checked anywhere else:
///
/// 1. the saturation arena survived the probe-env reset (the `preserve_saturation`
///    carry in `reset_probe_env_impl`) and is non-empty;
/// 2. every installed linking resolves to an IN-RANGE saturation node — a stale
///    or out-of-range id would index a foreign node;
/// 3. no linking resolves to an ABox individual REPRESENTATION node. That is the
///    separation the whole soundness argument rests on: the ABox wave
///    (`build_native_abox_saturation_seeds`) writes only individual-tag slots and
///    installs no concept linking, so a linking that pointed at one would mean
///    the two waves had collided in the id space and an ABox-influenced label
///    could be replayed onto an unrelated successor.
///
/// Any violation returns `false` and the coupling stays off, leaving the route
/// exactly as it behaves today.
fn native_saturation_coupling_metadata_covered(
    ctx: &CalculationAlgorithmContextBase,
    bridged: &Bridged,
) -> bool {
    use super::model::concept_process::ConceptProcessDataId;

    if !bridged.has_native_nominals() {
        return false;
    }
    let sat_node_count = ctx.process_context().sat_node_count();
    if sat_node_count == 0 {
        return false;
    }
    let mut resolved = 0usize;
    let check = |node: super::process::SatNodeId, resolved: &mut usize| -> bool {
        if node.is_none() {
            return true;
        }
        if node.index() >= sat_node_count {
            return false;
        }
        if ctx
            .process_context()
            .sat_node(node)
            .is_abox_individual_representation_node()
        {
            return false;
        }
        *resolved += 1;
        true
    };
    let concept_count = ctx.ontology_arenas().concept_count();
    for index in 0..concept_count {
        let concept = ConceptId::new(index);
        let concept_data = ctx.ontology_arenas().concept(concept).get_concept_data();
        if concept_data == super::model::substrate::INVALID {
            continue;
        }
        let ref_linking = ctx
            .ontology_arenas()
            .concept_process_data(ConceptProcessDataId::new(concept_data))
            .get_concept_reference_linking();
        if ref_linking.is_none() {
            continue;
        }
        let linking_data = ctx
            .ontology_arenas()
            .concept_saturation_reference_linking_data(ref_linking);
        let items = [
            linking_data.get_concept_saturation_reference_linking_data(false),
            linking_data.get_concept_saturation_reference_linking_data(true),
            linking_data.get_existential_successor_concept_saturation_reference_linking_data(),
        ];
        for item in items {
            if item.is_none() {
                continue;
            }
            let node = ctx
                .ontology_arenas()
                .saturation_concept_reference_linking(item)
                .get_individual_process_node_for_concept();
            if !check(node, &mut resolved) {
                return false;
            }
        }
    }
    // A coupling with nothing to read is not "covered": it would silently be a
    // no-op and hide a broken saturation hand-off behind an "armed" log line.
    resolved > 0
}

// ---------------------------------------------------------------------------
// Saturation-first probe answering (task #23).
//
// Konclude decides ~95% of its classification work by the cheap non-branching
// approximation saturation and runs the backtracking tableau only on the
// residue (docs/KONCLUDE-STUDY.md). This section wires the ported saturation
// units (saturation/s01..s12) in front of the bridge's completion probes:
// saturate ONCE per classification in a dedicated env, extract per-named
// verdicts + certain subsumers, and let `bridged_classify` answer whole
// subjects from them — every UNKNOWN falls through to the existing probe path
// unchanged. Opt-in via KM_HT_SATURATION=1 (how to run it in production is a
// separate decision; nothing in the default path changes).
// ---------------------------------------------------------------------------

/// Konclude's PRODUCTION saturation configuration: `readCalculationConfig`
/// (CCalculationTableauApproximationSaturationTaskHandleAlgorithm cpp 180–237,
/// config-present branch, non-EL structure path) with the config defaults from
/// CReasonerConfigurationGroup.cpp 440–451 (SaturationCriticalConceptTesting =
/// true, SaturationDirectCriticalToInsufficient = false,
/// SaturationSuccessorExtension = true) plus the ctor defaults (cpp 130–170)
/// for the fields readCalculationConfig leaves untouched.
fn configure_production_saturation(
    algo: &mut super::saturation::algorithm::SaturationTaskHandleAlgorithm,
) {
    algo.conf_force_all_concept_insertion = true; // cpp 191 (non-EL / ABox path)
    algo.conf_implication_adding_skipping = false; // cpp 192
    algo.conf_force_all_copy_instead_of_substituition = false; // cpp 185
    algo.conf_directly_critical_to_insufficient = false; // cfg 444 default false
    algo.conf_add_critical_concepts_to_queues = true; // cfg 440 default true
    algo.conf_check_critical_concepts = true; // cfg 440 default true

    // CReasonerConfigurationGroup.cpp 448 installs `true`; the reader's local
    // fallback `false` applies only when the property is absent from the
    // configuration group. This is the configuration used by Konclude's
    // production precomputation.
    let sat_ext = std::env::var_os("KM_HT_NO_SAT_SUCCESSOR_EXTENSION").is_none();
    algo.conf_concepts_extension_processing = sat_ext;
    algo.conf_all_concepts_extension_processing =
        sat_ext && std::env::var_os("KM_HT_NO_SAT_ALL_EXTENSION").is_none();
    algo.conf_functional_concepts_extension_processing =
        sat_ext && std::env::var_os("KM_HT_NO_SAT_FUNCTIONAL_EXTENSION").is_none();
    algo.conf_nominal_processing = true; // cfg 497 (inert: nominal-free fragment)
                                         // ctor defaults (cpp 152–168):
    algo.conf_copy_node_from_top_individual_for_many_concepts = true;
    algo.conf_detailed_merging_test_for_atmost_critical_testing = true;
    algo.conf_simple_merging_test_for_atmost_critical_testing = true;
    algo.conf_delayed_merging_critical_atmost_concepts = true;
    algo.conf_delayed_merging_critical_atmost_concepts_cardinality_size = 100;
    algo.conf_resolve_operand_concept_size = 100;
    algo.conf_referred_node_many_concept_count = 500;
    algo.conf_many_concept_referred_node_count_process_limit = 2;
    algo.conf_referred_node_concept_count_process_limit = 1500;
    algo.conf_referred_node_unprocessed_count_process_limit = 1;
    algo.conf_referred_node_checking_depth = 5;
}

/// Port of `CExtractPropagationIntoCreationDirectionPreProcess::preprocess`
/// (Reasoner/Preprocess, cpp 39–105) over the bridged arenas: mark every
/// ∀/∃-family concept whose role can also appear in successor-CREATION
/// direction — the saturation ALL rule keys its criticality escape hatch on
/// this flag (without it a `∃R.C ⊓ ∀R.¬C` node would complete SAT-certain).
///
/// KONCLUDE-PORT-NOTE[identity]: `creationRoleHash` is filled from the
/// creation role's indirect super-role list, which in Konclude STARTS with the
/// role itself; the bridge builds strict lists, so the role is inserted
/// explicitly (see `saturation_indirect_super_roles`).
/// KONCLUDE-PORT-NOTE[api]: the C++ also stamps
/// `CRoleProcessData::setPropagationAndCreationConceptsFlag` — CRoleProcessData
/// is unported; the single consumer (applyALLRule's else arm) treats absent
/// role data exactly as flag-set (see the s04 port note).
fn extract_propagation_into_creation_direction(ctx: &mut CalculationAlgorithmContextBase) {
    use super::model::concept_process::ConceptProcessData;
    use super::model::op::{CCFS_ALL_AQALL_TYPE, CCFS_POSSIBLE_ROLE_CREATION_TYPE};
    let n = ctx.ontology_arenas().concept_count();
    let mut creation_roles: std::collections::HashSet<RoleId> = std::collections::HashSet::new();
    for i in 0..n {
        let cid = ConceptId::new(i);
        let (is_creation, role) = {
            let c = ctx.ontology_arenas().concept(cid);
            (
                c.get_concept_operator()
                    .has_partial_operator_code_flag(CCFS_POSSIBLE_ROLE_CREATION_TYPE),
                c.get_role(),
            )
        };
        if is_creation && role.is_some() && !creation_roles.contains(&role) {
            creation_roles.insert(role); // [identity]
            let supers: Vec<super::model::substrate::NegLink<RoleId>> = ctx
                .ontology_arenas()
                .role(role)
                .get_indirect_super_role_list()
                .to_vec();
            for s in supers {
                if !s.negated {
                    creation_roles.insert(s.target);
                }
            }
        }
    }
    for i in 0..n {
        let cid = ConceptId::new(i);
        let (flagged, role, concept_data) = {
            let c = ctx.ontology_arenas().concept(cid);
            (
                c.get_concept_operator().has_partial_operator_code_flag(
                    CCFS_ALL_AQALL_TYPE | CCFS_POSSIBLE_ROLE_CREATION_TYPE,
                ),
                c.get_role(),
                c.get_concept_data(),
            )
        };
        if flagged && role.is_some() && creation_roles.contains(&role) {
            let arenas = ctx.ontology_arenas_mut();
            let con_proc_data = if concept_data == super::model::substrate::INVALID {
                let fresh = arenas.alloc_concept_process_data(ConceptProcessData::new());
                arenas.concept_mut(cid).set_concept_data(fresh.raw);
                fresh
            } else {
                super::model::concept_process::ConceptProcessDataId::new(concept_data)
            };
            arenas
                .concept_process_data_mut(con_proc_data)
                .propagation_into_creation_direction = true;
        }
    }
}

/// Port of the CONSTRUCTION half of
/// `CTotallyPrecomputationThread::createConceptSaturationProcessingJob`
/// (Reasoner/Consistiser cpp 2022–2230) +
/// `CSatisfiableCalculationTaskFromCalculationJobGenerator::createApproximatedSaturationCalculationTask`
/// (Reasoner/Generator cpp 40–163): one saturation seed per (concept, polarity)
/// item, plus Konclude's separate (role, concept, polarity) successor item
/// whenever the role has ranges. Each item gets a pre-built saturation node,
/// is registered in the databox node vector, and is queued for processing.
///
/// The leaf-first ordering, SUBSTITUTE/COPY assignment, and reachable
/// disjunct-candidate extension items are ported below. The role-range items
/// are essential after the bridge installs native CRole domain/range linkers:
/// their nodes initialize with `initRole`, exactly as Konclude requires.
fn build_saturation_seeds(ctx: &mut CalculationAlgorithmContextBase, bridged: &Bridged) {
    assert!(
        build_saturation_seeds_with_deadline(ctx, bridged, None),
        "unbounded saturation-seed construction cannot time out"
    );
}

/// Build the generic concept-saturation seeds, stopping safely when the
/// caller's task budget expires. The bridge owns the partially constructed
/// context and discards it on `false`, so no incomplete seed set is consumed.
fn build_saturation_seeds_with_deadline(
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    deadline: Option<std::time::Instant>,
) -> bool {
    use super::model::concept_process::{
        ConceptProcessData, ConceptSaturationReferenceLinkingData,
        SaturationConceptReferenceLinking, SaturationConceptReferenceLinkingId,
        SATURATION_COPY_MODE, SATURATION_SUBSTITUTE_MODE,
    };
    use super::model::op::{
        CCALL, CCAND, CCAQAND, CCAQCHOOCE, CCAQSOME, CCATLEAST, CCATMOST, CCATOM, CCEQ, CCIMPLTRIG,
        CCOR, CCSOME, CCSUB,
    };
    use super::process::sat_linker::IndividualSaturationProcessNodeLinkerId;
    use super::process::sat_node::IndividualSaturationProcessNode;
    use super::process::sat_ref::ExtendedConceptReferenceLinkingData;

    #[derive(Clone, Copy)]
    struct Seed {
        concept: ConceptId,
        negated: bool,
        role_ranges: RoleId,
        potentially_exist: bool,
    }

    // Construction items, C++ 2022-2127. Only existential/cardinality fillers
    // are potentially-exist items; marking every seed disabled substitution.
    let mut seeds: Vec<Seed> = Vec::new();
    let mut seed_index: HashMap<(ConceptId, bool), usize> = HashMap::new();
    let mut role_seed_index: HashMap<(RoleId, ConceptId, bool), usize> = HashMap::new();
    let push = |seeds: &mut Vec<Seed>,
                seed_index: &mut HashMap<(ConceptId, bool), usize>,
                concept: ConceptId,
                negated: bool,
                potentially_exist: bool|
     -> usize {
        if concept.is_none() {
            return usize::MAX;
        }
        if let Some(&index) = seed_index.get(&(concept, negated)) {
            seeds[index].potentially_exist |= potentially_exist;
            index
        } else {
            let index = seeds.len();
            seeds.push(Seed {
                concept,
                negated,
                role_ranges: RoleId::NONE,
                potentially_exist,
            });
            seed_index.insert((concept, negated), index);
            index
        }
    };
    let push_role = |seeds: &mut Vec<Seed>,
                     role_seed_index: &mut HashMap<(RoleId, ConceptId, bool), usize>,
                     role: RoleId,
                     concept: ConceptId,
                     negated: bool,
                     potentially_exist: bool|
     -> usize {
        if concept.is_none() || role.is_none() {
            return usize::MAX;
        }
        if let Some(&index) = role_seed_index.get(&(role, concept, negated)) {
            seeds[index].potentially_exist |= potentially_exist;
            index
        } else {
            let index = seeds.len();
            seeds.push(Seed {
                concept,
                negated,
                role_ranges: role,
                potentially_exist,
            });
            role_seed_index.insert((role, concept, negated), index);
            index
        }
    };

    // Exact `hasRoleRanges`: inspect the range side of every signed indirect
    // super role. The local helper restores Konclude's reflexive role entry
    // for saturation without changing the completion arena's role lists.
    let mut roles_with_ranges = std::collections::HashSet::new();
    for role_index in 0..ctx.ontology_arenas().role_count() {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return false;
        }
        let role = RoleId::new(role_index);
        if super::saturation::algorithm::SaturationTaskHandleAlgorithm::saturation_indirect_super_roles(
            role,
            ctx,
        )
        .iter()
        .any(|super_link| {
            !ctx.ontology_arenas()
                .role(super_link.target)
                .get_domain_range_concept_list(!super_link.negated)
                .is_empty()
        }) {
            roles_with_ranges.insert(role);
        }
    }
    // Restriction concept -> its role-specific successor item. Konclude wires
    // this through mExistentialSuccessorSatConRefLinking (cpp 2071-2074).
    let mut existential_successor_seed: Vec<(ConceptId, usize)> = Vec::new();
    let top = ctx.processing_data_box().ontology_top_concept;
    push(&mut seeds, &mut seed_index, top, false, false);
    for &named in &bridged.named {
        // `createSaturationConstructionJob` seeds class-named concepts, not
        // every concept-vector entry. Q_/definer atoms deliberately have no
        // class-name linker in the bridge, just like Konclude's anonymous
        // structural concepts.
        if ctx.ontology_arenas().concept(named).has_class_name() {
            push(&mut seeds, &mut seed_index, named, false, false);
        }
    }
    let n = ctx.ontology_arenas().concept_count();
    for i in 0..n {
        if i & 0x3ff == 0 && deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline)
        {
            return false;
        }
        let cid = ConceptId::new(i);
        let (op_code, role, operands) = {
            let c = ctx.ontology_arenas().concept(cid);
            (
                c.get_operator_code(),
                c.get_role(),
                c.get_operand_list().to_vec(),
            )
        };
        match op_code {
            CCSOME | CCAQSOME | CCALL => {
                // negation = (opCode == CCALL); operand negation = isNegated ^ negation
                let negation = op_code == CCALL;
                let (filler, filler_negated) = operands
                    .first()
                    .map(|op_link| (op_link.target, op_link.negated ^ negation))
                    .unwrap_or((top, negation));
                if roles_with_ranges.contains(&role) {
                    let item = push_role(
                        &mut seeds,
                        &mut role_seed_index,
                        role,
                        filler,
                        filler_negated,
                        true,
                    );
                    existential_successor_seed.push((cid, item));
                } else {
                    push(&mut seeds, &mut seed_index, filler, filler_negated, true);
                }
            }
            CCATLEAST | CCATMOST => {
                // ≥/≤: operand polarity as-is (cpp 2049–2054)
                let (filler, filler_negated) = operands
                    .first()
                    .map(|op_link| (op_link.target, op_link.negated))
                    .unwrap_or((top, false));
                if roles_with_ranges.contains(&role) {
                    let item = push_role(
                        &mut seeds,
                        &mut role_seed_index,
                        role,
                        filler,
                        filler_negated,
                        true,
                    );
                    existential_successor_seed.push((cid, item));
                } else {
                    push(&mut seeds, &mut seed_index, filler, filler_negated, true);
                }
            }
            _ => {}
        }
    }
    let base_seed_count = seeds.len();

    // `extendDisjunctionsCandidateAlternativesItems`, C++ 1153-1268. Konclude
    // does not seed every disjunction in the terminology. It starts from the
    // named/existential items above and adds only reachable disjunctions and
    // their effective alternatives. Auxiliary items are invalid special-item
    // references: substituting through one would conflate an alternative with
    // the class whose pseudo-model caused it to be saturated.
    let mut invalid_special = std::collections::HashSet::new();
    let mut extension_item = 0usize;
    while extension_item < seeds.len() {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return false;
        }
        let seed = seeds[extension_item];
        extension_item += 1;
        let seed_concept = ctx.ontology_arenas().concept(seed.concept);
        let mut examine = Vec::new();
        let mut candidate_alternative_extraction = false;
        if !seed.negated && seed_concept.has_class_name() {
            candidate_alternative_extraction = seed_concept.get_operator_code() == CCEQ;
            examine.extend(
                seed_concept
                    .get_operand_list()
                    .iter()
                    .map(|operand| (operand.target, operand.negated)),
            );
        } else {
            examine.push((seed.concept, seed.negated));
        }

        // Source-mode concepts can contain cyclic auxiliary definitions. The
        // C++ construction records processed concepts in its preprocessing
        // items; the compact Rust traversal must do the same explicitly.
        // Re-examining a signed concept cannot add information here: seed and
        // invalid-special insertion are both idempotent set operations.
        let mut examined = std::collections::HashSet::new();
        let mut cursor = 0usize;
        while cursor < examine.len() {
            let (concept, negated) = examine[cursor];
            cursor += 1;
            if !examined.insert((concept, negated)) {
                continue;
            }
            if cursor & 0x3ff == 0
                && deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline)
            {
                return false;
            }
            let data = ctx.ontology_arenas().concept(concept);
            let op_code = data.get_operator_code();
            let operands = data.get_operand_list().to_vec();
            let op_count = operands.len();

            if (!negated && (op_code == CCAND || op_code == CCOR && op_count == 1))
                || (negated && (op_code == CCOR || op_code == CCAND && op_count == 1))
            {
                examine.extend(
                    operands
                        .iter()
                        .map(|operand| (operand.target, operand.negated ^ negated)),
                );
            } else if op_code == CCAQCHOOCE {
                for operand in &operands {
                    if negated == operand.negated {
                        examine.push((operand.target, operand.negated));
                    }
                    if candidate_alternative_extraction && negated != operand.negated {
                        examine.push((operand.target, !operand.negated));
                    }
                }
            } else if (negated && ((op_code == CCAND || op_code == CCEQ) && op_count > 1))
                || (!negated && op_code == CCOR)
            {
                for operand in &operands {
                    let operand_negated = operand.negated ^ negated;
                    let operand_data = ctx.ontology_arenas().concept(operand.target);
                    let mut checking_concept = operand.target;
                    let mut checking_negated = operand_negated;
                    if operand_data.get_operator_code() == CCAQCHOOCE {
                        let replacements: Vec<ConceptId> = operand_data
                            .get_operand_list()
                            .iter()
                            .filter(|nested| nested.negated == operand_negated)
                            .map(|nested| nested.target)
                            .collect();
                        if replacements.len() == 1 {
                            checking_concept = replacements[0];
                            checking_negated = false;
                        }
                    }
                    push(
                        &mut seeds,
                        &mut seed_index,
                        checking_concept,
                        checking_negated,
                        false,
                    );
                    // CTotallyPrecomputationThread cpp 1225–1227 keeps the
                    // ordinary special reference for positive named disjuncts.
                    // Only anonymous or negated checking items are invalidated.
                    if !ctx
                        .ontology_arenas()
                        .concept(checking_concept)
                        .has_class_name()
                        || checking_negated
                    {
                        invalid_special.insert((checking_concept, checking_negated));
                    }
                }
                push(&mut seeds, &mut seed_index, concept, negated, false);
                invalid_special.insert((concept, negated));
            } else if ((!negated && op_code == CCALL)
                || (negated && matches!(op_code, CCSOME | CCAQSOME)))
                && candidate_alternative_extraction
            {
                push(&mut seeds, &mut seed_index, concept, !negated, false);
                invalid_special.insert((concept, !negated));
            }
        }
    }

    // analyseConceptSaturationSubsumerExistItems, C++ 1018-1102.
    let named: std::collections::HashSet<ConceptId> = bridged.named.iter().copied().collect();
    let mut special_reference: Vec<Option<usize>> = vec![None; seeds.len()];
    let mut multiple_predecessors = vec![false; seeds.len()];
    let mut indirect_successors = vec![false; seeds.len()];
    let mut exist_references: Vec<Vec<usize>> = vec![Vec::new(); seeds.len()];
    for item in 0..seeds.len() {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return false;
        }
        let mut stack = vec![(seeds[item].concept, seeds[item].negated)];
        let mut visited = std::collections::HashSet::new();
        while let Some((concept, negated)) = stack.pop() {
            if !visited.insert((concept, negated)) {
                continue;
            }
            let con = ctx.ontology_arenas().concept(concept);
            let op_code = con.get_operator_code();
            let operands = con.get_operand_list();
            let deterministic = (!negated
                && (matches!(op_code, CCAND | CCSUB | CCEQ)
                    || op_code == CCOR && operands.len() == 1))
                || (negated
                    && (op_code == CCOR || matches!(op_code, CCAND | CCEQ) && operands.len() == 1));
            if !deterministic {
                continue;
            }
            for operand in operands {
                let operand_concept = operand.target;
                let operand_negated = operand.negated ^ negated;
                let operand_data = ctx.ontology_arenas().concept(operand_concept);
                let operand_code = operand_data.get_operator_code();
                if !operand_negated
                    && (matches!(operand_code, CCEQ | CCSUB)
                        || operand_code == CCATOM && named.contains(&operand_concept))
                {
                    if let Some(&reference) = seed_index.get(&(operand_concept, false)) {
                        indirect_successors[reference] = true;
                        if special_reference[item].is_none()
                            && !invalid_special
                                .contains(&(seeds[item].concept, seeds[item].negated))
                        {
                            special_reference[item] = Some(reference);
                        } else {
                            multiple_predecessors[item] = true;
                        }
                    }
                } else if (!operand_negated && matches!(operand_code, CCAND | CCAQAND))
                    || (operand_negated && operand_code == CCOR)
                {
                    if operand_data.get_operand_list().len() > 1 {
                        multiple_predecessors[item] = true;
                    }
                    stack.push((operand_concept, operand_negated));
                } else if (!operand_negated && matches!(operand_code, CCSOME | CCAQSOME))
                    || (operand_negated && operand_code == CCALL)
                {
                    let role = operand_data.get_role();
                    let filler = operand_data
                        .get_operand_list()
                        .first()
                        .map(|link| (link.target, link.negated ^ operand_negated))
                        .unwrap_or((top, false));
                    let reference = if roles_with_ranges.contains(&role) {
                        role_seed_index.get(&(role, filler.0, filler.1))
                    } else {
                        seed_index.get(&filler)
                    };
                    if let Some(&reference) = reference {
                        exist_references[item].push(reference);
                    }
                    multiple_predecessors[item] = true;
                } else if (!negated && operand_code == CCATLEAST)
                    || (negated && operand_code == CCATMOST)
                {
                    let role = operand_data.get_role();
                    let filler = operand_data
                        .get_operand_list()
                        .first()
                        .map(|link| (link.target, link.negated))
                        .unwrap_or((top, false));
                    let reference = if roles_with_ranges.contains(&role) {
                        role_seed_index.get(&(role, filler.0, filler.1))
                    } else {
                        seed_index.get(&filler)
                    };
                    if let Some(&reference) = reference {
                        exist_references[item].push(reference);
                    }
                    multiple_predecessors[item] = true;
                } else if operand_code == CCAQCHOOCE {
                    for nested in operand_data.get_operand_list() {
                        if operand_negated != nested.negated {
                            continue;
                        }
                        let nested_data = ctx.ontology_arenas().concept(nested.target);
                        match nested_data.get_operator_code() {
                            CCAQSOME => {
                                if let Some(filler) = nested_data.get_operand_list().first() {
                                    let role = nested_data.get_role();
                                    let reference = if roles_with_ranges.contains(&role) {
                                        role_seed_index.get(&(role, filler.target, filler.negated))
                                    } else {
                                        seed_index.get(&(filler.target, filler.negated))
                                    };
                                    if let Some(&reference) = reference {
                                        exist_references[item].push(reference);
                                    }
                                }
                                multiple_predecessors[item] = true;
                            }
                            CCAQAND => {
                                if operand_data.get_operand_list().len() > 1 {
                                    multiple_predecessors[item] = true;
                                }
                                stack.push((nested.target, false));
                            }
                            _ => {}
                        }
                    }
                } else {
                    multiple_predecessors[item] = true;
                }
            }
        }
        exist_references[item].sort_unstable();
        exist_references[item].dedup();
    }

    // C++ propagateSubsumerItemFlag / propagateExistInitializationFlag.
    for item in 0..seeds.len() {
        if item & 0x3ff == 0
            && deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline)
        {
            return false;
        }
        if indirect_successors[item] {
            let mut next = special_reference[item];
            while let Some(reference) = next {
                if indirect_successors[reference] {
                    break;
                }
                indirect_successors[reference] = true;
                next = special_reference[reference];
            }
        }
        if seeds[item].potentially_exist {
            let mut next = special_reference[item];
            while let Some(reference) = next {
                if seeds[reference].potentially_exist {
                    break;
                }
                seeds[reference].potentially_exist = true;
                next = special_reference[reference];
            }
        }
    }

    // Diagnostic ablation for comparing Konclude's tag-ordered special-reference
    // choice with a bridge build whose independently assigned concept tags choose
    // another deterministic subsumer. Format: `source-tag:reference-tag`.
    if let Ok(override_spec) = std::env::var("KM_SAT_SPECIAL_REF_OVERRIDE") {
        for pair in override_spec.split(',') {
            let Some((source, reference)) = pair.split_once(':') else {
                continue;
            };
            let (Ok(source_tag), Ok(reference_tag)) =
                (source.parse::<Cint64>(), reference.parse::<Cint64>())
            else {
                continue;
            };
            let source_item = seeds.iter().position(|seed| {
                !seed.negated
                    && ctx
                        .ontology_arenas()
                        .concept(seed.concept)
                        .get_concept_tag()
                        == source_tag
            });
            let reference_item = seeds.iter().position(|seed| {
                !seed.negated
                    && ctx
                        .ontology_arenas()
                        .concept(seed.concept)
                        .get_concept_tag()
                        == reference_tag
            });
            if let (Some(source_item), Some(reference_item)) = (source_item, reference_item) {
                special_reference[source_item] = Some(reference_item);
                multiple_predecessors[source_item] = true;
                eprintln!(
                    "SAT-SPECIAL-REF-OVERRIDE source-tag={} reference-tag={}",
                    source_tag, reference_tag,
                );
            }
        }
    }

    // Dependency-first equivalent of orderItemsSaturationTesting.
    fn order_item(
        item: usize,
        special_reference: &[Option<usize>],
        exist_references: &[Vec<usize>],
        state: &mut [u8],
        order: &mut Vec<usize>,
    ) {
        if state[item] == 2 {
            return;
        }
        if state[item] == 1 {
            return;
        }
        state[item] = 1;
        if let Some(reference) = special_reference[item] {
            order_item(reference, special_reference, exist_references, state, order);
        }
        // C++ pushes the list in forward order onto a stack, so the last
        // existential reference is ordered first.
        for &reference in exist_references[item].iter().rev() {
            order_item(reference, special_reference, exist_references, state, order);
        }
        state[item] = 2;
        order.push(item);
    }
    let mut order = Vec::with_capacity(seeds.len());
    let mut order_state = vec![0u8; seeds.len()];
    // Konclude starts with real non-existential leaves, then existential
    // leaves, and only then sweeps the remaining components.
    for item in 0..seeds.len() {
        if !indirect_successors[item] && !seeds[item].potentially_exist {
            order_item(
                item,
                &special_reference,
                &exist_references,
                &mut order_state,
                &mut order,
            );
        }
    }
    for item in 0..seeds.len() {
        if !indirect_successors[item] && seeds[item].potentially_exist {
            order_item(
                item,
                &special_reference,
                &exist_references,
                &mut order_state,
                &mut order,
            );
        }
    }
    for item in 0..seeds.len() {
        order_item(
            item,
            &special_reference,
            &exist_references,
            &mut order_state,
            &mut order,
        );
    }

    // Allocate every ontology item before wiring cross-item references.
    let mut onto_items = vec![SaturationConceptReferenceLinkingId::NONE; seeds.len()];
    for (item_index, seed) in seeds.iter().enumerate() {
        if item_index & 0x3ff == 0
            && deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline)
        {
            return false;
        }
        let concept = seed.concept;
        let negation = seed.negated;
        if seed.role_ranges.is_some() {
            // `getSaturationRoleSuccessorConceptDataItem` stores this item in
            // the role/concept/negation hash only. It must not occupy the
            // filler's ordinary positive/negative reference slot.
            let onto_item = {
                let arenas = ctx.ontology_arenas_mut();
                let mut item = SaturationConceptReferenceLinking::new();
                item.init_concept_saturation_testing_item(concept, negation, seed.role_ranges);
                item.set_potentially_exist_initialization_concept(seed.potentially_exist);
                if arenas.role(seed.role_ranges).is_data_role() {
                    item.set_data_range_concept(true);
                }
                arenas.alloc_saturation_concept_reference_linking(item)
            };
            onto_items[item_index] = onto_item;
            continue;
        }
        // Ensure the concept's process data + saturation reference-linking data.
        let con_proc_data = {
            let concept_data = ctx.ontology_arenas().concept(concept).get_concept_data();
            if concept_data == super::model::substrate::INVALID {
                let arenas = ctx.ontology_arenas_mut();
                let fresh = arenas.alloc_concept_process_data(ConceptProcessData::new());
                arenas.concept_mut(concept).set_concept_data(fresh.raw);
                fresh
            } else {
                super::model::concept_process::ConceptProcessDataId::new(concept_data)
            }
        };
        let mut ref_linking_data = ctx
            .ontology_arenas()
            .concept_process_data(con_proc_data)
            .get_concept_reference_linking();
        if ref_linking_data.is_none() {
            let arenas = ctx.ontology_arenas_mut();
            ref_linking_data = arenas.alloc_concept_saturation_reference_linking_data(
                ConceptSaturationReferenceLinkingData::new(),
            );
            arenas
                .concept_process_data_mut(con_proc_data)
                .set_concept_reference_linking(ref_linking_data);
        }
        // One item per (concept, polarity): skip if already wired.
        let existing = ctx
            .ontology_arenas()
            .concept_saturation_reference_linking_data(ref_linking_data)
            .get_concept_saturation_reference_linking_data(negation);
        if existing.is_some() {
            onto_items[item_index] = existing;
            continue;
        }
        // Ontology-side item (CSaturationConceptDataItem).
        let onto_item = {
            let arenas = ctx.ontology_arenas_mut();
            let mut item = SaturationConceptReferenceLinking::new();
            item.init_concept_saturation_testing_item(concept, negation, RoleId::NONE);
            item.set_potentially_exist_initialization_concept(seed.potentially_exist);
            let onto_item = arenas.alloc_saturation_concept_reference_linking(item);
            arenas
                .concept_saturation_reference_linking_data_mut(ref_linking_data)
                .set_saturation_reference_linking_data(onto_item, negation);
            onto_item
        };
        onto_items[item_index] = onto_item;
    }

    // Wire each restriction to the role-specific item before any saturation
    // node is constructed. This is the exact reference read first by
    // `createSuccessorForConcept`; ordinary filler lookup remains its fallback.
    for (restriction, item_index) in existential_successor_seed {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return false;
        }
        if item_index == usize::MAX || onto_items[item_index].is_none() {
            continue;
        }
        let con_proc_data = {
            let concept_data = ctx
                .ontology_arenas()
                .concept(restriction)
                .get_concept_data();
            if concept_data == super::model::substrate::INVALID {
                let arenas = ctx.ontology_arenas_mut();
                let fresh = arenas.alloc_concept_process_data(ConceptProcessData::new());
                arenas.concept_mut(restriction).set_concept_data(fresh.raw);
                fresh
            } else {
                super::model::concept_process::ConceptProcessDataId::new(concept_data)
            }
        };
        let mut ref_linking_data = ctx
            .ontology_arenas()
            .concept_process_data(con_proc_data)
            .get_concept_reference_linking();
        if ref_linking_data.is_none() {
            let arenas = ctx.ontology_arenas_mut();
            ref_linking_data = arenas.alloc_concept_saturation_reference_linking_data(
                ConceptSaturationReferenceLinkingData::new(),
            );
            arenas
                .concept_process_data_mut(con_proc_data)
                .set_concept_reference_linking(ref_linking_data);
        }
        let current = ctx
            .ontology_arenas()
            .concept_saturation_reference_linking_data(ref_linking_data)
            .get_existential_successor_concept_saturation_reference_linking_data();
        if current.is_none() {
            ctx.ontology_arenas_mut()
                .concept_saturation_reference_linking_data_mut(ref_linking_data)
                .set_existential_successor_concept_saturation_reference_linking_data(
                    onto_items[item_index],
                );
        }
    }

    // Reference mode, C++ 2190-2205. Trigger-host concepts conservatively use
    // COPY, matching the triggerImpHash guard in Konclude.
    for item in 0..seeds.len() {
        if item & 0x3ff == 0
            && deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline)
        {
            return false;
        }
        let Some(reference) = special_reference[item] else {
            continue;
        };
        let contains_trigger = ctx
            .ontology_arenas()
            .concept(seeds[item].concept)
            .get_operand_list()
            .iter()
            .any(|operand| {
                ctx.ontology_arenas()
                    .concept(operand.target)
                    .get_operator_code()
                    == CCIMPLTRIG
            });
        let mode = if !seeds[item].potentially_exist
            && !multiple_predecessors[item]
            && !contains_trigger
        {
            SATURATION_SUBSTITUTE_MODE
        } else {
            SATURATION_COPY_MODE
        };
        ctx.ontology_arenas_mut()
            .saturation_concept_reference_linking_mut(onto_items[item])
            .set_special_item_reference(onto_items[reference])
            .set_special_item_reference_mode(mode);
    }

    // Generator construction loop. Build all nodes first, then queue them in
    // dependency order; databox insertion is head-first, hence reverse insert.
    // Konclude starts concept-test ids strictly above the ABox vector's next
    // individual id. Sharing ids would overwrite a representative node in the
    // saturation vector and make cache labels depend on construction order.
    let mut next_indi_id: Cint64 = bridged
        .nominal_seeds
        .iter()
        .map(|seed| seed.individual_tag)
        .max()
        .map_or(1, |max_tag| max_tag.saturating_add(1).max(1));
    let mut linkers = vec![IndividualSaturationProcessNodeLinkerId::NONE; seeds.len()];
    // `extendApproximatedSaturationCalculationJobConstruction` prepends each
    // construct. The task generator therefore allocates nodes in reverse
    // ordered-item order, giving referenced dependencies larger individual
    // IDs. Successor-extension processing is keyed by negative individual ID,
    // so this reversal is required to process dependencies before dependents.
    for &item_index in order.iter().rev() {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return false;
        }
        let seed = seeds[item_index];
        let concept = seed.concept;
        let negation = seed.negated;
        let onto_item = onto_items[item_index];
        // Process-side item mirror + the node (generator cpp 108–135).
        let ext_item = {
            let mut ext = ExtendedConceptReferenceLinkingData::new();
            ext.init_concept_saturation_testing_item(concept, negation, seed.role_ranges);
            ext.set_concept_reference_linking(onto_item.raw);
            ctx.process_context_mut()
                .alloc_extended_con_ref_linking_data(ext)
        };
        let individual_id = next_indi_id;
        next_indi_id += 1;
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(
                super::model::substrate::INVALID,
            ));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .init_individual_saturation_process_node(individual_id, ext_item, Id::NONE);
        ctx.ontology_arenas_mut()
            .saturation_concept_reference_linking_mut(onto_item)
            .set_individual_process_node_for_concept(node);
        ctx.processing_data_box_mut()
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields CIndividualSaturationProcessNodeVector")
            .set_data(individual_id, node);
        // indiProcNodeLinker: initProcessNodeLinker(node, processing=true) +
        // dataBox->addIndividualSaturationProcessNodeLinker (generator cpp 129–134).
        let linker = ctx
            .process_context_mut()
            .sat_node_individual_saturation_process_node_linker(node, true);
        ctx.process_context_mut()
            .indi_sat_process_node_linker_mut(linker)
            .set_processing_queued(true);
        linkers[item_index] = linker;
    }
    // The generator also prepends each allocated linker to the processing
    // list. Adding the reverse construction sequence reproduces the final
    // dependency-first list.
    for &item_index in order.iter().rev() {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return false;
        }
        ctx.processing_data_box_mut()
            .add_individual_saturation_process_node_linker(linkers[item_index]);
    }
    if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
        let substitute_count = (0..seeds.len())
            .filter(|&item| {
                ctx.ontology_arenas()
                    .saturation_concept_reference_linking(onto_items[item])
                    .get_special_reference_mode()
                    == SATURATION_SUBSTITUTE_MODE
            })
            .count();
        let copy_count = (0..seeds.len())
            .filter(|&item| {
                ctx.ontology_arenas()
                    .saturation_concept_reference_linking(onto_items[item])
                    .get_special_reference_mode()
                    == SATURATION_COPY_MODE
            })
            .count();
        eprintln!(
            "BRIDGE-SATURATION-SEEDS: base={} extended={} invalid-special={} substitute={} copy={}",
            base_seed_count,
            seeds.len(),
            invalid_special.len(),
            substitute_count,
            copy_count,
        );
    }
    true
}

/// Construct Konclude's second saturation wave: one separated representative
/// node for every ABox individual, using the individual's real id. Positive
/// object-property assertions are installed as named-to-named role links; the
/// completion-only `exists R.{b}` spelling is deliberately not seeded here.
fn build_native_abox_saturation_seeds(
    _sat_algo: &mut super::saturation::algorithm::SaturationTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    deadline: Option<std::time::Instant>,
) -> Option<Vec<(Cint64, super::process::SatNodeId)>> {
    use super::process::sat_node::IndividualSaturationProcessNode;

    let mut nodes = Vec::with_capacity(bridged.nominal_seeds.len());
    let mut by_tag = HashMap::with_capacity(bridged.nominal_seeds.len());
    let mut linkers = Vec::with_capacity(bridged.nominal_seeds.len());
    for seed in &bridged.nominal_seeds {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return None;
        }
        let occupied = ctx
            .processing_data_box()
            .individual_saturation_process_node_vector_ref()
            .is_some_and(|vector| vector.has_data(seed.individual_tag));
        if occupied {
            return None;
        }
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .init_individual_saturation_process_node(seed.individual_tag, Id::NONE, Id::NONE)
            .set_nominal_individual(seed.individual)
            .set_separated(true)
            .set_abox_individual_representation_node(true);
        ctx.processing_data_box_mut()
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields a saturation-node vector")
            .set_data(seed.individual_tag, node);
        let linker = ctx
            .process_context_mut()
            .sat_node_individual_saturation_process_node_linker(node, true);
        ctx.process_context_mut()
            .indi_sat_process_node_linker_mut(linker)
            .set_processing_queued(true);
        nodes.push((seed.individual_tag, node));
        by_tag.insert(seed.individual_tag, node);
        linkers.push(linker);
    }

    // Stage each forward edge and reverse face once all named representatives
    // exist. `initialize_role_assertions` consumes this typed journal only
    // after `initialize_initialization_concepts` has copied the named
    // assertion-resolved label, matching Konclude's exact initialization
    // order. Installing the semantic link here would add domain/range concepts
    // to the old label and the subsequent representative copy would erase
    // them.
    for seed in &bridged.nominal_seeds {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return None;
        }
        let source = *by_tag.get(&seed.individual_tag)?;
        for &(role, target_tag) in &seed.role_assertions {
            if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
                return None;
            }
            let target = *by_tag.get(&target_tag)?;
            ctx.process_context_mut()
                .sat_node_ext_add_role_assertion(source, target, role, false);
            ctx.process_context_mut()
                .sat_node_ext_add_role_assertion(target, source, role, true);
        }
    }

    // ProcessingDataBox stores the C++ head at the Vec tail. Reverse insertion
    // makes the ascending individual order the actual processing order.
    for linker in linkers.into_iter().rev() {
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            return None;
        }
        ctx.processing_data_box_mut()
            .add_individual_saturation_process_node_linker(linker);
    }
    Some(nodes)
}

fn native_cache_label_concepts(
    ctx: &CalculationAlgorithmContextBase,
    node: super::process::SatNodeId,
) -> Option<Vec<(ConceptId, bool)>> {
    let label = ctx
        .process_context()
        .sat_node(node)
        .reapply_con_sat_label_set;
    if label.is_none() {
        return Some(Vec::new());
    }
    let mut concepts = Vec::new();
    let mut descriptor = ctx
        .process_context()
        .reapply_con_sat_label_set(label)
        .get_concept_saturation_description_linker();
    let mut walked = 0usize;
    while descriptor.is_some() {
        if descriptor.index() >= ctx.process_context().con_sat_desc_count()
            || walked > ctx.process_context().con_sat_desc_count()
        {
            return None;
        }
        let data = ctx.process_context().con_sat_desc(descriptor);
        concepts.push((data.get_concept(), data.get_negation()));
        descriptor = data.get_next_concept_desciptor();
        walked += 1;
    }
    concepts.sort_unstable_by_key(|(concept, negated)| (concept.raw, *negated));
    concepts.dedup();
    Some(concepts)
}

fn native_individual_label_identity(values: &[Cint64]) -> u64 {
    // Stable FNV-1a over canonical signed ids. The reuse gate also compares the
    // full vectors, so this identifier supplies Konclude's canonical-label
    // identity metadata without making correctness depend on hash collision.
    let mut hash = 0xcbf29ce484222325u64;
    for value in values {
        for byte in value.to_le_bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    hash
}

/// Write the bridge-local typed equivalent of Konclude's representative
/// backend association. Every label family used by the completion read path is
/// materialised, even when the entry is explicitly marked insufficient.
fn write_native_abox_representative_cache(
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    nodes: &[(Cint64, super::process::SatNodeId)],
) -> Option<NativeAboxRepresentativeCache> {
    use super::model::op::{
        CCALL, CCAQALL, CCAQSOME, CCATLEAST, CCATMOST, CCSELF, CCSOME, CCVALUE,
    };
    use super::process::sat_node::IndividualSaturationProcessNodeStatusFlags as F;

    if nodes.len() != bridged.nominal_seeds.len() {
        return None;
    }
    let mut cache = NativeAboxRepresentativeCache::default();
    for &(individual_tag, node) in nodes {
        if node.is_none() || node.index() >= ctx.process_context().sat_node_count() {
            return None;
        }
        let (direct_flags, indirect_flags) = {
            let saturation_node = ctx.process_context().sat_node(node);
            (
                saturation_node.direct_status_flags.get_flags(),
                saturation_node.indirect_status_flags.get_flags(),
            )
        };
        if direct_flags & F::INDSATFLAGCLASHED != 0 || indirect_flags & F::INDSATFLAGCLASHED != 0 {
            cache.entries.clear();
            cache.association_write_aborted = true;
            return Some(cache);
        }

        let concepts = native_cache_label_concepts(ctx, node)?;
        let mut existential_roles: BTreeSet<Cint64> = BTreeSet::new();
        let mut existential_max: BTreeMap<Cint64, Cint64> = BTreeMap::new();
        let mut at_most: BTreeMap<Cint64, Cint64> = BTreeMap::new();
        for &(concept, negated) in &concepts {
            if concept.is_none()
                || concept.index() >= ctx.ontology_arenas().concept_count() as usize
            {
                return None;
            }
            let concept_ref = ctx.ontology_arenas().concept(concept);
            let operator = concept_ref.get_operator_code();
            let role = concept_ref.get_role();
            if role.is_some()
                && ((!negated
                    && matches!(operator, CCSOME | CCAQSOME | CCVALUE | CCSELF | CCATLEAST))
                    || (negated && matches!(operator, CCALL | CCAQALL | CCATMOST)))
            {
                existential_roles.insert(role.raw);
                let cardinality = if (!negated
                    && matches!(operator, CCSOME | CCAQSOME | CCVALUE | CCSELF))
                    || (negated && matches!(operator, CCALL | CCAQALL))
                {
                    1
                } else if !negated && operator == CCATLEAST {
                    concept_ref.get_parameter().max(0)
                } else {
                    concept_ref.get_parameter().saturating_add(1).max(0)
                };
                existential_max
                    .entry(role.raw)
                    .and_modify(|current| *current = (*current).max(cardinality))
                    .or_insert(cardinality);
            }
            let bound = if !negated && operator == CCATMOST {
                Some(concept_ref.get_parameter())
            } else if negated && operator == CCATLEAST {
                Some(concept_ref.get_parameter().saturating_sub(1))
            } else {
                None
            };
            if let (Some(bound), true) = (bound, role.is_some()) {
                at_most
                    .entry(role.raw)
                    .and_modify(|current| *current = (*current).min(bound))
                    .or_insert(bound);
            }
        }

        let mut instantiated_role_orientations: BTreeSet<(Cint64, bool)> = BTreeSet::new();
        let mut neighbour_roles: BTreeMap<Cint64, BTreeSet<(Cint64, bool)>> = BTreeMap::new();
        let mut indirect_nominals: BTreeSet<Cint64> = ctx
            .process_context_mut()
            .sat_node_successor_connected_nominals(node)
            .into_iter()
            .collect();
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, false);
        if linked_hash.is_some() {
            let role_buckets: Vec<(RoleId, _)> = ctx
                .process_context()
                .linked_role_sat_succ_hash(linked_hash)
                .get_linked_role_successor_hash()
                .iter()
                .map(|(&role, &data)| (role, data))
                .collect();
            for (role, bucket) in role_buckets {
                let successors: Vec<_> = ctx
                    .process_context()
                    .linked_role_sat_succ_data(bucket)
                    .get_successor_node_data_map()
                    .values()
                    .copied()
                    .collect();
                let mut role_instantiated = false;
                for successor in successors {
                    if successor.is_none()
                        || successor.index() >= ctx.process_context().sat_succ_data_count()
                    {
                        return None;
                    }
                    let successor_data = ctx.process_context().sat_succ_data(successor);
                    if !successor_data.is_active() {
                        continue;
                    }
                    role_instantiated = true;
                    let mut neighbour_tag = if successor_data.value_nominal_connection {
                        indirect_nominals.insert(successor_data.value_nominal_id);
                        Some(successor_data.value_nominal_id)
                    } else {
                        None
                    };
                    if neighbour_tag.is_none()
                        && successor_data.succ_indi_node.is_some()
                        && successor_data.succ_indi_node.index()
                            < ctx.process_context().sat_node_count()
                    {
                        let successor_node = ctx
                            .process_context()
                            .sat_node(successor_data.succ_indi_node);
                        let nominal = successor_node.get_nominal_individual();
                        neighbour_tag = if nominal.is_some()
                            && nominal.index() < ctx.ontology_arenas().individual_count() as usize
                        {
                            Some(
                                ctx.ontology_arenas()
                                    .individual(nominal)
                                    .get_individual_id(),
                            )
                        } else {
                            // An existential whose filler is `{a}` points at a
                            // concept-saturation node rather than the ABox
                            // representative. Recover the nominal id from that
                            // node's label. The association status remains the
                            // exact direct/indirect saturation-status test
                            // below; this metadata shape is not an additional
                            // insufficiency condition in Konclude.
                            let label = successor_node.reapply_con_sat_label_set;
                            let mut inferred_nominal = None;
                            if label.is_some() {
                                let mut descriptor = ctx
                                    .process_context()
                                    .reapply_con_sat_label_set(label)
                                    .get_concept_saturation_description_linker();
                                let mut walked = 0usize;
                                while descriptor.is_some()
                                    && descriptor.index()
                                        < ctx.process_context().con_sat_desc_count()
                                    && walked <= ctx.process_context().con_sat_desc_count()
                                {
                                    let descriptor_ref =
                                        ctx.process_context().con_sat_desc(descriptor);
                                    let candidate = descriptor_ref.get_concept();
                                    if !descriptor_ref.get_negation()
                                        && candidate.is_some()
                                        && candidate.index()
                                            < ctx.ontology_arenas().concept_count() as usize
                                        && ctx
                                            .ontology_arenas()
                                            .concept(candidate)
                                            .get_operator_code()
                                            == op::CCNOMINAL
                                    {
                                        let individual = ctx
                                            .ontology_arenas()
                                            .concept(candidate)
                                            .get_nominal_individual();
                                        if individual.is_some()
                                            && individual.index()
                                                < ctx.ontology_arenas().individual_count() as usize
                                        {
                                            inferred_nominal = Some(
                                                ctx.ontology_arenas()
                                                    .individual(individual)
                                                    .get_individual_id(),
                                            );
                                            break;
                                        }
                                    }
                                    descriptor = descriptor_ref.get_next_concept_desciptor();
                                    walked += 1;
                                }
                            }
                            if let Some(nominal_tag) = inferred_nominal {
                                indirect_nominals.insert(nominal_tag);
                                Some(nominal_tag)
                            } else {
                                Some(successor_node.get_individual_id())
                            }
                        };
                    }
                    if let Some(neighbour_tag) = neighbour_tag {
                        neighbour_roles
                            .entry(neighbour_tag)
                            .or_default()
                            .insert((role.raw, false));
                    }
                }
                if role_instantiated {
                    instantiated_role_orientations.insert((role.raw, false));
                }
            }
        }

        // Konclude's association writer consumes both assertion linkers on an
        // ontology individual. The saturation successor hash above contains
        // only links oriented out of this representative, so it cannot by
        // itself serialize the reverse linker on an assertion target. Replay
        // the immutable typed ABox journal in both directions, including every
        // indirect super-role orientation installed by `addRoleAssertion`.
        // These are asserted links and therefore deterministic; model-choice
        // links remain exclusively on the completion writeback path below.
        for source_seed in &bridged.nominal_seeds {
            for &(asserted_role, target_tag) in &source_seed.role_assertions {
                if asserted_role.is_none()
                    || asserted_role.index() >= ctx.ontology_arenas().role_count() as usize
                {
                    return None;
                }
                let mut super_roles = ctx
                    .ontology_arenas()
                    .role(asserted_role)
                    .get_indirect_super_role_list()
                    .to_vec();
                if !super_roles
                    .iter()
                    .any(|link| link.target == asserted_role && !link.negated)
                {
                    super_roles.push(NegLink {
                        target: asserted_role,
                        negated: false,
                    });
                }
                for role_link in super_roles {
                    let role = role_link.target;
                    if role.is_none() || role.index() >= ctx.ontology_arenas().role_count() as usize
                    {
                        return None;
                    }
                    if individual_tag == source_seed.individual_tag {
                        instantiated_role_orientations.insert((role.raw, role_link.negated));
                        indirect_nominals.insert(target_tag);
                        neighbour_roles
                            .entry(target_tag)
                            .or_default()
                            .insert((role.raw, role_link.negated));
                    }
                    if individual_tag == target_tag {
                        instantiated_role_orientations.insert((role.raw, !role_link.negated));
                        indirect_nominals.insert(source_seed.individual_tag);
                        neighbour_roles
                            .entry(source_seed.individual_tag)
                            .or_default()
                            .insert((role.raw, !role_link.negated));
                    }
                }
            }
        }

        let (completely_handled, completely_propagated) =
            native_abox_association_status(direct_flags, indirect_flags);
        let status_incomplete = !completely_handled;
        // The saturation substrate does not retain per-descriptor dependency
        // track points. Only a completely handled association certifies its
        // final label. Values from an insufficient association remain
        // metadata and must not be replayed as branch-zero facts.
        let concept_values = concepts
            .iter()
            .map(|&(concept, negated)| NativeAboxConceptValue {
                concept,
                negated,
                deterministic: completely_handled,
            })
            .collect();
        let deterministic_same_individuals = Vec::new();
        let deterministic_same_label_identity =
            native_individual_label_identity(&deterministic_same_individuals);
        let mut deterministic_different_individuals: Vec<Cint64> = bridged
            .nominal_different
            .iter()
            .filter_map(|&(left, right)| {
                if left == individual_tag {
                    Some(right)
                } else if right == individual_tag {
                    Some(left)
                } else {
                    None
                }
            })
            .collect();
        if !deterministic_different_individuals.is_empty() {
            deterministic_different_individuals.push(individual_tag);
            deterministic_different_individuals.sort_unstable();
            deterministic_different_individuals.dedup();
        }
        cache.next_association_update_id = cache.next_association_update_id.saturating_add(1);
        let instantiated_role_values: Vec<NativeAboxRoleValue> =
            instantiated_role_orientations
                .into_iter()
                .map(|(role, inversed)| NativeAboxRoleValue {
                    role: RoleId::new(role),
                    inversed,
                    deterministic: true,
                })
                .collect();
        let instantiated_roles: Vec<RoleId> = instantiated_role_values
            .iter()
            .map(|value| value.role)
            .collect();
        let existential_roles: Vec<RoleId> =
            existential_roles.into_iter().map(RoleId::new).collect();
        let entry = NativeAboxRepresentativeEntry {
            individual_tag,
            concepts,
            concept_values: Some(concept_values),
            instantiated_role_values: Some(instantiated_role_values),
            instantiated_roles,
            existential_role_values: Some(
                existential_roles
                    .iter()
                    .map(|&role| NativeAboxRoleValue {
                        role,
                        inversed: false,
                        deterministic: true,
                    })
                    .collect(),
            ),
            existential_roles,
            at_most_cardinalities: at_most
                .into_iter()
                .map(|(role, cardinality)| (RoleId::new(role), cardinality))
                .collect(),
            existential_max_cardinalities: existential_max
                .into_iter()
                .map(|(role, cardinality)| (RoleId::new(role), cardinality))
                .collect(),
            indirect_nominal_connections: indirect_nominals.into_iter().collect(),
            neighbour_role_combinations: neighbour_roles
                .into_iter()
                .map(|(neighbour_tag, roles)| NativeAboxNeighbourRoleSet {
                    neighbour_tag,
                    roles: roles
                        .into_iter()
                        .map(|(role, inversed)| (RoleId::new(role), inversed))
                        .collect(),
                    role_values: None,
                    merged_alias_deterministic: Some(true),
                })
                .collect(),
            completely_saturated: completely_handled,
            completely_handled,
            completely_propagated,
            insufficient: status_incomplete,
            representative_same_individual_merging: Some(false),
            deterministic_same_individual_label_identity: Some(deterministic_same_label_identity),
            deterministic_merged_same_considered_label_identity: Some(
                deterministic_same_label_identity,
            ),
            deterministic_same_individuals: Some(deterministic_same_individuals.clone()),
            deterministic_merged_same_considered_individuals: Some(deterministic_same_individuals),
            nondeterministic_same_individuals: Some(Vec::new()),
            deterministic_different_individuals: Some(deterministic_different_individuals.clone()),
            nondeterministic_different_individuals: Some(deterministic_different_individuals),
            representative_same_individual_id: Some(individual_tag),
            deterministic_same_individual_id: Some(individual_tag),
            completion_processing_restriction_flags: None,
            completion_label_descriptor_count: None,
            association_update_id: cache.next_association_update_id,
            used_association_update_id: None,
            scheduled_individual: None,
            association_origin: Some(NativeAboxAssociationOrigin::IndividualSaturation),
            merge_identity_metadata_complete: true,
            role_metadata_complete: true,
            synchronization_metadata_complete: true,
        };
        let mut entry = entry;
        for combination in &mut entry.neighbour_role_combinations {
            combination.role_values = Some(
                combination
                    .roles
                    .iter()
                    .map(|&(role, inversed)| NativeAboxRoleValue {
                        role,
                        inversed,
                        deterministic: true,
                    })
                    .collect(),
            );
        }
        cache.entries.insert(individual_tag, entry);
    }
    Some(cache)
}

fn native_cache_entry_covers_seed(
    entry: &NativeAboxRepresentativeEntry,
    seed: &NominalSeed,
) -> bool {
    let sorted_roles = |roles: &[RoleId]| {
        roles.iter().all(|role| role.is_some())
            // The same role may occur once in each orientation. The typed
            // values below carry that polarity, while Konclude's combined
            // role-set projection retains the repeated role id.
            && roles.windows(2).all(|pair| pair[0].raw <= pair[1].raw)
    };
    let sorted_cardinalities = entry
        .at_most_cardinalities
        .iter()
        .all(|(role, _)| role.is_some())
        && entry
            .at_most_cardinalities
            .windows(2)
            .all(|pair| pair[0].0.raw < pair[1].0.raw);
    let sorted_existential_cardinalities = entry
        .existential_max_cardinalities
        .iter()
        .all(|(role, cardinality)| role.is_some() && *cardinality >= 0)
        && entry
            .existential_max_cardinalities
            .windows(2)
            .all(|pair| pair[0].0.raw < pair[1].0.raw);
    let sorted_indirect_nominals = entry
        .indirect_nominal_connections
        .windows(2)
        .all(|pair| pair[0] < pair[1]);
    let neighbour_roles_well_formed = entry.neighbour_role_combinations.iter().all(|combination| {
        let role_values_well_formed = combination.role_values.as_ref().is_some_and(|values| {
            values.windows(2).all(|pair| {
                (pair[0].role.raw, pair[0].inversed, pair[0].deterministic)
                    < (pair[1].role.raw, pair[1].inversed, pair[1].deterministic)
            }) && values
                .iter()
                .map(|value| (value.role, value.inversed))
                .collect::<Vec<_>>()
                == combination.roles
        });
        let merge_alias_well_formed =
            combination
                .merged_alias_deterministic
                .is_some_and(|deterministic| {
                    deterministic
                        || combination
                            .role_values
                            .as_ref()
                            .is_some_and(|values| values.iter().all(|value| !value.deterministic))
                });
        role_values_well_formed
            && merge_alias_well_formed
            && combination
                .roles
                .iter()
                .all(|(role, _)| role.is_some() && entry.instantiated_roles.contains(role))
            && combination
                .roles
                .windows(2)
                .all(|pair| (pair[0].0.raw, pair[0].1) < (pair[1].0.raw, pair[1].1))
    });
    let concept_values_well_formed = entry.concept_values.as_ref().is_some_and(|values| {
        values.windows(2).all(|pair| {
            (pair[0].concept.raw, pair[0].negated, pair[0].deterministic)
                < (pair[1].concept.raw, pair[1].negated, pair[1].deterministic)
        }) && values
            .iter()
            .map(|value| (value.concept, value.negated))
            .collect::<Vec<_>>()
            == entry.concepts
    });
    let role_values_well_formed = |roles: &[RoleId], values: &Option<Vec<NativeAboxRoleValue>>| {
        values.as_ref().is_some_and(|values| {
            values.windows(2).all(|pair| {
                (pair[0].role.raw, pair[0].inversed, pair[0].deterministic)
                    < (pair[1].role.raw, pair[1].inversed, pair[1].deterministic)
            }) && values.iter().map(|value| value.role).collect::<Vec<_>>() == roles
        })
    };

    let asserted_roles_covered = seed.role_assertions.iter().all(|&(role, target_tag)| {
        entry
            .neighbour_role_combinations
            .iter()
            .find(|combination| combination.neighbour_tag == target_tag)
            .is_some_and(|combination| combination.roles.contains(&(role, false)))
    });
    entry.individual_tag == seed.individual_tag
        && concept_values_well_formed
        && sorted_roles(&entry.instantiated_roles)
        && sorted_roles(&entry.existential_roles)
        && role_values_well_formed(&entry.instantiated_roles, &entry.instantiated_role_values)
        && role_values_well_formed(&entry.existential_roles, &entry.existential_role_values)
        && sorted_cardinalities
        && sorted_existential_cardinalities
        && sorted_indirect_nominals
        && neighbour_roles_well_formed
        && entry.representative_same_individual_id.is_some()
        && entry.deterministic_same_individual_id.is_some()
        && asserted_roles_covered
}

fn native_generated_role_assertion_synchronized(
    ctx: &CalculationAlgorithmContextBase,
    bridged: &Bridged,
    seed: &NominalSeed,
    entry: &NativeAboxRepresentativeEntry,
    concept: ConceptId,
    negated: bool,
) -> bool {
    if negated
        || concept.is_none()
        || concept.index() >= ctx.ontology_arenas().concept_count() as usize
    {
        return false;
    }
    let concept_ref = ctx.ontology_arenas().concept(concept);
    if concept_ref.get_operator_code() != op::CCSOME || concept_ref.get_operand_count() != 1 {
        return false;
    }
    let role = concept_ref.get_role();
    let Some(filler) = concept_ref.get_operand_list().first() else {
        return false;
    };
    if filler.negated {
        return false;
    }
    let Some(target) = bridged
        .nominal_seeds
        .iter()
        .find(|target| target.nominal_concept == filler.target)
    else {
        return false;
    };
    seed.role_assertions
        .contains(&(role, target.individual_tag))
        && entry
            .neighbour_role_combinations
            .iter()
            .find(|combination| combination.neighbour_tag == target.individual_tag)
            .is_some_and(|combination| combination.roles.contains(&(role, false)))
}

/// Exact concept-label conjunct of
/// `testIndividualNodeBackendCacheConceptsSynchronization` for a saturation
/// written representative entry. Saturation's FULL_CONCEPT_SET label contains
/// deterministic cache values, so a newly added non-deterministic descriptor
/// does not equal that cached value and must invalidate synchronization.
fn native_backend_concepts_synchronized(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    seed: &NominalSeed,
    node: NodeId,
    entry: &NativeAboxRepresentativeEntry,
) -> bool {
    if !entry.completely_handled
        || node.is_none()
        || node.index() >= ctx.process_context().node_count()
    {
        return false;
    }
    let label = ctx.process_context().node(node).reapply_con_label_set;
    if label.is_none() {
        return false;
    }
    let mut descriptor = ctx
        .process_context()
        .label_set(label)
        .get_adding_sorted_concept_description_linker();
    let mut walked = 0usize;
    while descriptor.is_some() {
        if descriptor.index() >= ctx.process_context().con_desc_count()
            || walked > ctx.process_context().con_desc_count()
        {
            return false;
        }
        let (concept, negated, dependency_track_point, next) = {
            let descriptor_ref = ctx.process_context().con_desc(descriptor);
            (
                descriptor_ref.get_concept(),
                descriptor_ref.is_negated(),
                descriptor_ref.get_dependency_track_point(),
                descriptor_ref.get_next_concept_descriptor(),
            )
        };
        // Konclude excludes exactly the positive own nominal descriptor.
        if concept != seed.nominal_concept || negated {
            let nondeterministic =
                algo.has_nondeterministic_dependency(dependency_track_point, ctx);
            let cached = entry.concept_values.as_ref().is_some_and(|values| {
                values
                    .binary_search_by_key(&(concept.raw, negated, !nondeterministic), |value| {
                        (value.concept.raw, value.negated, value.deterministic)
                    })
                    .is_ok()
            });
            if !cached
                && !native_generated_role_assertion_synchronized(
                    ctx, bridged, seed, entry, concept, negated,
                )
            {
                return false;
            }
        }
        descriptor = next;
        walked += 1;
    }
    true
}

/// Bridge-local port of
/// `tryEstablishExpansionBlockingWithBackendCacheSynchronisation` (cpp 22554–22578).
///
/// The generic u20 routine bottoms out in the unported representative-memory
/// association; this route carries every Konclude predicate in the typed
/// native-ABox association and reproduces the C++ split exactly:
///
/// ```text
/// if (assocData) {
///   backendExpBlocking = assocData->isCompletelyHandled()
///                        && !assocData->hasRepresentativeSameIndividualMerging();
///   if (backendExpBlocking && getDeterministicMergedSameConsideredLabelCacheEntry()
///          != getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL))
///     backendExpBlocking = false;
///   if (backendExpBlocking && testIndividualNodeBackendCacheConceptsSynchronization(...)) {
///     if (!PRFINVALIDBLOCKINGORCACHING && mConfAllowBackendSuccessorExpansionBlocking)
///       add(PRFSYNCHRONIZEDBACKEND | …SUCCESSOREXPANSIONBLOCKED | …INDIRECTNOMINALEXPANSIONBLOCKED);
///     expansionBlocked = true;
///   }
///   if (mConfAllowBackendNeighbourExpansionBlocking)
///     add(PRFSYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
///         | PRFRETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED);
/// }
/// ```
///
/// so the INDEPENDENT neighbour block plus its retest flag are installed for ANY
/// association (`reusable_for_full_completion()` / concept synchronization gate
/// only the stronger successor + indirect-nominal block), and the returned
/// `expansionBlocked` still reports only the strong block.
fn try_establish_native_backend_expansion_blocking(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    seed: &NominalSeed,
    node: NodeId,
) -> bool {
    if node.is_none()
        || node.index() >= ctx.process_context().node_count()
        || !ctx
            .process_context()
            .node(node)
            .is_nominal_individual_representative_backend_data_loaded()
    {
        return false;
    }
    // `if (assocData)` — the typed association must additionally COVER the seed's
    // asserted edges to stand in for the raw assertion linkers (see
    // `neighbour_expansion_blocking_candidate`).
    let entry = {
        let cache = bridged.native_representative_cache.borrow();
        let Some(cache) = cache.as_ref() else {
            return false;
        };
        if cache.association_write_aborted {
            return false;
        }
        let Some(entry) = cache.entries.get(&seed.individual_tag) else {
            return false;
        };
        if !native_cache_entry_covers_seed(entry, seed) {
            return false;
        }
        entry.clone()
    };

    // backendExpBlocking = isCompletelyHandled() && !hasRepresentativeSameIndividualMerging()
    //                      && detMergedSameConsideredLabel == DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL
    let mut expansion_blocked = false;
    if entry.reusable_for_full_completion()
        && native_backend_concepts_synchronized(algo, ctx, bridged, seed, node, &entry)
    {
        if !ctx
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            )
            && algo.conf_allow_backend_successor_expansion_blocking
        {
            ctx.process_context_mut()
                .node_mut(node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
                        | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
                        | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
                );
        }
        expansion_blocked = true;
    }
    // The independent neighbour block: gated only on the config flag, exactly as
    // upstream. `PRFRETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED` schedules the
    // first `detectIndividualNodeBackendCacheSynchronized` pass, which decides via
    // the critical predicates whether the block is released and the cache-backed
    // selective expansion runs.
    if algo.conf_allow_backend_neighbour_expansion_blocking {
        ctx.process_context_mut()
            .node_mut(node)
            .add_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
                    | IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
            );
    }
    expansion_blocked
}

/// Read FULL_CONCEPT_SET_LABEL into one completion nominal. All saturated
/// concepts are sound and may be replayed for an insufficient association;
/// only the separate expansion/blocking permission is gated by complete,
/// non-insufficient status.
fn replay_native_representative_cache(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    seed: &NominalSeed,
    node: NodeId,
    dependency_track_point: super::process::TrackPointId,
) -> bool {
    let entry = {
        let cache = bridged.native_representative_cache.borrow();
        let Some(cache) = cache.as_ref() else {
            return true;
        };
        if cache.association_write_aborted {
            return true;
        }
        let Some(entry) = cache.entries.get(&seed.individual_tag) else {
            return false;
        };
        if !native_cache_entry_covers_seed(entry, seed) {
            return false;
        }
        entry.clone()
    };

    let Some(concept_values) = entry.concept_values.as_ref() else {
        return false;
    };
    for value in concept_values.iter().filter(|value| value.deterministic) {
        algo.add_concept_to_individual_skip_and_processing(
            value.concept,
            value.negated,
            node,
            dependency_track_point,
            true,
            false,
            false,
            ctx,
        );
        if ctx.has_pending_signal() {
            break;
        }
    }
    ctx.process_context_mut()
        .node_mut(node)
        .set_nominal_individual_representative_backend_data_loaded(true);

    true
}

/// Per-classification saturation outcome, extracted into plain data so the
/// probe env's resets cannot invalidate it.
pub struct SaturationOutcome {
    /// Per named index: `Some(true)` = UNSAT-certain, `Some(false)` =
    /// SAT-certain, `None` = unknown (probe needed).
    pub sat_verdict: Vec<Option<bool>>,
    /// Per named index: the COMPLETE certain-subsumer set (named indices,
    /// self excluded) — present exactly when the node is sufficient
    /// (SAT-certain), per `CPrecomputedSaturationSubsumerExtractor`.
    pub certain_subsumers: Vec<Option<Vec<usize>>>,
    /// Positive named labels for every processed saturation node, including
    /// insufficient nodes. For a pure-TBox saturation these are sound
    /// consequences even on insufficient nodes. With native-ABox nodes in the
    /// saturation graph an insufficient node's label can additionally carry
    /// individual-derived or branch-dependent entries (nominal backward
    /// propagation, substitute chains through assertion-resolved nodes), which
    /// are facts about particular individuals or one retained model — NOT
    /// class subsumptions. They may therefore seed KPSet *scheduling* (the
    /// predecessor graph and test order) unconditionally, but may become
    /// taxonomy edges or probe-free trusted subsumers only for subjects whose
    /// label is certified — see [`SaturationOutcome::label_certified`].
    pub known_subsumers: Vec<Vec<usize>>,
}

impl SaturationOutcome {
    /// True iff `subject`'s extracted label may be consumed as unconditional
    /// subsumptions.
    ///
    /// This is exactly Konclude's `CPrecomputedSaturationSubsumerExtractor`
    /// consumption contract: a CLASHED node is UNSAT-certain (every pair
    /// `subject ⊑ c` is then vacuously entailed), and a sufficient node
    /// (¬INSUFFICIENT ∧ ¬UNPROCESSED, no problematic EQ candidate — i.e.
    /// `certain_subsumers` present) has an EXACT deterministic subsumer set.
    /// Everything else — in particular nominal-connected / native-ABox
    /// influenced nodes, which the saturation flags INSUFFICIENT — must have
    /// its label treated as candidate data only and re-derived through the
    /// completion path (read-off, KPSet messages, pair probes).
    pub fn label_certified(&self, subject: usize) -> bool {
        match self.sat_verdict.get(subject).copied().flatten() {
            Some(true) => true,
            Some(false) => self
                .certain_subsumers
                .get(subject)
                .is_some_and(Option::is_some),
            None => false,
        }
    }
}

/// Resolve Konclude's saturation substitute chain and report the named
/// concepts carried by its intermediate nodes.
///
/// This is the first loop in
/// `CPrecomputedSaturationSubsumerExtractor::extractSubsumers`: the base node
/// is excluded, every non-terminal substitute node contributes its positive
/// class concept when it is not a role-range test or the queried concept, and
/// the terminal node is returned for the ordinary label extraction below.
fn resolve_saturation_substitute_chain(
    ctx: &CalculationAlgorithmContextBase,
    base_node: super::process::SatNodeId,
    queried_concept: ConceptId,
    named_index: &std::collections::HashMap<ConceptId, usize>,
    subsumers: &mut Vec<usize>,
) -> super::process::SatNodeId {
    let mut resolved = base_node;
    while ctx
        .process_context()
        .sat_node(resolved)
        .has_substitute_individual_node()
    {
        if resolved != base_node {
            let reference = ctx
                .process_context()
                .sat_node(resolved)
                .get_saturation_concept_reference_linking();
            if reference.is_some() {
                let item = ctx
                    .process_context()
                    .extended_con_ref_linking_data(reference);
                let concept = item.get_saturation_concept();
                if !item.get_saturation_negation()
                    && item.get_saturation_role_ranges().is_none()
                    && concept != queried_concept
                {
                    if let Some(&index) = named_index.get(&concept) {
                        subsumers.push(index);
                    }
                }
            }
        }
        resolved = ctx
            .process_context()
            .sat_node(resolved)
            .get_substitute_individual_node();
    }
    resolved
}

/// `CPrecomputedSaturationSubsumerExtractor::getConceptFlags` + `extractSubsumers`
/// over the saturated bridge env: follow the POSITIVE node (substitute-chain
/// resolved), read INDIRECT flags of base + resolved node —
/// CLASHED ⇒ UNSAT-certain; ¬INSUFFICIENT ∧ ¬UNPROCESSED and no problematic
/// EQ-candidate descriptor ⇒ SAT-certain with the label's non-negated named
/// entries as the exact subsumer set; anything else ⇒ unknown.
fn extract_saturation_outcome(
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
) -> SaturationOutcome {
    use super::process::sat_node::IndividualSaturationProcessNodeStatusFlags as F;
    let n_named = bridged.named.len();
    let named_index: std::collections::HashMap<ConceptId, usize> = bridged
        .named
        .iter()
        .enumerate()
        .map(|(i, &c)| (c, i))
        .collect();
    let mut sat_verdict: Vec<Option<bool>> = vec![None; n_named];
    let mut certain_subsumers: Vec<Option<Vec<usize>>> = vec![None; n_named];
    let mut known_subsumers: Vec<Vec<usize>> = vec![Vec::new(); n_named];
    let mut unknown_no_node = 0usize;
    let mut unknown_insufficient = 0usize;
    let mut unknown_unprocessed = 0usize;
    let mut unknown_eq_candidate = 0usize;
    let trust_insufficient = std::env::var_os("KM_HT_TRUST_INSUFFICIENT").is_some();
    for (i, &named) in bridged.named.iter().enumerate() {
        let base_node =
            super::saturation::algorithm::SaturationTaskHandleAlgorithm::s07_concept_reference_node(
                named, false, ctx,
            );
        if base_node.is_none() {
            unknown_no_node += 1;
            continue;
        }
        // `extractSubsumers` reports positive named concepts attached to
        // intermediate substitute nodes before reading the terminal label.
        let mut subs: Vec<usize> = Vec::new();
        let resolved =
            resolve_saturation_substitute_chain(ctx, base_node, named, &named_index, &mut subs);
        let read = |node: super::process::SatNodeId,
                    ctx: &CalculationAlgorithmContextBase|
         -> (bool, bool, bool, bool) {
            let sat_node = ctx.process_context().sat_node(node);
            let ind = sat_node.indirect_status_flags.get_flags();
            let dir = sat_node.direct_status_flags.get_flags();
            (
                ind & F::INDSATFLAGCLASHED != 0,
                ind & F::INDSATFLAGINSUFFICIENT != 0,
                ind & F::INDSATFLAGUNPROCESSED != 0,
                dir & F::INDSATFLAGEQCANDPROPLEMATIC != 0,
            )
        };
        let (b_clash, b_insuf, b_unproc, _b_eqprob) = read(base_node, ctx);
        let (r_clash, r_insuf, r_unproc, r_eqprob) = read(resolved, ctx);
        if std::env::var_os("KM_SAT_DEBUG").is_some() {
            eprintln!(
                "SAT-SUBJ {} concept={:?} base={:?} resolved={:?} b_clash={} r_clash={}",
                i, named, base_node, resolved, b_clash, r_clash
            );
        }
        let clashed = b_clash || r_clash;
        let insufficient = b_insuf || r_insuf;
        let unprocessed = b_unproc || r_unproc;
        // extractSubsumers (cpp 40–130): non-negated class-named label entries
        // are sound known subsumers even when the node is insufficient.
        let mut eq_candidate_present = false;
        let label = ctx
            .process_context()
            .sat_node(resolved)
            .reapply_con_sat_label_set;
        if label.is_some() {
            let mut des = ctx
                .process_context()
                .reapply_con_sat_label_set(label)
                .get_concept_saturation_description_linker();
            while des.is_some() {
                let (concept, negated) = {
                    let d = ctx.process_context().con_sat_desc(des);
                    (d.get_concept(), d.get_negation())
                };
                let op_code = ctx.ontology_arenas().concept(concept).get_operator_code();
                eq_candidate_present |= op_code == op::CCEQCAND;
                if !negated {
                    if let Some(&idx) = named_index.get(&concept) {
                        if idx != i {
                            subs.push(idx);
                        }
                    }
                }
                des = ctx
                    .process_context()
                    .con_sat_desc(des)
                    .get_next_concept_desciptor();
            }
        }
        subs.sort_unstable();
        subs.dedup();
        known_subsumers[i] = subs.clone();
        if clashed {
            sat_verdict[i] = Some(true);
            continue;
        }
        if insufficient && !trust_insufficient || unprocessed || eq_candidate_present && r_eqprob {
            unknown_insufficient += usize::from(insufficient && !trust_insufficient);
            unknown_unprocessed += usize::from(unprocessed);
            unknown_eq_candidate += usize::from(eq_candidate_present && r_eqprob);
            continue; // unknown — probe needed
        }
        sat_verdict[i] = Some(false);
        certain_subsumers[i] = Some(subs);
    }
    if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
        eprintln!(
            "BRIDGE-SATURATION-UNKNOWN: no-node={} insufficient={} unprocessed={} eq-candidate={}",
            unknown_no_node, unknown_insufficient, unknown_unprocessed, unknown_eq_candidate,
        );
    }
    SaturationOutcome {
        sat_verdict,
        certain_subsumers,
        known_subsumers,
    }
}

/// Saturate the bridged ontology once (dedicated env — the probe env and its
/// resets are untouched) and extract the verdicts. `None` when the input is
/// outside the bridge fragment.
pub fn bridged_saturate(tin: &TInput) -> Option<SaturationOutcome> {
    if !bridge_input_guard(tin) {
        return None;
    }
    bridged_saturate_with_trigger_absorption(tin, std::env::var_os("KM_TRIGGER_ABSORB").is_some())
}

fn bridged_saturate_with_trigger_absorption(
    tin: &TInput,
    trigger_absorb: bool,
) -> Option<SaturationOutcome> {
    // This private entry point is also used by classification's pre-pass.
    // Recheck the shared fence before building or extracting any certificate.
    if !bridge_input_guard(tin) {
        return None;
    }
    if has_builtin_top_role(tin)
        || has_fixed_datatype_object_position(tin)
        || has_any_nominal_input(tin)
    {
        return None;
    }
    let source_mode = trigger_absorb
        && !tin.source_axioms.is_empty()
        && std::env::var_os("KM_NO_SOURCE_TBOX").is_none();
    if !datatype_bridge_route_exact(tin, source_mode) {
        return None;
    }
    let (_completion_algo, mut ctx, bridged) =
        fresh_bridge_env_with_trigger_absorption(tin, trigger_absorb);
    if bridged.unsupported > 0 {
        return None;
    }
    if !run_bridged_saturation(&mut ctx, &bridged) {
        return None;
    }
    Some(extract_saturation_outcome(&mut ctx, &bridged))
}

/// Run the production approximation saturation ON the given bridge env
/// (preprocess + seeds + drive). Returns false on a budget overrun: unfinished
/// queues may hold unchecked critical concepts, so no per-node flags are
/// trustworthy — the caller must discard the pass (no verdict extraction, no
/// saturation-node coupling). The saturation NODES remain in the env's arenas
/// either way (the concept→saturation reference linkings installed by the
/// seeds point at them; see `reset_probe_env`'s saturation carry).
fn run_bridged_saturation(ctx: &mut CalculationAlgorithmContextBase, bridged: &Bridged) -> bool {
    run_bridged_saturation_with_native_consistency_prefix(
        ctx,
        bridged,
        None,
        NativeSaturationAssociationMode::Publish,
    )
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum NativeSaturationAssociationMode {
    /// Individual-saturation precomputation owns the representative-cache
    /// association write.
    Publish,
    /// A later saturation consumer may inspect the installed consistency
    /// model, but must not replace the completed representative associations.
    ReadOnlyConsumer,
}

fn run_bridged_saturation_with_native_consistency_prefix(
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    native_consistency_prefix: Option<HashMap<Cint64, Vec<(ConceptId, bool)>>>,
    association_mode: NativeSaturationAssociationMode,
) -> bool {
    let mut sat_algo = super::saturation::algorithm::SaturationTaskHandleAlgorithm::new();
    sat_algo.native_consistency_nominal_nondeterministic_prefix = native_consistency_prefix;
    configure_production_saturation(&mut sat_algo);
    let preparation_started = std::time::Instant::now();
    let preparation_budget = std::time::Duration::from_secs(
        std::env::var("KM_HT_SATURATION_BUDGET_S")
            .ok()
            .and_then(|value| value.parse::<u64>().ok())
            .unwrap_or(120),
    );
    let preparation_deadline = Some(preparation_started + preparation_budget);
    let phase_progress = super::completion::bridge_progress_enabled();
    extract_propagation_into_creation_direction(ctx);
    if phase_progress {
        eprintln!(
            "BRIDGE-SAT-PHASE propagation-direction: {:.2}s",
            preparation_started.elapsed().as_secs_f64()
        );
    }
    if preparation_deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
        return false;
    }
    let t_seeds = std::time::Instant::now();
    if !build_saturation_seeds_with_deadline(ctx, bridged, preparation_deadline) {
        return false;
    }
    if phase_progress {
        eprintln!(
            "BRIDGE-SAT-PHASE seeds: {:.2}s",
            t_seeds.elapsed().as_secs_f64()
        );
    }
    // Konclude constructs the concept-testing nodes and the named ABox nodes
    // into one saturation task, then enters the processing loop once. In
    // particular, a named node creates its separated TOP assertion-resolve
    // node and assertion extensions before the task reaches critical-concept
    // checking. Running the concept wave to completion first would copy an
    // already-insufficient TOP status into every later assertion extension;
    // adding a satisfying class assertion cannot retract that monotone flag.
    let native_nodes = if bridged.has_native_nominals() {
        let Some(native_nodes) =
            build_native_abox_saturation_seeds(&mut sat_algo, ctx, bridged, preparation_deadline)
        else {
            return false;
        };
        Some(native_nodes)
    } else {
        None
    };
    let t_loop = std::time::Instant::now();
    if !sat_algo.run_saturation_on(ctx) {
        if phase_progress {
            eprintln!(
                "BRIDGE-SAT-PHASE loop: {:.2}s (budget overrun)",
                t_loop.elapsed().as_secs_f64()
            );
        }
        return false;
    }
    if phase_progress {
        eprintln!(
            "BRIDGE-SAT-PHASE loop: {:.2}s (nodes={})",
            t_loop.elapsed().as_secs_f64(),
            ctx.process_context().sat_node_count()
        );
    }
    if let Some(native_nodes) = native_nodes {
        // The representative-cache writer consumes the final linked-successor
        // view. Force the same incremental collection Konclude performs in its
        // saturation analyser before copying the role label families.
        for &(_, node) in &native_nodes {
            let mut node = node;
            sat_algo.collect_linked_successor_nodes(&mut node, ctx, INVALID);
        }
        let Some(cache) = write_native_abox_representative_cache(ctx, bridged, &native_nodes)
        else {
            return false;
        };
        if association_mode == NativeSaturationAssociationMode::Publish {
            *bridged.native_representative_cache.borrow_mut() = Some(cache);
        }
    }
    if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
        eprintln!(
            "SAT-STATS: insufficient all={} atmost={} or={} eqcand={} value={} nominal={}",
            sat_algo.insufficient_all_count,
            sat_algo.insufficient_atmost_count,
            sat_algo.insufficient_or_count,
            sat_algo.insufficient_eqcand_count,
            sat_algo.insufficient_value_count,
            sat_algo.insufficient_nominal_count,
        );
    }
    if std::env::var_os("KM_SAT_DEBUG").is_some() {
        debug_dump_saturation_nodes(ctx);
    }
    true
}

/// Temporary diagnostic (env `KM_SAT_DEBUG=1`): per saturation node, dump the
/// completion state, direct/indirect flag words and the full saturated label
/// (concept id, op code, negation).
fn debug_dump_saturation_nodes(ctx: &CalculationAlgorithmContextBase) {
    let n = ctx.process_context().sat_node_count();
    for i in 0..n {
        let node = super::process::SatNodeId::new(i as Cint64);
        let sat_node = ctx.process_context().sat_node(node);
        let label = sat_node.reapply_con_sat_label_set;
        eprintln!(
            "SAT-NODE {}: indi={} completed={} dir={:#x} ind={:#x} subst={:?}",
            i,
            sat_node.get_individual_id(),
            sat_node.is_completed(),
            sat_node.direct_status_flags.get_flags(),
            sat_node.indirect_status_flags.get_flags(),
            sat_node.get_substitute_individual_node(),
        );
        if label.is_some() {
            let ls = ctx.process_context().reapply_con_sat_label_set(label);
            let mut entries: Vec<(Cint64, String)> = Vec::new();
            for (tag, data) in ls
                .concept_des_dep_hash
                .iter()
                .chain(ls.additional_concept_des_dep_hash.iter())
            {
                let des = data.con_sat_des;
                if des.is_some() {
                    let c = ctx.process_context().con_sat_desc(des).get_concept();
                    let neg = ctx.process_context().con_sat_desc(des).get_negation();
                    let op = ctx.ontology_arenas().concept(c).get_operator_code();
                    entries.push((*tag, format!("c{}(op{},neg={})", c.index(), op, neg)));
                } else {
                    entries.push((*tag, "reapply-only".to_string()));
                }
            }
            entries.sort();
            for (tag, s) in entries {
                eprintln!("    tag {} -> {}", tag, s);
            }
        }
    }
}

/// Linear told-name closure used outside the mixed native
/// cardinality+ABox profile.  The richer definition-containment closure below
/// is valuable for that profile, but its global structural fixpoint is
/// unnecessary on large nominal-free TBoxes: any omitted shortcut pair is
/// still decided by the ordinary completion probes.
fn source_told_named_subsumer_closure(
    tin: &TInput,
) -> std::collections::HashSet<(usize, usize)> {
    let index: HashMap<&str, usize> = tin
        .concepts
        .iter()
        .enumerate()
        .map(|(i, name)| (name.as_str(), i))
        .collect();
    fn collect<'a>(concept: &'a SourceConcept, out: &mut Vec<&'a str>) {
        match concept {
            SourceConcept::Name(name) => out.push(name.as_str()),
            SourceConcept::And(operands) => {
                for operand in operands {
                    collect(operand, out);
                }
            }
            _ => {}
        }
    }
    let mut direct: Vec<Vec<usize>> = vec![Vec::new(); tin.concepts.len()];
    let mut add = |left: &SourceConcept, right: &SourceConcept| {
        let SourceConcept::Name(left) = left else {
            return;
        };
        let Some(&sub) = index.get(left.as_str()) else {
            return;
        };
        let mut names = Vec::new();
        collect(right, &mut names);
        for name in names {
            if let Some(&sup) = index.get(name) {
                if sup != sub {
                    direct[sub].push(sup);
                }
            }
        }
    };
    for axiom in &tin.source_axioms {
        match axiom.kind {
            crate::json_io::SourceAxiomKind::SubClass => add(&axiom.left, &axiom.right),
            crate::json_io::SourceAxiomKind::Equivalent => {
                add(&axiom.left, &axiom.right);
                add(&axiom.right, &axiom.left);
            }
            crate::json_io::SourceAxiomKind::Disjoint => {}
        }
    }
    let mut closure = std::collections::HashSet::new();
    for sub in 0..direct.len() {
        let mut stack = direct[sub].clone();
        while let Some(sup) = stack.pop() {
            if closure.insert((sub, sup)) {
                stack.extend(direct[sup].iter().copied());
            }
        }
    }
    closure
}

/// Deterministic named hierarchy already present in Konclude's CCSUB/CCEQ
/// terminology before classification: the EXACT, search-free part of the
/// subsumption relation, closed under both of its rules and transitively.
/// Every pair is entailed, so it is a sound known-subsumer seed for KPSet and
/// requires no tableau probe.
///
/// Two rules, both decided by set containment on the axioms alone:
///
/// * TOLD — `N ⊑ … ⊓ M ⊓ …` with `M` a named class ⇒ `N ⊑ M`.
/// * DEFINITION — whenever the source proves `D ⊑ M` (an equivalence side, or
///   an inclusion whose right side is the named class `M`) and every top-level
///   conjunct of `D` is already known to hold for `N`, then
///   `N ⊑ ⨅conj(D) ⊑ M`. `And` is a `BTreeSet` in the source syntax, so equal
///   conjunctions ARE syntactically equal here — the same reason the
///   terminology builder's `concept_cache` shares one `ConceptId` between the
///   two definitions.
///
/// Neither rule can fire in the converse direction: `conj(D_M) ⊆ conj(D_N)`
/// justifies `N ⊑ M` only; `M ⊑ N` needs the opposite containment AND a
/// definition for `N`.
///
/// Why the DEFINITION rule belongs here rather than in the completion:
/// Konclude derives it from the absorbed reverse direction of `M`'s definition,
/// which is a MODEL-based route — the KPSet candidate set only ever contains
/// what the one completion model the search built happens to carry, and a
/// definition whose trigger chain runs through a disjunction is carried only by
/// the branch that model committed to. Measured on ore_ont_9540: subject
/// `UJI_Wall` reached the verification phase with two candidates (its told
/// subsumer plus one non-candidate equivalence), so `Possible_UJI_Wall` — whose
/// definition conjuncts are exactly a subset of `UJI_Wall`'s — was never tested
/// and never emitted. This pass decides that class of consequence up front, and
/// because the pairs also land in the known-subsumer set they REMOVE pair
/// probes instead of adding any.
fn source_named_subsumer_closure(tin: &TInput) -> std::collections::HashSet<(usize, usize)> {
    let index: HashMap<&str, usize> = tin
        .concepts
        .iter()
        .enumerate()
        .map(|(i, name)| (name.as_str(), i))
        .collect();
    let n_named = tin.concepts.len();

    /// Top-level conjuncts of a superclass side. `And` is flattened; `Top`
    /// carries no obligation and no information.
    fn conjuncts<'a>(concept: &'a SourceConcept, out: &mut Vec<&'a SourceConcept>) {
        match concept {
            SourceConcept::And(operands) => {
                for operand in operands {
                    conjuncts(operand, out);
                }
            }
            SourceConcept::Top => {}
            other => out.push(other),
        }
    }

    /// One `D ⊑ M` provider: the named conjuncts of `D` (as class indices) and
    /// its structural conjuncts (as interned keys). Both must be discharged for
    /// a class before `M` may be concluded for it.
    type Provider = (usize, Vec<usize>, Vec<usize>);

    /// Structural conjuncts are interned only where a provider body TESTS them.
    /// Any other conjunct can never decide a rule, so it is neither interned
    /// nor inherited — that is what keeps the per-class sets small on a large
    /// source TBox.
    fn record_provider<'a>(
        head: &SourceConcept,
        body: &'a SourceConcept,
        index: &HashMap<&str, usize>,
        keys: &mut HashMap<&'a SourceConcept, usize>,
        providers: &mut Vec<Provider>,
    ) {
        let SourceConcept::Name(head) = head else {
            return;
        };
        let Some(&sup) = index.get(head.as_str()) else {
            return;
        };
        let mut parts = Vec::new();
        conjuncts(body, &mut parts);
        let mut named = Vec::new();
        let mut structural = Vec::new();
        for part in parts {
            match part {
                SourceConcept::Name(name) => match index.get(name.as_str()) {
                    Some(&class) => named.push(class),
                    // A conjunct outside the concept vector can never be
                    // discharged, so the whole body is unusable here.
                    None => return,
                },
                other => {
                    let next = keys.len();
                    structural.push(*keys.entry(other).or_insert(next));
                }
            }
        }
        named.sort_unstable();
        named.dedup();
        structural.sort_unstable();
        structural.dedup();
        // `⊤ ⊑ M` is sound but would make every class a subclass of `M` from a
        // purely syntactic pass; leave that shape to the completion. A body
        // that is just `M` itself is vacuous.
        if named.is_empty() && structural.is_empty() {
            return;
        }
        if structural.is_empty() && named.len() == 1 && named[0] == sup {
            return;
        }
        providers.push((sup, named, structural));
    }

    let mut keys: HashMap<&SourceConcept, usize> = HashMap::new();
    let mut providers: Vec<Provider> = Vec::new();
    for axiom in &tin.source_axioms {
        match axiom.kind {
            // `D ⊑ M` with a named right side — including the structural-left
            // GCI half of an equivalence the terminology could not host as a
            // direct definition.
            crate::json_io::SourceAxiomKind::SubClass => {
                record_provider(&axiom.right, &axiom.left, &index, &mut keys, &mut providers);
            }
            crate::json_io::SourceAxiomKind::Equivalent => {
                record_provider(&axiom.left, &axiom.right, &index, &mut keys, &mut providers);
                record_provider(&axiom.right, &axiom.left, &index, &mut keys, &mut providers);
            }
            crate::json_io::SourceAxiomKind::Disjoint => {}
        }
    }

    // Seed the per-class state from the asserted superclass sides.
    let mut upper: Vec<std::collections::HashSet<usize>> = vec![Default::default(); n_named];
    let mut key_subjects: Vec<Vec<usize>> = vec![Vec::new(); keys.len()];
    let mut pair_stack: Vec<(usize, usize)> = Vec::new();
    let mut key_stack: Vec<(usize, usize)> = Vec::new();
    {
        let mut seed = |left: &SourceConcept, right: &SourceConcept| {
            let SourceConcept::Name(left) = left else {
                return;
            };
            let Some(&sub) = index.get(left.as_str()) else {
                return;
            };
            let mut parts = Vec::new();
            conjuncts(right, &mut parts);
            for part in parts {
                match part {
                    SourceConcept::Name(name) => {
                        if let Some(&sup) = index.get(name.as_str()) {
                            pair_stack.push((sub, sup));
                        }
                    }
                    other => {
                        if let Some(&key) = keys.get(other) {
                            if upper[sub].insert(key) {
                                key_subjects[key].push(sub);
                                key_stack.push((sub, key));
                            }
                        }
                    }
                }
            }
        };
        for axiom in &tin.source_axioms {
            match axiom.kind {
                crate::json_io::SourceAxiomKind::SubClass => seed(&axiom.left, &axiom.right),
                crate::json_io::SourceAxiomKind::Equivalent => {
                    seed(&axiom.left, &axiom.right);
                    seed(&axiom.right, &axiom.left);
                }
                crate::json_io::SourceAxiomKind::Disjoint => {}
            }
        }
    }

    let mut closure: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
    let mut supers: Vec<Vec<usize>> = vec![Vec::new(); n_named];
    let mut subs: Vec<Vec<usize>> = vec![Vec::new(); n_named];
    loop {
        // Propagate the current facts to a fixpoint: transitivity of the pair
        // relation, and inheritance of a superclass's conjuncts by its
        // subclasses (`N ⊑ M ⊑ D` ⇒ `N ⊑ D`).
        while !pair_stack.is_empty() || !key_stack.is_empty() {
            while let Some((sub, sup)) = pair_stack.pop() {
                if sub == sup || sub >= n_named || sup >= n_named || !closure.insert((sub, sup)) {
                    continue;
                }
                supers[sub].push(sup);
                subs[sup].push(sub);
                let inherited: Vec<usize> = upper[sup].iter().copied().collect();
                for key in inherited {
                    if upper[sub].insert(key) {
                        key_subjects[key].push(sub);
                        key_stack.push((sub, key));
                    }
                }
                for i in 0..supers[sup].len() {
                    pair_stack.push((sub, supers[sup][i]));
                }
                for i in 0..subs[sub].len() {
                    pair_stack.push((subs[sub][i], sup));
                }
            }
            while let Some((sub, key)) = key_stack.pop() {
                for i in 0..subs[sub].len() {
                    let descendant = subs[sub][i];
                    if upper[descendant].insert(key) {
                        key_subjects[key].push(descendant);
                        key_stack.push((descendant, key));
                    }
                }
            }
        }
        // One DEFINITION sweep over the propagated state. Candidates come from
        // the smallest witness set of any single conjunct — a class can only
        // discharge a body if it already carries every one of its conjuncts.
        let mut derived = false;
        for (sup, named, structural) in &providers {
            let mut best: Option<(usize, bool, usize)> = None;
            for &class in named {
                let len = subs[class].len() + 1;
                if best.is_none_or(|(best_len, _, _)| len < best_len) {
                    best = Some((len, true, class));
                }
            }
            for &key in structural {
                let len = key_subjects[key].len();
                if best.is_none_or(|(best_len, _, _)| len < best_len) {
                    best = Some((len, false, key));
                }
            }
            let candidates: Vec<usize> = match best {
                Some((_, true, class)) => {
                    let mut candidates = subs[class].clone();
                    candidates.push(class);
                    candidates
                }
                Some((_, false, key)) => key_subjects[key].clone(),
                None => continue,
            };
            for sub in candidates {
                if sub == *sup || closure.contains(&(sub, *sup)) {
                    continue;
                }
                let discharged = structural.iter().all(|key| upper[sub].contains(key))
                    && named
                        .iter()
                        .all(|&class| class == sub || closure.contains(&(sub, class)));
                if discharged {
                    pair_stack.push((sub, *sup));
                    derived = true;
                }
            }
        }
        if !derived {
            break;
        }
    }
    closure
}

/// Does the source terminology contain the inverse-sensitive mirror pattern
/// that the bridge must currently defer?
///
/// Source axioms are stored in negation normal form, so
/// `N ≡ ObjectComplementOf(ObjectSomeValuesFrom(R F))` arrives as
/// `N ≡ ObjectAllValuesFrom(R ObjectComplementOf(F))`. The `owl:Thing`
/// filler is the one special case whose negation normalises to bottom.
fn has_unhandled_inverse_negative_existential_mirror(tin: &TInput) -> bool {
    use crate::frontend::syntax::{Concept, Role as SourceRole};
    use crate::json_io::SourceAxiomKind;

    fn concept_has_inverse_role(concept: &Concept) -> bool {
        match concept {
            Concept::Not(inner) => concept_has_inverse_role(inner),
            Concept::And(operands) | Concept::Or(operands) => {
                operands.iter().any(concept_has_inverse_role)
            }
            Concept::Exists(role, filler)
            | Concept::Forall(role, filler)
            | Concept::AtLeast(_, role, filler)
            | Concept::AtMost(_, role, filler) => {
                matches!(role, SourceRole::Inverse(_)) || concept_has_inverse_role(filler)
            }
            Concept::HasSelf(role) => matches!(role, SourceRole::Inverse(_)),
            Concept::Name(_) | Concept::Top | Concept::Bottom | Concept::Nominal(_) => false,
        }
    }

    // cb_to_ht's `inverse` flag covers pairwise inverse metadata, but inverse
    // semantics can also survive only as an explicit inverse role in source
    // provenance or as a swapped role bridge R(x,y) -> S(y,x).  The latter is
    // intentionally independent of `tin.inverse` in the orchestrator.  The
    // mirror fence must recognize all three representations before any public
    // bridge API can issue a certificate.
    let source_inverse = tin.source_axioms.iter().any(|axiom| {
        concept_has_inverse_role(&axiom.left) || concept_has_inverse_role(&axiom.right)
    });
    let swapped_role_bridge = tin.clauses.iter().any(|clause| {
        clause.head.iter().any(|head| {
            let HAtom::Role {
                s: head_source,
                t: head_target,
                ..
            } = head
            else {
                return false;
            };
            clause.body.iter().any(|body| {
                matches!(
                    body,
                    HAtom::Role {
                        s: body_source,
                        t: body_target,
                        ..
                    } if body_source == head_target && body_target == head_source
                )
            })
        })
    });
    if !(tin.inverse || source_inverse || swapped_role_bridge) {
        return false;
    }

    fn named_mirror(left: &Concept, right: &Concept) -> bool {
        if !matches!(left, Concept::Name(_)) {
            return false;
        }
        matches!(
            right,
            Concept::Forall(
                _,
                filler
            ) if matches!(
                filler.as_ref(),
                Concept::Not(inner) if matches!(inner.as_ref(), Concept::Name(_))
            ) || matches!(filler.as_ref(), Concept::Bottom)
        )
    }

    tin.source_axioms.iter().any(|axiom| {
        axiom.kind == SourceAxiomKind::Equivalent
            && (named_mirror(&axiom.left, &axiom.right) || named_mirror(&axiom.right, &axiom.left))
    })
}

/// Input-level soundness fence shared by every classification/saturation API.
///
/// Keep this check ahead of datatype, bottom-prepass, nominal, and saturation
/// certificates: none of those certificates reconstructs the inverse feedback
/// needed by a named `N = not exists R.F` mirror.
fn bridge_input_guard(tin: &TInput) -> bool {
    !has_unhandled_inverse_negative_existential_mirror(tin)
}

/// Production classification of a `TInput` over the konclude_ht bridge.
///
/// Per subject: model read-off when the saturation was deterministic
/// (authoritative — the canonical model IS the subsumer set), else candidate
/// extraction + pairwise `bridged_unsat(s ⊓ ¬c)` verification (label ABSENCE
/// in a saturated clash-free graph is a countermodel even on a
/// non-deterministic drive, so the candidate positives are a complete
/// filter; only presences need verification).
///
/// Returns `None` (DEFER — the caller must fall back to a sound+complete
/// arm) when the answer would not be both sound and complete:
/// - the encoder could not express every clause (`unsupported > 0`);
/// - the input carries nominals/ABox content (not bridged);
/// - a subject still lacks a verdict after every retry round (a STOPped
///   drive/probe defers the SUBJECT first; only subjects that exhaust the
///   escalated budgets defer the whole classification).
///
/// Per-probe budget: `KM_BRIDGE_PROBE_BUDGET_S` (default 10 s) for the first
/// round; deferred subjects are retried with the budget escalated ×4 per
/// round for `KM_BRIDGE_RETRY_ROUNDS` (default 2) extra rounds — so one
/// pathological subject costs bounded time while the cheap bulk completes,
/// instead of the first budget-STOP discarding all finished work.
pub fn bridged_classify(tin: &TInput) -> Option<BridgedClassification> {
    if !bridge_input_guard(tin) {
        return None;
    }
    // Saturation-first probe answering (task #23, opt-in KM_HT_SATURATION=1)
    // + the saturation-node coupling into the residue probes (task #24 wave 2,
    // opt-in KM_HT_SATCACHE=1 on top). The coupling stays OPT-IN because
    // without the extension-resolving refinement (needs the ext machinery,
    // currently unsound/off) the replayed labels under-approximate the
    // ∀-restricted successors, establish fails there, and the enlarged labels
    // measurably POISON probes earlier (12653: permanent defer at subject 1
    // vs 14 plain). Re-evaluate the default after the ext-machinery audit.
    // Trigger absorption is designed to make the non-branching saturation
    // residue filter effective, so enabling it also enables this pre-pass. The
    // legacy explicit flag remains available for absorption-off diagnostics.
    let trigger_absorb = std::env::var_os("KM_TRIGGER_ABSORB").is_some();
    let use_saturation = std::env::var_os("KM_HT_NO_SATURATION").is_none()
        && (std::env::var_os("KM_HT_SATURATION").is_some() || trigger_absorb);
    let use_satcache = use_saturation
        && std::env::var_os("KM_HT_NO_SATCACHE").is_none()
        && (std::env::var_os("KM_HT_SATCACHE").is_some() || trigger_absorb);
    bridged_classify_opts_with_trigger_absorption(tin, use_saturation, use_satcache, trigger_absorb)
}

/// The env-independent core of [`bridged_classify`] — `use_saturation` answers
/// whole subjects from a pre-probe saturation pass, `use_satcache` additionally
/// arms the saturation-node coupling (expand-from-saturation + caching-blocking,
/// Konclude's production completion profile) inside the residue probes.
pub fn bridged_classify_opts(
    tin: &TInput,
    use_saturation: bool,
    use_satcache: bool,
) -> Option<BridgedClassification> {
    if !bridge_input_guard(tin) {
        return None;
    }
    bridged_classify_opts_with_trigger_absorption(
        tin,
        use_saturation,
        use_satcache,
        std::env::var_os("KM_TRIGGER_ABSORB").is_some(),
    )
}

fn bridged_classify_opts_with_trigger_absorption(
    tin: &TInput,
    use_saturation: bool,
    use_satcache: bool,
    trigger_absorb: bool,
) -> Option<BridgedClassification> {
    // Typed role facts are admitted only through the exact source-mode
    // metadata gate below. The terminology builder gives them the exact
    // existential/universal nominal encoding used by the source-mode concept
    // machinery.
    // A named mirror `N ≡ ¬∃R.F` is represented in source NNF as
    // `N ≡ ∀R.¬F`. With inverse roles, a root type can constrain the
    // generated R-successor through R⁻ and thereby entail cross-region
    // `A ⊑ N` facts. The current bridge neither reconstructs the complete
    // contravariant mirror hierarchy nor safely verifies every such inverse
    // feedback consequence. On ORE 4669 this fragment has produced both false
    // UNSAT classes and, under a different schedule, an unvalidated positive
    // projection whose logical completeness is unknown. Neither result
    // satisfies the bridge's complete-or-defer contract. Keep the trusted CB
    // fallback authoritative until the exact positive-proxy/disjointness
    // mechanism is part of this input.
    if !bridge_input_guard(tin) {
        return None;
    }
    // The bridge has neither a universal-role object nor a typed data-domain
    // object. Decline before constructing an arena instead of treating either
    // construct as an ordinary named symbol.
    if has_builtin_top_role(tin) || has_fixed_datatype_object_position(tin) {
        return None;
    }
    let source_mode = trigger_absorb
        && !tin.source_axioms.is_empty()
        && std::env::var_os("KM_NO_SOURCE_TBOX").is_none();
    if !datatype_bridge_route_exact(tin, source_mode) {
        return None;
    }
    let native_nominals = native_nominal_metadata_covered(tin, source_mode);
    if has_any_nominal_input(tin) && !native_nominals {
        return None;
    }
    let independent_abox_elided = independent_large_abox_profile(tin, native_nominals);
    // Native ABox saturation is scheduled separately, immediately before the
    // authoritative full consistency graph. Do not feed its subject verdicts
    // into taxonomy KPSet: those labels are ABox-influenced (measured on
    // ore_ont_9540: 18 spurious family-collapsing subsumptions), and Konclude
    // does not consume them for classification either — its KPSet reads the
    // CONCEPT saturation items, not the per-individual representation nodes.
    //
    // The COMPLETION-side coupling is a different mechanism and is NOT ABox
    // derived. `get_creation_successor_saturation_node` (u22.rs:1293) resolves a
    // creation successor only through the ontology-side concept→saturation
    // reference linkings that `build_saturation_seeds_with_deadline` installs;
    // `build_native_abox_saturation_seeds` installs none, it only writes the
    // individual-tag slots of the saturation-node vector. So the coupling reads
    // exactly the TBox concept wave, which is what Konclude's classification
    // completion tasks read (`conf_expand_created_successors_from_saturation` /
    // `conf_caching_blocking_from_saturation`, u31.rs:151-153 defaults). Folding
    // the two decisions into one `use_saturation` flag was the divergence: on
    // every native-nominal ontology KM ran its classification probes with the
    // coupling structurally off, so `saturation_cache_establish_count` and
    // `saturation_expansion_concept_count` are 0 by construction and every
    // generated successor is expanded by the tableau instead of being replayed
    // from, and blocked by, its saturation node.
    let native_saturation_coupling_requested =
        use_satcache && native_nominals && !independent_abox_elided;
    let use_saturation = use_saturation && (!native_nominals || independent_abox_elided);
    let use_satcache = use_satcache && use_saturation;
    let n_named = tin.concepts.len();
    // The classification UNIVERSE: real named classes only. `tin.concepts`
    // also carries frontend-SYNTHETIC concepts (recognition markers `Q_n`,
    // `aux_`/`def_` definers, `__`-markers) — the signature never contains
    // them, and treating them as candidate supers is ruinous: refuting one
    // marker "candidate" costs a full SAT search per subject (measured on
    // ore_ont_12653: every subject burnt its whole probe budget refuting
    // Q_n markers; with the universe filter the candidate sets collapse to
    // the real taxonomy).
    // `queries` is authoritative for declared classes. A legal source class
    // can have a local name such as `Q_real` or `aux_part`; apply the internal
    // name heuristic only to non-query helper concepts.
    let declared_queries: std::collections::HashSet<usize> =
        tin.queries.iter().map(|&query| query as usize).collect();
    let universe: std::collections::HashSet<usize> = tin
        .concepts
        .iter()
        .enumerate()
        .filter(|(index, n)| {
            (declared_queries.contains(index) || !crate::orchestrate::cb_to_ht::is_internal(n))
                && !crate::orchestrate::cb_to_ht::is_bottom(n)
        })
        .map(|(i, _)| i)
        .collect();
    let subjects: Vec<usize> = if tin.queries.is_empty() {
        let mut v: Vec<usize> = universe.iter().copied().collect();
        v.sort_unstable();
        v
    } else {
        tin.queries.iter().map(|&q| q as usize).collect()
    };
    let progress = std::env::var_os("KM_BRIDGE_PROGRESS").is_some();
    let mut out = BridgedClassification {
        consistent: true,
        unsatisfiable: Vec::new(),
        subsumptions: Vec::new(),
    };
    let subject_set: std::collections::HashSet<usize> = subjects.iter().copied().collect();
    // ONE bridged environment for the whole classification (#13): built once,
    // reset to pristine between probes (`reset_probe_env`), instead of an
    // O(TBox) rebuild per subject AND per pairwise probe.
    let t_env = std::time::Instant::now();
    let (mut algo, mut ctx, bridged) =
        fresh_bridge_env_with_trigger_absorption(tin, trigger_absorb);
    if progress {
        eprintln!(
            "BRIDGE-ENV: {:.2}s (named={}, trigger_absorb={trigger_absorb})",
            t_env.elapsed().as_secs_f64(),
            bridged.named.len()
        );
    }
    if bridged.unsupported > 0 {
        return None;
    }
    let base_budget = std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(10);
    let retry_rounds = std::env::var("KM_BRIDGE_RETRY_ROUNDS")
        .ok()
        .and_then(|s| s.parse::<u32>().ok())
        .unwrap_or(2);
    let card_nominal_profile = native_cardinality_abox_profile(tin, bridged.has_native_nominals());
    // The exact, search-free part of the relation (told names + definition
    // conjunct containment, transitively closed).  Select the richer
    // definition rule from the bridge's actual retained-native-nominal state,
    // not from broader source metadata that may describe a nominal-free
    // normalized TBox.
    let mut saturation_known_pairs = if card_nominal_profile {
        source_named_subsumer_closure(tin)
    } else if independent_abox_elided {
        HashSet::new()
    } else {
        source_told_named_subsumer_closure(tin)
    };
    saturation_known_pairs.retain(|(sub, sup)| subject_set.contains(sub) && universe.contains(sup));
    out.subsumptions
        .extend(saturation_known_pairs.iter().copied());
    let mut native_saturation_ran = false;
    // Armed once, after the precomputation saturation has COMPLETED and its
    // concept→saturation reference linkings have been verified to be present,
    // in range and disjoint from the ABox representation nodes. Stays false on
    // every route that does not run that saturation (empty-role certificate,
    // legacy nominal-only schedule, budget-aborted pass), so the coupling can
    // never read a partial or absent saturation graph.
    let mut native_saturation_coupling = false;
    let mut retained_consistency_base = false;
    let mut retained_consistency_next_id = 1_000i64;
    // The two pieces of the retained deterministic consistency base that the
    // branch-epoch journals do NOT restore (see the snapshot site below).
    let mut retained_consistency_branch_node = super::process::BranchNodeId::NONE;
    let mut retained_consistency_databox: Option<super::process::databox::ProcessingDataBox> = None;
    if bridged.has_native_nominals() {
        if independent_abox_elided {
            // ConditionalFull=false, role-independent ABox: one root per
            // distinct asserted-type signature is an exact consistency task.
            // Duplicate individuals add no constraints without nominals,
            // inequalities, or inter-individual edges.
            reset_probe_env_impl(&mut algo, &mut ctx, &bridged, false, false);
            let selected_tags = independent_abox_representative_tags(&bridged);
            if !initialize_native_nominal_state_for_tags(
                &mut algo,
                &mut ctx,
                &bridged,
                Some(&selected_tags),
            ) {
                return None;
            }
            algo.probe_budget = Some(std::time::Duration::from_secs(
                base_budget.saturating_mul(4u64.saturating_pow(retry_rounds)),
            ));
            configure_production_search(&mut algo);
            match native_nominal_consistency(&mut algo, &mut ctx, &bridged) {
                Some(false) => {
                    return Some(BridgedClassification {
                        consistent: false,
                        unsatisfiable: Vec::new(),
                        subsumptions: Vec::new(),
                    });
                }
                Some(true) => {}
                None => return None,
            }
        } else {
        let model_certified = empty_role_nominal_model_certificate(tin, &bridged);
        if progress && model_certified {
            eprintln!("BRIDGE-NOMINAL-CONSISTENCY: exact empty-role source model");
        }
        if !model_certified {
            if card_nominal_profile {
                // `CTotallyPrecomputationThread` schedules these phases in this
                // exact default conditional-full order: saturation first, then
                // one all-root consistency completion. At 198 individuals the
                // full-completion threshold suppresses representative batches.
                let mut precomputation_phase = NativePrecomputationPhase::Start;
                advance_native_precomputation_phase(
                    &mut precomputation_phase,
                    NativePrecomputationPhase::IndividualSaturation,
                )?;
                reset_probe_env_impl(&mut algo, &mut ctx, &bridged, false, false);
                if !run_bridged_saturation(&mut ctx, &bridged) {
                    return None;
                }
                native_saturation_ran = true;
                advance_native_precomputation_phase(
                    &mut precomputation_phase,
                    NativePrecomputationPhase::FullConsistencyCompletion,
                )?;
                reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, true);
                // The reset carried the saturation arenas (`preserve_saturation`);
                // verify the concept-side hand-off before anything may read it.
                native_saturation_coupling = native_saturation_coupling_requested
                    && native_saturation_coupling_metadata_covered(&ctx, &bridged);
                // Konclude's saturation-node expansion cache HANDLER is
                // constructed for every completion task
                // (`CReasonerManagerThread::createTaskHandleAlgorithm`, cpp
                // 202-204/230); only its cache CONTENT is optional. The handler
                // is what `detectIndividualNodeSaturationCached` (cpp 4769)
                // needs to run its retest at all, and the retest's FIRST branch
                // (`CSaturationNodeExpansionCacheHandler::isNodeSatisfiableCached`,
                // cpp 101-108) is cache-INDEPENDENT: a node whose label has not
                // grown since the caching was last validated
                // (`lastConfirmedConceptDescriptor == addingSortedConceptDescriptionLinker`)
                // and whose saturation node is still neither insufficient nor
                // clashed stays saturation-blocked.
                //
                // Without the handler that branch is unreachable, so EVERY
                // `propagateIndividualNodeModified` on a saturation-blocked node
                // — including link-only ones (`setIndividualNodeAncestorConnectionModified`,
                // the functional-successor reuse at u35, merges) that do not
                // touch the label — clears `PRF_SATURATIONBLOCKINGCACHED` +
                // `PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED` and replays
                // every absorbed generating concept. The block is then
                // re-established on the successor the replay creates, and the
                // cycle repeats: establishes grow with the search instead of
                // bounding it.
                //
                // The cache stays EMPTY here: `install_bridge_saturation_node_expansion_cache`
                // builds it with a NONE reader, and the two writing paths
                // (`conf_saturation_satisfiabilitiy_expansion_cache_writing`,
                // `conf_saturation_concept_unsatisfiability_saturated_cache_writing`)
                // remain false on this route, so no saturation node ever gets a
                // `cache_expansion_data` entry. `cached_deterministic_expansion_concepts`
                // (u17) and the cache-entry arm of `is_node_satisfiable_cached`
                // therefore stay inert exactly as they are today — this restores
                // the re-confirmation and nothing else.
                if native_saturation_coupling {
                    install_bridge_saturation_node_expansion_cache(&mut ctx);
                }
                // Konclude's consistency task generator reserves the first
                // positive completion-node id before the all-root job. Named
                // ABox roots use negative ids and must not leave this allocator
                // at the databox default zero.
                ctx.processing_data_box_mut()
                    .set_first_possible_individual_node_id(retained_consistency_next_id);
                algo.probe_budget = Some(std::time::Duration::from_secs(
                    base_budget.saturating_mul(4u64.saturating_pow(retry_rounds)),
                ));
                configure_production_search(&mut algo);
                // The all-root consistency completion is a
                // `CCalculationTableauCompletionTaskHandleAlgorithm` like every
                // class job, and Konclude's coupling flags are ctor/config
                // defaults, not per-task settings — the consistency task runs
                // with them too. It must: the class jobs COW-inherit this
                // graph's nodes, so a successor created here without saturation
                // blocking data stays unblocked in every later job.
                if native_saturation_coupling {
                    configure_native_nominal_completion_saturation_coupling(&mut algo);
                }
                let used_association_update_ids =
                    freeze_native_representative_association_versions(&algo);
                // The successful full-consistency completion is the association
                // writer on this profile, exactly as upstream: with
                // `fullCompletionGraphConstruction=1` the batched representative
                // computation is suppressed and
                // `CIndividualNodeBackendCacheHandler` writes the associations from
                // the completion graph via the task's representative-backend
                // updating adapter. The Stage-2 trace shows precisely that —
                // `trace-summary.txt` records 198 `backend.association
                // mode=generated` events (all `usedAssociationUpdateId=1`, i.e.
                // replacing the saturation-written v1 associations, 179 of which
                // were `loadedIncompletelyMarked=1`) emitted before the first
                // classification job at `trace.log:200`, from the patched hook in
                // `CIndividualNodeBackendCacheHandler.cpp:1852`. Only associations
                // the saturation writer could not complete are (re)written; a
                // complete one keeps its version byte for byte.
                let incomplete_associations: HashSet<Cint64> = bridged
                    .native_representative_cache
                    .borrow()
                    .as_ref()?
                    .entries
                    .iter()
                    .filter_map(|(&tag, entry)| {
                        (!entry.complete_for_precomputation()).then_some(tag)
                    })
                    .collect();
                match native_nominal_consistency(&mut algo, &mut ctx, &bridged) {
                    Some(false) => {
                        return Some(BridgedClassification {
                            consistent: false,
                            unsatisfiable: Vec::new(),
                            subsumptions: Vec::new(),
                        });
                    }
                    Some(true) => {
                        if !incomplete_associations.is_empty() {
                            write_completed_native_representative_associations(
                                &ctx,
                                &bridged,
                                NativeSuccessfulRepresentativeTask {
                                    selected_individuals: &incomplete_associations,
                                    used_association_update_ids: &used_association_update_ids,
                                },
                            )?;
                        }
                    }
                    None => {
                        return None;
                    }
                }
                advance_native_precomputation_phase(
                    &mut precomputation_phase,
                    NativePrecomputationPhase::ConsistencyDeclared,
                )?;
                retained_consistency_next_id = ctx
                    .processing_data_box_mut()
                    .next_individual_node_id(false);
                if retained_consistency_next_id <= 0 {
                    return None;
                }
                // The successful leaf supplies only the reserved positive id.
                // Roll every active alternative epoch back to the graph at the
                // first nondeterministic fork: Konclude's deterministic
                // consistency continuation base.
                let owned_epoch_count = algo
                    .or_branch_stack
                    .iter()
                    .filter(|branch| branch.own_epoch)
                    .count();
                let deterministic_branch_node = algo
                    .or_branch_stack
                    .first()
                    .map(|branch| branch.parent_used_branch_node)
                    .unwrap_or(ctx.base.used_branch_tree_node);
                if owned_epoch_count != ctx.process_context().branch_epoch_depth() {
                    return None;
                }
                while let Some(branch) = algo.or_branch_stack.pop() {
                    if branch.own_epoch {
                        ctx.pop_branch_epoch();
                    }
                }
                if ctx.process_context().branch_epoch_depth() != 0
                    || !algo.or_branch_stack.is_empty()
                {
                    return None;
                }
                // Epochs restore the graph and databox; the normal branch
                // discard path separately restores this dependency-tree
                // cursor. Manual all-branch rollback must do the same.
                ctx.base.used_branch_tree_node = deterministic_branch_node;
                ctx.branch_tree_node = deterministic_branch_node;
                install_native_nominal_backend_replay(&mut algo, &bridged);
                // PRISTINE BASE SNAPSHOT. Konclude bases EVERY class job on the
                // deterministic consistency task
                // (`consTaskData->getDeterministicSatisfiableTask()`), never on the
                // previous class job. Both pieces of that base live OUTSIDE the
                // epoch journals — the databox is a plain context field and the
                // branch-tree cursor is watermark-only memory — so they must be
                // captured here, at depth 0, and re-installed verbatim by every
                // later `renew`. Reading them back off the live context (the
                // pre-fix behaviour) chains class job N onto class job N-1.
                retained_consistency_branch_node = deterministic_branch_node;
                retained_consistency_databox = Some(ctx.processing_data_box().clone());
                ctx.push_branch_epoch();
                retained_consistency_base = true;
            } else {
                // Preserve the exact nominal-only schedule from efbcbbc. Its
                // 10621 classification is a validated full-IRI reference.
                let mut decided = None;
                for round in 0..=retry_rounds {
                    algo.probe_budget = Some(std::time::Duration::from_secs(
                        base_budget.saturating_mul(4u64.saturating_pow(round)),
                    ));
                    configure_production_search(&mut algo);
                    match native_nominal_consistency(&mut algo, &mut ctx, &bridged) {
                        Some(false) => {
                            return Some(BridgedClassification {
                                consistent: false,
                                unsatisfiable: Vec::new(),
                                subsumptions: Vec::new(),
                            });
                        }
                        Some(true) => {
                            decided = Some(());
                            break;
                        }
                        None if round < retry_rounds => {
                            reset_probe_env(&mut algo, &mut ctx, &bridged, false);
                        }
                        None => {}
                    }
                }
                decided?;
            }
        }
        }
        if !retained_consistency_base {
            reset_classification_probe_env(
                &mut algo,
                &mut ctx,
                &bridged,
                native_saturation_ran,
                independent_abox_elided,
            );
        }
    }
    let certified_unsatisfiable: std::collections::HashSet<usize> = bridged
        .certified_unsatisfiable
        .iter()
        .copied()
        .filter(|&concept| concept < n_named)
        .collect();
    out.unsatisfiable.extend(
        certified_unsatisfiable
            .iter()
            .copied()
            .filter(|concept| subject_set.contains(concept)),
    );
    let mut pending: Vec<usize> = subjects
        .iter()
        .copied()
        .filter(|subject| !certified_unsatisfiable.contains(subject))
        .collect();
    let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
    let mut kpset_state: Option<SynchronousKPSetClassState> = None;
    // Saturation-first probe answering (task #23): saturate the bridged
    // ontology ONCE in an independent calculation task and pass only the
    // extracted flags/subsumers into classification. Only explicit SATCACHE
    // coupling keeps the saturation nodes in the completion environment.
    // This mirrors Konclude's task boundary; carrying uncoupled saturation
    // process state made 541 completion probes search a different graph.
    // Then answer whole subjects from certain
    // verdicts: UNSAT-certain subjects land in `unsatisfiable`, SAT-certain
    // subjects with a sufficient label get their COMPLETE subsumer set from
    // the saturated label (Konclude's CPrecomputedSaturationSubsumerExtractor
    // consumption). Only the UNKNOWN residue runs the completion probes,
    // with the coupling (u08/u17/u22) armed when `use_satcache`.
    let mut saturation_ran = native_saturation_ran;
    let mut satcache_active = false;
    if use_saturation {
        let t_sat = std::time::Instant::now();
        let mut saturation_complete = true;
        let outcome = if use_satcache {
            let native_consistency_prefix = bridged
                .native_consistency_nominal_nondeterministic_prefix
                .borrow()
                .clone();
            saturation_complete = if native_consistency_prefix.is_some() {
                run_bridged_saturation_with_native_consistency_prefix(
                    &mut ctx,
                    &bridged,
                    native_consistency_prefix,
                    NativeSaturationAssociationMode::ReadOnlyConsumer,
                )
            } else {
                run_bridged_saturation(&mut ctx, &bridged)
            };
            // An interrupted approximation pass still contains only monotonic
            // consequences. Extracted positive labels and clash flags are
            // sound KPSet seeds; the completed-node guard prevents unfinished
            // nodes from becoming SAT-certain. Do not couple this partial graph
            // into completion below.
            let t_extract = std::time::Instant::now();
            let extracted = extract_saturation_outcome(&mut ctx, &bridged);
            if progress {
                eprintln!(
                    "BRIDGE-SAT-PHASE extract: {:.2}s",
                    t_extract.elapsed().as_secs_f64()
                );
            }
            Some(extracted)
        } else {
            bridged_saturate_with_trigger_absorption(tin, trigger_absorb)
        };
        if let Some(mut outcome) = outcome {
            // Unit-bottom certificates are completed satisfiability jobs, not
            // merely an output shortcut. Seed every active certified item so
            // KPSet can propagate its UNSAT result through the class graph and
            // the all-models barrier never observes an untested item.
            for &concept in &certified_unsatisfiable {
                outcome.sat_verdict[concept] = Some(true);
                outcome.certain_subsumers[concept] = None;
            }
            if use_satcache && std::env::var_os("KM_SAT_DEBUG").is_some() {
                for (i, c) in bridged.named.iter().enumerate() {
                    eprintln!(
                        "SAT-NAME {} concept={:?} {}",
                        i,
                        c,
                        tin.concepts.get(i).map(|n| n.as_str()).unwrap_or("?")
                    );
                }
                let n = ctx.ontology_arenas().concept_count();
                for ci in 0..n {
                    let cid = super::model::ConceptId::new(ci);
                    let c = ctx.ontology_arenas().concept(cid);
                    let ops: Vec<String> = c
                        .get_operand_list()
                        .iter()
                        .map(|l| format!("{}{:?}", if l.negated { "!" } else { "" }, l.target))
                        .collect();
                    eprintln!(
                        "SAT-CONCEPT {:?} op={} tag={} role={:?} param={} operands=[{}]",
                        cid,
                        c.get_operator_code(),
                        c.get_concept_tag(),
                        c.get_role(),
                        c.get_parameter(),
                        ops.join(",")
                    );
                }
            }
            // Output certification: only CERTIFIED labels become taxonomy
            // edges here (UNSAT-certain subjects, whose pairs are vacuous, and
            // SAT-certain subjects, whose extracted set is exact). An
            // insufficient/unknown node's label can carry branch-dependent or
            // native-ABox-derived entries (measured on ore_ont_9540: 18
            // spurious family-collapsing subsumptions from ABox-influenced
            // labels emitted unconditionally); those subjects stay in the
            // residue below, where every candidate pair is re-derived by the
            // completion path before it may reach the output.
            for &s in &pending {
                if !outcome.label_certified(s) {
                    continue;
                }
                for &c in &outcome.known_subsumers[s] {
                    if c != s && universe.contains(&c) && saturation_known_pairs.insert((s, c)) {
                        out.subsumptions.push((s, c));
                    }
                }
            }
            let mut answered_unsat = 0usize;
            let mut answered_sat = 0usize;
            pending.retain(|&s| match outcome.sat_verdict[s] {
                Some(true) => {
                    if std::env::var_os("KM_SAT_DEBUG").is_some() {
                        eprintln!(
                            "SAT-UNSAT-VERDICT subject {} ({})",
                            s,
                            tin.concepts.get(s).map(|n| n.as_str()).unwrap_or("?")
                        );
                    }
                    out.unsatisfiable.push(s);
                    answered_unsat += 1;
                    false
                }
                Some(false) => {
                    if outcome.certain_subsumers[s].is_some() {
                        answered_sat += 1;
                        false
                    } else {
                        true
                    }
                }
                None => true,
            });
            if std::env::var_os("KM_BRIDGE_SAT_RESIDUE").is_some() {
                for &subject in &pending {
                    eprintln!(
                        "BRIDGE-SATURATION-RESIDUE subject={subject} class={}",
                        tin.concepts.get(subject).map(String::as_str).unwrap_or("?")
                    );
                }
            }
            // Konclude does not run the insufficient residue in signature
            // order.  Its KPSet classifier builds the predecessor graph from
            // every saturation label, then schedules root classes before
            // their descendants.  The bridge executes jobs synchronously, but
            // consumes the same production KPSet order. Labels drive that
            // SCHEDULING unconditionally; only certified labels (see
            // `SaturationOutcome::label_certified`) may enter the trusted
            // subsumer sets that `certain_subsumer` accepts without a probe.
            let known_subsumers_entailed: Vec<bool> = (0..n_named)
                .map(|subject| outcome.label_certified(subject))
                .collect();
            let state = classifier.initialize_synchronous_kpset_from_saturation_data(
                &bridged.named,
                &outcome.sat_verdict,
                &outcome.certain_subsumers,
                &outcome.known_subsumers,
                &known_subsumers_entailed,
                &pending,
                ctx.ontology_arenas().concepts(),
            );
            pending = state.ordered_subjects.clone();
            kpset_state = Some(state);
            saturation_ran = use_satcache && saturation_complete;
            satcache_active = use_satcache && saturation_complete;
            if progress {
                eprintln!(
                    "BRIDGE-SATURATION{}: {:.2}s, answered {} unsat + {} sat of {} subjects ({} residue to probes, known-label-subjects={}, satcache={})",
                    if saturation_complete { "" } else { "-PARTIAL" },
                    t_sat.elapsed().as_secs_f64(),
                    answered_unsat,
                    answered_sat,
                    answered_unsat + answered_sat + pending.len(),
                    pending.len(),
                    outcome
                        .known_subsumers
                        .iter()
                        .filter(|subsumers| !subsumers.is_empty())
                        .count(),
                    satcache_active,
                );
            }
        }
    }
    if kpset_state.is_none() {
        let mut empty_verdict = vec![None; n_named];
        for &concept in &certified_unsatisfiable {
            empty_verdict[concept] = Some(true);
        }
        let empty_certain = vec![None; n_named];
        let mut known = vec![Vec::new(); n_named];
        for &(sub, sup) in &saturation_known_pairs {
            if sub < n_named && sup < n_named {
                known[sub].push(sup);
            }
        }
        // Source-closure subsumers (told names plus definition conjunct
        // containment) are entailed by construction, so they remain fully
        // trusted KPSet subsumer entries.
        let known_subsumers_entailed = vec![true; n_named];
        let state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &empty_verdict,
            &empty_certain,
            &known,
            &known_subsumers_entailed,
            &pending,
            ctx.ontology_arenas().concepts(),
        );
        pending = state.ordered_subjects.clone();
        kpset_state = Some(state);
    }
    // Diagnostic split: retain Konclude's saturation-label replay/blocking but
    // suppress only the associated-expansion cache shared across completion
    // probes.  This distinguishes a bad raw saturation label from a bad
    // completion-cache write without disabling the whole saturation coupling.
    if satcache_active && std::env::var_os("KM_HT_NO_ASSOC_EXP_CACHE").is_none() {
        install_bridge_saturation_node_expansion_cache(&mut ctx);
    }
    if std::env::var_os("KM_HT_NO_SAT_EXP_CACHE").is_none() {
        install_bridge_satisfiable_expander_cache(&mut ctx);
    }
    let mut kpset_state = kpset_state.expect("synchronous KPSet state initialized");
    // Diagnostic scheduler replay: accept an explicit comma-separated subject
    // order so a Konclude trace can be replayed without baking ontology names or
    // ids into the reasoner. Production never sets these variables.
    if let Ok(order) = std::env::var("KM_BRIDGE_ORDER_SUBJECTS") {
        let ordered: Vec<usize> = order
            .split(',')
            .filter_map(|value| value.trim().parse().ok())
            .collect();
        let rank: HashMap<usize, usize> = ordered
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, subject)| (subject, rank))
            .collect();
        let original_rank: HashMap<usize, usize> = pending
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, subject)| (subject, rank))
            .collect();
        pending.sort_by_key(|subject| {
            (
                rank.get(subject).copied().unwrap_or(usize::MAX),
                original_rank.get(subject).copied().unwrap_or(usize::MAX),
            )
        });
        if std::env::var_os("KM_BRIDGE_ORDER_ONLY").is_some() {
            pending.retain(|subject| rank.contains_key(subject));
        }
    }
    // Diagnostic only: retain a single post-saturation subject while preserving
    // construction of the complete KPSet graph and saturation cache above.
    if let Ok(subject) = std::env::var("KM_BRIDGE_ONLY_SUBJECT") {
        if let Ok(subject) = subject.parse::<usize>() {
            pending.retain(|&candidate| candidate == subject);
        }
    }
    let subject_by_item: HashMap<usize, usize> = kpset_state
        .item_ids
        .iter()
        .enumerate()
        .filter_map(|(subject, item)| item.is_some().then_some((item.index(), subject)))
        .collect();
    let subject_by_concept: HashMap<ConceptId, usize> = bridged
        .named
        .iter()
        .copied()
        .enumerate()
        .map(|(subject, concept)| (concept, subject))
        .collect();
    // Classify one subject end-to-end (read-off + any needed verification
    // probes) into `out`. `None` ⇔ some probe STOPped — the subject is
    // DEFERRED, `out` untouched for it (pairs are only pushed once every
    // probe of the subject has a verdict).
    // KM_BRIDGE_FRESH_ENV=1 (diagnostic): rebuild the env per probe instead
    // of resetting — the pre-#13 isolation, for A/B against the reset path.
    let fresh_env = std::env::var_os("KM_BRIDGE_FRESH_ENV").is_some();
    // KM_BRIDGE_COW_CONFIRM=1 (opt-in): re-run poison-deferred probes under
    // COW branch epochs to CONFIRM them instead of deferring. Correct
    // (complete restore ⇒ classically complete) but measured too slow inside
    // the probe budgets on the recognition family (the uniform first-touch
    // journal cost — ore_ont_12653 subjects blew their 900 s validation
    // window). Becomes the default once per-node COW localization lands.
    let cow_confirm = std::env::var_os("KM_BRIDGE_COW_CONFIRM").is_some();
    // Deterministic-subsumer short-circuit (Konclude parity): a branch-tag-gated
    // subsumer recorded on the item's subsumer set is entailed in every model,
    // so the pairwise loop accepts it directly instead of running a full
    // satisfiability probe. This mirrors the trust the authoritative read-off
    // already grants deterministic label positives; disable with
    // `KM_HT_NO_DET_SUBSUMER=1` for an A/B against the probe-every-pair path.
    let deterministic_subsumer_shortcut = std::env::var_os("KM_HT_NO_DET_SUBSUMER").is_none();
    let probe_start_id = if retained_consistency_base {
        retained_consistency_next_id
    } else {
        1_000
    };
    let mut synchronous_satisfiable_phase_finished = false;
    let mut classify_one = |s: usize,
                            algo: &mut CompletionTaskHandleAlgorithm,
                            ctx: &mut CalculationAlgorithmContextBase,
                            out: &mut BridgedClassification,
                            prepare_only: bool|
     -> Option<()> {
        // Konclude does not begin possible-subsumption calculations until
        // every satisfiability job has returned.  The first verification call
        // is the synchronous barrier: build the KPSet propagation graph and
        // prune the completed maps before looking at a single pair.
        if !prepare_only && !synchronous_satisfiable_phase_finished {
            let t_barrier = std::time::Instant::now();
            classifier.finish_synchronous_satisfiable_phase(
                &mut kpset_state,
                ctx.ontology_arenas().concepts(),
            );
            if progress {
                eprintln!(
                    "BRIDGE-SAT-PHASE kpset-barrier: {:.2}s",
                    t_barrier.elapsed().as_secs_f64()
                );
            }
            synchronous_satisfiable_phase_finished = true;
        }
        let t_subj = std::time::Instant::now();
        let mut renew = |algo: &mut CompletionTaskHandleAlgorithm,
                         ctx: &mut CalculationAlgorithmContextBase,
                         cow: bool|
         -> Option<()> {
            if retained_consistency_base {
                restore_retained_classification_base(
                    algo,
                    ctx,
                    &bridged,
                    retained_consistency_databox.as_ref()?,
                    retained_consistency_branch_node,
                    retained_consistency_next_id,
                )?;
            } else if fresh_env {
                let budget = algo.probe_budget;
                let (a2, c2, _b2) = fresh_bridge_env_with_trigger_absorption(tin, trigger_absorb);
                *algo = a2;
                *ctx = c2;
                algo.probe_budget = budget;
            } else {
                reset_classification_probe_env(
                    algo,
                    ctx,
                    &bridged,
                    saturation_ran,
                    independent_abox_elided,
                );
            }
            configure_production_search(algo);
            if ctx.base.used_sat_exp_cache_handler.is_some() {
                // CCalculationTableauCompletionTaskHandleAlgorithm defaults,
                // cpp 194-199 and readCalculationConfig cpp 536-539.
                algo.conf_sat_exp_cache_retrieval = true;
                algo.conf_sat_exp_cache_concept_expansion = true;
                algo.conf_sat_exp_cache_satisfiable_blocking = true;
                algo.conf_sat_exp_cache_writing = true;
            }
            // Saturation-node coupling (task #24 wave 2): Konclude's production
            // completion profile — expand created successors from saturation +
            // caching-blocking from saturation, including cache revalidation
            // after modification. Successful jobs also extend the shared
            // associated-expansion cache. Re-armed after every reset because
            // the reset rebuilds the algorithm. The KM_BRIDGE_FRESH_ENV
            // diagnostic path rebuilds an UNsaturated env, so the coupling
            // stays off there (the lookups would find no reference linkings).
            if satcache_active && !fresh_env {
                configure_production_completion_saturation_coupling(algo);
                algo.conf_saturation_satisfiabilitiy_expansion_cache_writing =
                    std::env::var_os("KM_HT_NO_SAT_CACHE_WRITING").is_none();
            } else if native_saturation_coupling && !fresh_env {
                // Native-nominal route: the same Konclude coupling, but reading
                // the precomputation saturation instead of a classification-time
                // pass, with the nominal-connected fail-closed legs. The shared
                // associated-expansion cache stays OUT — it is installed only
                // under `satcache_active` above, so no cross-probe deterministic
                // expansion is replayed here and
                // `conf_saturation_satisfiabilitiy_expansion_cache_writing`
                // stays false, matching Konclude's own default (u31.rs:155).
                configure_native_nominal_completion_saturation_coupling(algo);
            }
            // VERDICT TRUST HIERARCHY, escalation leg: re-run an untrusted
            // probe under COW branch epochs — complete per-alternative state
            // restore, so chronological search is classically complete and
            // the unrestored-advance poison never fires. Slower (journaling)
            // — used only to CONFIRM a plain-mode verdict tainted by
            // phantomized nodes. Oracle-validated (plain/COW matrix).
            if cow {
                algo.conf_inprocess_cow = true;
            }
            Some(())
        };
        let derived = {
            let item = &kpset_state
                .ontology_item
                .get_concept_satisfiable_test_item_container()[kpset_state.item_ids[s].index()];
            if item.is_result_unsatisfiable_derivated() {
                out.unsatisfiable.push(s);
                return Some(());
            }
            item.is_result_satisfiable_derivated().then(|| {
                let mut candidates: Vec<usize> = item
                    .get_subsuming_concept_item_list()
                    .iter()
                    .filter_map(|known| subject_by_item.get(&known.index()).copied())
                    .collect();
                if let Some(possible) = item.get_possible_subsumption_map_ref() {
                    candidates.extend(
                        possible
                            .concepts()
                            .into_iter()
                            .filter_map(|concept| subject_by_concept.get(&concept).copied()),
                    );
                }
                candidates.sort_unstable();
                candidates.dedup();
                candidates
            })
        };
        let (mut subs, authoritative, root) = if let Some(subs) = derived {
            if progress {
                eprintln!(
                    "BRIDGE-KPSET-DERIVED subject {s}: {} candidates, no satisfiability job",
                    subs.len()
                );
            }
            (subs, false, None)
        } else {
            renew(algo, ctx, false)?;
            let mut next_indi_id: i64 = probe_start_id;
            let mut readoff = bridged_classify_subject_with_root(
                algo,
                ctx,
                &bridged,
                &mut next_indi_id,
                s,
                n_named,
            );
            if readoff.is_none() && algo.completeness_poisoned && cow_confirm {
                // Plain search untrusted (an unrestored advance phantomized
                // nodes) — the poison deferred the read-off. Escalate to COW.
                renew(algo, ctx, true)?;
                let mut id_cow: i64 = probe_start_id;
                readoff = bridged_classify_subject_with_root(
                    algo,
                    ctx,
                    &bridged,
                    &mut id_cow,
                    s,
                    n_named,
                );
            }
            if readoff.is_none() && progress {
                eprintln!(
                    "BRIDGE-DEFER subject {s}: READ-OFF stop after {:.1}s (signal={:?}, nodes={}, sat-blocks={}, sat-expanded={})",
                    t_subj.elapsed().as_secs_f64(),
                    ctx.pending_signal(),
                    ctx.process_context().node_count(),
                    algo.saturation_cache_establish_count,
                    algo.saturation_expansion_concept_count,
                );
            }
            let (subs, authoritative, root) = readoff?;
            (subs, authoritative, Some(root))
        };
        if let Some(root) = root {
            if !(authoritative && subs.len() == n_named) {
                analyse_kpset_completion_model(&mut classifier, &mut kpset_state, s, root, ctx);
            }
        }
        if !authoritative {
            // Konclude does not restrict possible-subsumption tests to the
            // named concepts visible in the completion model's root label.
            // The satisfiability job emits
            // CClassificationInitializePossibleClassSubsumptionMessageData;
            // COptimizedKPSetClassSubsumptionClassifierThread.cpp
            // 1835-1904 installs that message's candidates in the possible
            // map, and lines 868-895 schedule every remaining entry after the
            // satisfiability phase. `analyse_kpset_completion_model` above is
            // the synchronous message delivery. Refresh `subs` from the map
            // after delivery so this synchronous driver executes the same
            // transition instead of testing only the pre-message read-off.
            let item = &kpset_state
                .ontology_item
                .get_concept_satisfiable_test_item_container()[kpset_state.item_ids[s].index()];
            subs.extend(
                item.get_subsuming_concept_item_list()
                    .iter()
                    .filter_map(|known| subject_by_item.get(&known.index()).copied()),
            );
            if let Some(possible) = item.get_possible_subsumption_map_ref() {
                subs.extend(
                    possible
                        .concepts()
                        .into_iter()
                        .filter_map(|concept| subject_by_concept.get(&concept).copied()),
                );
            }
            subs.sort_unstable();
            subs.dedup();
        }
        // Optional diagnostic filter: intersect a second model obtained with
        // reversed disjunction order. This is sound, but it is not part of
        // Konclude's KPSet pipeline. Konclude consumes the first model's
        // possible-subsumption/pseudo-model messages and verifies the remaining
        // pairs. On the disjunction family a second full read-off usually
        // removes only one candidate and costs far more than those pair checks.
        if !authoritative && std::env::var_os("KM_BRIDGE_REVERSE_READOFF").is_some() {
            renew(algo, ctx, false)?;
            algo.conf_or_reverse = true;
            let mut id_rev: i64 = probe_start_id;
            if let Some((subs_rev, _, reverse_root)) =
                bridged_classify_subject_with_root(algo, ctx, &bridged, &mut id_rev, s, n_named)
            {
                analyse_kpset_completion_model(
                    &mut classifier,
                    &mut kpset_state,
                    s,
                    reverse_root,
                    ctx,
                );
                if subs_rev.len() < n_named {
                    let keep: std::collections::HashSet<usize> = subs_rev.into_iter().collect();
                    let before = subs.len();
                    subs.retain(|c| keep.contains(c));
                    if progress && subs.len() != before {
                        let names: Vec<&str> = subs
                            .iter()
                            .take(48)
                            .map(|&c| tin.concepts[c].as_str())
                            .collect();
                        eprintln!(
                            "BRIDGE-INTERSECT subject {s} ({}): candidates {before} -> {} [{}]",
                            tin.concepts[s],
                            subs.len(),
                            names.join(",")
                        );
                    }
                }
            }
            algo.conf_or_reverse = false;
        }
        // The subject-unsatisfiable signal is the FULL index range
        // (authoritative). A tiny ontology can legitimately have a subject
        // subsumed by every named concept, so disambiguate with a direct
        // single-seed unsat probe.
        if authoritative && subs.len() == n_named {
            renew(algo, ctx, false)?;
            let mut id2: i64 = probe_start_id;
            let mut v = bridged_unsat(algo, ctx, &bridged, &mut id2, &[(bridged.named[s], false)]);
            if v.is_none() && algo.completeness_poisoned && cow_confirm {
                renew(algo, ctx, true)?;
                let mut id_cow: i64 = probe_start_id;
                v = bridged_unsat(
                    algo,
                    ctx,
                    &bridged,
                    &mut id_cow,
                    &[(bridged.named[s], false)],
                );
            }
            match v {
                Some(true) => {
                    out.unsatisfiable.push(s);
                    return Some(());
                }
                Some(false) => {} // genuinely subsumed by everything — keep pairs
                None => return None,
            }
        }
        // Restrict candidates to the classification universe (real named
        // classes; see the `universe` doc above). AFTER the full-range unsat
        // disambiguation — that signal is defined on the raw read-off.
        subs.retain(|&c| c == s || universe.contains(&c));
        if authoritative {
            for c in subs {
                if c != s && !saturation_known_pairs.contains(&(s, c)) {
                    out.subsumptions.push((s, c));
                }
            }
            return Some(());
        }
        if prepare_only {
            // The completion-model analyser above has delivered Konclude's
            // deterministic-subsumer, possible-subsumer, and pseudo-model
            // messages into the persistent KPSet item.  Pair verification is
            // intentionally deferred until every subject reaches this point.
            return Some(());
        }
        // Non-deterministic subject: verify each candidate pairwise. Collect
        // locally and commit only when EVERY probe answered, so a deferred
        // subject leaves no partial pairs behind for the retry round.
        let mut pairs: Vec<(usize, usize)> = Vec::new();
        for c in subs {
            if c == s {
                continue;
            }
            if saturation_known_pairs.contains(&(s, c)) {
                continue;
            }
            // Deterministic subsumers were extracted branch-tag gated, so
            // `s ⊑ c` is entailed. Konclude records them as subsumptions and
            // never tests them; accept without a probe (see the authoritative
            // read-off above, which trusts deterministic positives the same
            // way). Recorded directly like an authoritative subsumer rather
            // than routed through `interprete_subsumption_result`, so retries
            // recompute idempotently and no propagation state is mutated.
            if deterministic_subsumer_shortcut && kpset_state.certain_subsumer(s, c) {
                if progress {
                    eprintln!(
                        "BRIDGE-KPSET-SKIP {} v {}: deterministic-subsumer",
                        tin.concepts[s], tin.concepts[c]
                    );
                }
                pairs.push((s, c));
                continue;
            }
            if let Some((confirmed, invalid)) = kpset_state.candidate_state(s, c) {
                if invalid {
                    if progress {
                        eprintln!(
                            "BRIDGE-KPSET-SKIP {} v {}: propagated-false",
                            tin.concepts[s], tin.concepts[c]
                        );
                    }
                    continue;
                }
                if confirmed {
                    if progress {
                        eprintln!(
                            "BRIDGE-KPSET-SKIP {} v {}: propagated-true",
                            tin.concepts[s], tin.concepts[c]
                        );
                    }
                    pairs.push((s, c));
                    continue;
                }
            }
            if kpset_state.pseudo_model_refutes(s, c) {
                if progress {
                    eprintln!(
                        "BRIDGE-KPSET-VERIFY {} v {}: pseudo-model-false is advisory",
                        tin.concepts[s], tin.concepts[c]
                    );
                }
                // A pseudo-model is a structural summary, not a model
                // certificate. The synchronous bridge does not reproduce all
                // invariants of Konclude's asynchronous message lifecycle. On
                // 10621 this shortcut falsely refuted Flagellum <= Organ_part.
                // Retain the complete A and not-B satisfiability probe below.
            }
            if progress {
                eprintln!(
                    "BRIDGE-PAIR-START {} v {}",
                    tin.concepts[s], tin.concepts[c]
                );
            }
            renew(algo, ctx, false)?;
            let mut id2: i64 = probe_start_id;
            let mut v = bridged_unsat(
                algo,
                ctx,
                &bridged,
                &mut id2,
                &[(bridged.named[s], false), (bridged.named[c], true)],
            );
            if v.is_none() && algo.completeness_poisoned && cow_confirm {
                // plain verdict untrusted — confirm under COW epochs
                renew(algo, ctx, true)?;
                let mut id_cow: i64 = probe_start_id;
                v = bridged_unsat(
                    algo,
                    ctx,
                    &bridged,
                    &mut id_cow,
                    &[(bridged.named[s], false), (bridged.named[c], true)],
                );
            }
            match v {
                Some(true) => {
                    if progress {
                        eprintln!(
                            "BRIDGE-PAIR-END {} v {}: true",
                            tin.concepts[s], tin.concepts[c]
                        );
                    }
                    kpset_state
                        .ontology_item
                        .inc_running_possible_subsumption_tests_count(1);
                    classifier.interprete_subsumption_result(
                        &mut kpset_state.ontology_item,
                        bridged.named[s],
                        bridged.named[c],
                        true,
                        ctx.ontology_arenas().concepts(),
                    );
                    pairs.push((s, c))
                }
                Some(false) => {
                    if progress {
                        eprintln!(
                            "BRIDGE-PAIR-END {} v {}: false",
                            tin.concepts[s], tin.concepts[c]
                        );
                    }
                    kpset_state
                        .ontology_item
                        .inc_running_possible_subsumption_tests_count(1);
                    classifier.interprete_subsumption_result(
                        &mut kpset_state.ontology_item,
                        bridged.named[s],
                        bridged.named[c],
                        false,
                        ctx.ontology_arenas().concepts(),
                    );
                }
                None => {
                    if progress {
                        eprintln!(
                            "BRIDGE-DEFER subject {s}: PAIR {}v{} stop after {:.1}s subj-total",
                            tin.concepts[s],
                            tin.concepts[c],
                            t_subj.elapsed().as_secs_f64()
                        );
                    }
                    return None;
                }
            }
        }
        out.subsumptions.extend(pairs);
        // A non-deterministic subject can also be unsatisfiable without the
        // read-off reporting the full range (a clash IS reported full-range,
        // so this is only reachable when the drive found a model — the
        // subject is satisfiable; nothing to check).
        Some(())
    };
    // Phase 1: run every satisfiability-model job and deliver all of its
    // classification messages.  This is Konclude's satisfiability phase; no
    // possible-subsumption pair may be scheduled before its all-jobs barrier.
    let verification_subjects = pending.clone();
    let t_prepare = std::time::Instant::now();
    let mut permanent_defer = 0usize;
    for round in 0..=retry_rounds {
        algo.probe_budget = Some(std::time::Duration::from_secs(
            base_budget.saturating_mul(4u64.saturating_pow(round)),
        ));
        let total = pending.len();
        let mut deferred: Vec<usize> = Vec::new();
        for (k, &s) in pending.iter().enumerate() {
            if classify_one(s, &mut algo, &mut ctx, &mut out, true).is_none() {
                if algo.completeness_poisoned {
                    permanent_defer += 1;
                } else {
                    deferred.push(s);
                }
            }
            log_bridge_satisfiable_expander_cache_stats(&ctx, "prepare", s);
            if progress && (k % 64 == 0 || k + 1 == total || permanent_defer > 0) {
                eprintln!(
                    "BRIDGE-PREPARE round {round} subject {}/{total} deferred={} permanent={}",
                    k + 1,
                    deferred.len(),
                    permanent_defer
                );
            }
            if permanent_defer > 0 {
                // One deterministic defer decides the whole classification
                // (complete-or-defer contract) — finishing the remaining
                // subjects is pure waste, and in the race the bridge worker
                // shares the node with the CB engine.
                break;
            }
        }
        pending = deferred;
        if pending.is_empty() || permanent_defer > 0 {
            break;
        }
    }
    if !pending.is_empty() || permanent_defer > 0 {
        if progress {
            eprintln!(
                "BRIDGE-PREPARE defer: {} budget + {} permanent subjects without a model",
                pending.len(),
                permanent_defer
            );
        }
        return None;
    }

    if progress {
        eprintln!(
            "BRIDGE-SAT-PHASE prepare-total: {:.2}s ({} subjects)",
            t_prepare.elapsed().as_secs_f64(),
            verification_subjects.len()
        );
    }

    // Phase 2: the first call crosses the all-models barrier inside
    // `classify_one`, ports Konclude's global KPSet graph/map pruning, and
    // then verifies only candidates that remain unknown.  Successful model
    // jobs marked their items derived, so they are not rerun here.
    pending = verification_subjects;
    let t_verify = std::time::Instant::now();
    permanent_defer = 0;
    for round in 0..=retry_rounds {
        algo.probe_budget = Some(std::time::Duration::from_secs(
            base_budget.saturating_mul(4u64.saturating_pow(round)),
        ));
        let total = pending.len();
        let mut deferred: Vec<usize> = Vec::new();
        for (k, &s) in pending.iter().enumerate() {
            if classify_one(s, &mut algo, &mut ctx, &mut out, false).is_none() {
                if algo.completeness_poisoned {
                    permanent_defer += 1;
                } else {
                    deferred.push(s);
                }
            }
            log_bridge_satisfiable_expander_cache_stats(&ctx, "verify", s);
            if progress && (k % 64 == 0 || k + 1 == total || permanent_defer > 0) {
                eprintln!(
                    "BRIDGE-VERIFY round {round} subject {}/{total} deferred={} permanent={}",
                    k + 1,
                    deferred.len(),
                    permanent_defer
                );
            }
            if permanent_defer > 0 {
                break;
            }
        }
        pending = deferred;
        if pending.is_empty() || permanent_defer > 0 {
            break;
        }
    }
    if progress {
        eprintln!(
            "BRIDGE-SAT-PHASE verify-total: {:.2}s",
            t_verify.elapsed().as_secs_f64()
        );
    }
    // KM_HT_UNSATCACHE diagnostics: writes vs hits across the WHOLE
    // classification (the handler is carried across probe resets, so these
    // are cumulative). Interprets a null A/B result: 0 writes = the u22
    // guards rejected every candidate line; writes>0 hits=0 = the read
    // points never matched (label shapes / caching-tag mismatch).
    if progress {
        if let Some(state) = ctx.base.take_used_unsatisfiable_cache_handler() {
            eprintln!(
                "BRIDGE-CLASSIFY unsatcache: {} lines written, {} read hits",
                state.handler.stat_write_count, state.handler.stat_hit_count
            );
            ctx.base.restore_used_unsatisfiable_cache_handler(state);
        }
    }
    if !pending.is_empty() || permanent_defer > 0 {
        if progress {
            eprintln!(
                "BRIDGE-CLASSIFY defer: {} budget + {} permanent subjects without verdict",
                pending.len(),
                permanent_defer
            );
        }
        return None;
    }
    out.unsatisfiable.sort_unstable();
    out.unsatisfiable.dedup();
    if !out.unsatisfiable.is_empty() {
        let unsatisfiable: std::collections::HashSet<usize> =
            out.unsatisfiable.iter().copied().collect();
        out.subsumptions
            .retain(|(subject, _)| !unsatisfiable.contains(subject));
    }
    out.subsumptions.sort_unstable();
    out.subsumptions.dedup();
    Some(out)
}

// ---------------------------------------------------------------------------
// Tests: ofn text → frontend → cb_to_ht::convert → bridge → verdicts.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::super::completion::strategy::ConceptProcessingPriorityStrategy;
    use super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::process::sat_ref::ExtendedConceptReferenceLinkingData;
    use super::*;

    fn source_equivalence(
        left: crate::frontend::syntax::Concept,
        right: crate::frontend::syntax::Concept,
    ) -> crate::json_io::SourceAxiomMeta {
        crate::json_io::SourceAxiomMeta {
            kind: crate::json_io::SourceAxiomKind::Equivalent,
            left,
            right,
        }
    }

    fn native_nominal_meta(
        entries: Vec<(&str, &str, Vec<crate::frontend::syntax::Concept>)>,
        different: Vec<(&str, &str)>,
    ) -> crate::json_io::NominalAboxMeta {
        crate::json_io::NominalAboxMeta {
            complete: true,
            individuals: entries
                .into_iter()
                .map(
                    |(individual, proxy, assertions)| crate::json_io::NominalIndividualMeta {
                        individual: individual.into(),
                        proxies: vec![proxy.into()],
                        assertions,
                        assertion_markers: Vec::new(),
                    },
                )
                .collect(),
            same: Vec::new(),
            different: different
                .into_iter()
                .map(|(left, right)| (left.into(), right.into()))
                .collect(),
            role_assertions: Vec::new(),
            negative_role_assertions: Vec::new(),
            unsupported: Vec::new(),
        }
    }

    fn nominal_role(
        role: &str,
        source: &str,
        target: &str,
    ) -> crate::json_io::NominalRoleAssertionMeta {
        crate::json_io::NominalRoleAssertionMeta {
            role: role.into(),
            source: source.into(),
            target: target.into(),
        }
    }

    fn basic_native_role_input(
        roles: &[&str],
        nominal_abox: crate::json_io::NominalAboxMeta,
    ) -> TInput {
        use crate::frontend::syntax::Concept as C;

        fn contains_number(concept: &C) -> bool {
            match concept {
                C::AtLeast(..) | C::AtMost(..) => true,
                C::Not(operand) | C::Exists(_, operand) | C::Forall(_, operand) => {
                    contains_number(operand)
                }
                C::And(operands) | C::Or(operands) => operands.iter().any(contains_number),
                C::Name(_) | C::Top | C::Bottom | C::Nominal(_) | C::HasSelf(_) => false,
            }
        }
        let number = nominal_abox
            .individuals
            .iter()
            .flat_map(|individual| &individual.assertions)
            .any(contains_number);
        TInput {
            concepts: vec![
                "A".into(),
                "__nom__a".into(),
                "__nom__b".into(),
                "__nom__c".into(),
            ],
            roles: roles.iter().map(|role| (*role).into()).collect(),
            queries: vec![0],
            number,
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            nominal_abox,
            ..Default::default()
        }
    }

    fn cached_native_role_input() -> TInput {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let mut meta = native_nominal_meta(
            vec![
                (
                    "a",
                    "__nom__a",
                    vec![C::AtMost(5, R::Name("r".into()), Box::new(C::Top))],
                ),
                ("b", "__nom__b", vec![]),
                ("c", "__nom__c", vec![]),
            ],
            vec![],
        );
        meta.role_assertions.push(nominal_role("r", "a", "b"));
        meta.role_assertions.push(nominal_role("s", "c", "a"));
        basic_native_role_input(&["r", "s"], meta)
    }

    fn force_native_association_incomplete(
        bridged: &Bridged,
        individual_tag: Cint64,
        completely_propagated: bool,
    ) {
        let mut cache = bridged.native_representative_cache.borrow_mut();
        let entry = cache
            .as_mut()
            .expect("representative cache")
            .entries
            .get_mut(&individual_tag)
            .expect("native association");
        entry.completely_saturated = false;
        entry.completely_handled = false;
        entry.completely_propagated = completely_propagated;
        entry.insufficient = true;
    }

    fn source_subclass(
        left: crate::frontend::syntax::Concept,
        right: crate::frontend::syntax::Concept,
    ) -> crate::json_io::SourceAxiomMeta {
        crate::json_io::SourceAxiomMeta {
            kind: crate::json_io::SourceAxiomKind::SubClass,
            left,
            right,
        }
    }

    fn empty_role_model_input() -> TInput {
        use crate::frontend::syntax::Concept as C;

        TInput {
            concepts: vec![
                "A".into(),
                "B".into(),
                "__nom__a".into(),
                "__nom__b".into(),
                "__dt__value".into(),
            ],
            roles: vec!["r".into(), "s".into(), "p".into()],
            queries: vec![0, 1],
            source_axioms: vec![
                source_subclass(C::Name("A".into()), C::Name("B".into())),
                crate::json_io::SourceAxiomMeta {
                    kind: crate::json_io::SourceAxiomKind::Equivalent,
                    left: C::Name("A".into()),
                    right: C::Name("B".into()),
                },
                crate::json_io::SourceAxiomMeta {
                    kind: crate::json_io::SourceAxiomKind::Disjoint,
                    left: C::Name("A".into()),
                    right: C::Name("B".into()),
                },
                source_subclass(
                    C::Name("A".into()),
                    C::Exists(
                        crate::frontend::syntax::Role::Name("p".into()),
                        Box::new(C::Name("__dt__value".into())),
                    ),
                ),
            ],
            // An ordinary guarded role inclusion is vacuous in the exhibited
            // empty-role interpretation and exercises the RBox safety gate.
            clauses: vec![HtClause {
                body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
                head: vec![HAtom::Role { r: 1, s: 0, t: 1 }],
            }],
            nominal_abox: native_nominal_meta(
                vec![
                    ("a", "__nom__a", vec![C::Top]),
                    ("b", "__nom__b", vec![C::Top]),
                ],
                vec![("a", "b")],
            ),
            ..Default::default()
        }
    }

    #[test]
    fn semantic_number_flag_selects_native_abox_profile_without_card_defs() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let mut meta = native_nominal_meta(
            vec![
                (
                    "a",
                    "__nom__a",
                    vec![C::AtMost(1, R::Name("r".into()), Box::new(C::Top))],
                ),
                ("b", "__nom__b", vec![]),
                ("c", "__nom__c", vec![]),
            ],
            vec![],
        );
        meta.role_assertions
            .extend([nominal_role("r", "a", "b"), nominal_role("r", "a", "c")]);
        let tin = basic_native_role_input(&["r"], meta);
        assert!(tin.number);
        assert!(
            tin.card_defs.is_empty(),
            "the regression must exercise KM_NO_HT_CARD-style input"
        );

        let (algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(native_cardinality_abox_profile(
            &tin,
            bridged.has_native_nominals()
        ));
        assert!(
            bridged.direct_native_role_assertions,
            "typed role assertions must replace the legacy existential spelling"
        );
        assert!(algo.conf_direct_rule_preprocessing);
        assert!(algo.conf_cache_oriented_or_ordering);

        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("the no-card_defs mixed ABox profile must complete");
        assert!(
            result.consistent,
            "without DifferentIndividuals, the two R-neighbours may merge"
        );
    }

    #[test]
    fn conditional_full_profile_rejects_konclude_threshold_sized_abox() {
        let mut tin = cached_native_role_input();
        let template = tin.nominal_abox.individuals[0].clone();
        tin.nominal_abox.individuals.resize(9_999, template.clone());
        assert!(native_cardinality_abox_profile(&tin, true));
        tin.nominal_abox.individuals.push(template);
        assert!(
            !native_cardinality_abox_profile(&tin, true),
            "Konclude's conditional-full profile is strict below 10,000 individuals"
        );
    }

    #[test]
    fn independent_large_abox_profile_rejects_every_coupling_fence() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let mut clean = cached_native_role_input();
        clean.nominal_abox.role_assertions.clear();
        clean.number = true;
        clean.source_axioms = vec![source_subclass(C::Name("A".into()), C::Top)];
        let template = clean.nominal_abox.individuals[0].clone();
        clean
            .nominal_abox
            .individuals
            .resize(CONDITIONAL_FULL_INDIVIDUAL_LIMIT, template);
        assert!(independent_large_abox_profile(&clean, true));
        assert!(!independent_large_abox_profile(&clean, false));

        let mut coupled = clean.clone();
        coupled.nominal_abox.individuals.pop();
        assert!(!independent_large_abox_profile(&coupled, true));

        let mut coupled = clean.clone();
        coupled
            .nominal_abox
            .role_assertions
            .push(nominal_role("r", "a", "b"));
        assert!(!independent_large_abox_profile(&coupled, true));

        let mut coupled = clean.clone();
        coupled.nominal_abox.negative_role_assertions.push(nominal_role(
            "r", "a", "b",
        ));
        assert!(!independent_large_abox_profile(&coupled, true));

        let mut coupled = clean.clone();
        coupled.nominal_abox.different.push(("a".into(), "b".into()));
        assert!(!independent_large_abox_profile(&coupled, true));

        for concept in [
            C::Not(Box::new(C::Nominal("a".into()))),
            C::Exists(R::Universal, Box::new(C::Top)),
            C::Forall(R::Universal, Box::new(C::Top)),
            C::AtLeast(1, R::Universal, Box::new(C::Top)),
            C::AtMost(1, R::Universal, Box::new(C::Top)),
            C::HasSelf(R::Universal),
        ] {
            let mut coupled = clean.clone();
            coupled.source_axioms = vec![source_subclass(C::Name("A".into()), concept)];
            assert!(!independent_large_abox_profile(&coupled, true));
        }

        for assertion in [
            C::And([C::Nominal("a".into()), C::Top].into()),
            C::Exists(R::Universal, Box::new(C::Top)),
        ] {
            let mut coupled = clean.clone();
            coupled.nominal_abox.individuals[0]
                .assertions
                .push(assertion);
            assert!(!independent_large_abox_profile(&coupled, true));
        }
    }

    #[test]
    fn independent_abox_representatives_canonicalize_assertion_sets() {
        let tin = cached_native_role_input();
        let (_algo, _ctx, mut bridged) =
            fresh_bridge_env_with_trigger_absorption(&tin, true);
        let first = bridged.nominal_seeds[0].clone();
        let mut reordered = first.clone();
        reordered.individual_tag = 10_001;
        reordered.assertions.reverse();
        reordered.assertions.push(reordered.assertions[0]);
        let mut duplicate = first.clone();
        duplicate.individual_tag = 10_002;
        let mut distinct = first.clone();
        distinct.individual_tag = 10_003;
        distinct.assertions[0].1 = !distinct.assertions[0].1;
        bridged.nominal_seeds = vec![first.clone(), reordered, duplicate, distinct.clone()];

        let selected = independent_abox_representative_tags(&bridged);
        assert_eq!(selected.len(), 2);
        assert!(selected.contains(&first.individual_tag));
        assert!(selected.contains(&distinct.individual_tag));
        assert!(!selected.contains(&10_001));
        assert!(!selected.contains(&10_002));
    }

    fn exact_atomic_datatype_input() -> TInput {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let concepts: Vec<String> = vec![
            "A".into(),
            "Q_guard".into(),
            "__dt__boolean".into(),
            "__dt__val__\"true\"^^xsd:boolean".into(),
            "__dt__val__\"false\"^^xsd:boolean".into(),
            "__dt__integer".into(),
            "__dt__val__\"23\"^^xsd:integer".into(),
            "__dt__val__\"46\"^^xsd:integer".into(),
            "__dt__string".into(),
            "__dt__val__\"McNeal\"^^xsd:string".into(),
            "__dt__val__\"Tisell_Salander\"^^xsd:string".into(),
            "__dt__float".into(),
        ];
        let roles = vec![
            "bool_value".into(),
            "integer_value".into(),
            "view".into(),
            "pressure_mmHg".into(),
            "slot_synonym".into(),
            "object_role".into(),
        ];
        let values = [3usize, 4, 6, 7, 9, 10];
        let mut clauses = Vec::new();
        for &value in &values {
            clauses.push(HtClause {
                body: vec![
                    HAtom::Concept {
                        neg: false,
                        c: value,
                        t: 0,
                    },
                    HAtom::Concept {
                        neg: false,
                        c: value,
                        t: 1,
                    },
                ],
                head: vec![HAtom::Eq { s: 0, t: 1 }],
            });
        }
        for (position, &left) in values.iter().enumerate() {
            for &right in values.iter().skip(position + 1) {
                clauses.push(HtClause {
                    body: vec![
                        HAtom::Concept {
                            neg: false,
                            c: left,
                            t: 0,
                        },
                        HAtom::Concept {
                            neg: false,
                            c: right,
                            t: 0,
                        },
                    ],
                    head: vec![],
                });
            }
        }
        for (value, range) in [(3, 2), (4, 2), (6, 5), (7, 5), (9, 8), (10, 8)] {
            clauses.push(HtClause {
                body: vec![HAtom::Concept {
                    neg: false,
                    c: value,
                    t: 0,
                }],
                head: vec![HAtom::Concept {
                    neg: false,
                    c: range,
                    t: 0,
                }],
            });
        }
        clauses.push(HtClause {
            body: vec![HAtom::Concept {
                neg: false,
                c: 2,
                t: 0,
            }],
            head: vec![
                HAtom::Concept {
                    neg: false,
                    c: 3,
                    t: 0,
                },
                HAtom::Concept {
                    neg: false,
                    c: 4,
                    t: 0,
                },
            ],
        });
        // Both mixed datatype clause shapes seen in 10621. Source mode keeps
        // these exact copies instead of suppressing them with ordinary source
        // clausifier copies.
        clauses.push(HtClause {
            body: vec![HAtom::Concept {
                neg: false,
                c: 0,
                t: 0,
            }],
            head: vec![HAtom::Exist {
                r: 0,
                neg: false,
                c: 3,
                t: 0,
            }],
        });
        clauses.push(HtClause {
            body: vec![
                HAtom::Concept {
                    neg: false,
                    c: 1,
                    t: 0,
                },
                HAtom::Role { r: 0, s: 0, t: 1 },
            ],
            head: vec![HAtom::Concept {
                neg: false,
                c: 2,
                t: 1,
            }],
        });

        let source_axioms = vec![
            source_subclass(
                C::Name("A".into()),
                C::Exists(
                    R::Name("bool_value".into()),
                    Box::new(C::Name(concepts[3].clone())),
                ),
            ),
            source_subclass(
                C::Name("A".into()),
                C::Exists(
                    R::Name("integer_value".into()),
                    Box::new(C::Name(concepts[6].clone())),
                ),
            ),
            source_subclass(
                C::Name("A".into()),
                C::Exists(
                    R::Name("view".into()),
                    Box::new(C::Name(concepts[9].clone())),
                ),
            ),
            source_subclass(
                C::Name("A".into()),
                C::Exists(
                    R::Name("pressure_mmHg".into()),
                    Box::new(C::Name(concepts[11].clone())),
                ),
            ),
            source_subclass(
                C::Top,
                C::Forall(
                    R::Name("bool_value".into()),
                    Box::new(C::Name(concepts[2].clone())),
                ),
            ),
            source_subclass(
                C::Top,
                C::Forall(
                    R::Name("integer_value".into()),
                    Box::new(C::Name(concepts[5].clone())),
                ),
            ),
            // A string range on a different role mirrors 10621's `view`
            // literals plus independent `slot_synonym` range.
            source_subclass(
                C::Top,
                C::Forall(
                    R::Name("slot_synonym".into()),
                    Box::new(C::Name(concepts[8].clone())),
                ),
            ),
            source_subclass(
                C::Top,
                C::Forall(
                    R::Name("pressure_mmHg".into()),
                    Box::new(C::Name(concepts[11].clone())),
                ),
            ),
            source_subclass(
                C::Top,
                C::Forall(R::Name("object_role".into()), Box::new(C::Name("A".into()))),
            ),
        ];

        TInput {
            concepts,
            roles,
            clauses,
            queries: vec![0],
            source_axioms,
            ..Default::default()
        }
    }

    #[test]
    fn source_mode_retains_exact_unit_bottom_certificates() {
        use crate::frontend::syntax::Concept as C;

        // The source side channel activates native source reconstruction but
        // does not prove A empty.  The normalized clause models a consequence
        // appended by the frontend bottom prepass and must not be suppressed
        // as though it were merely a clausifier copy of the source axiom.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("B".into()), C::Name("B".into()))],
            clauses: vec![HtClause {
                body: vec![HAtom::Concept {
                    neg: false,
                    c: 0,
                    t: 0,
                }],
                head: vec![],
            }],
            ..Default::default()
        };

        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert_eq!(bridged.certified_unsatisfiable, vec![0]);

        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("an exact unit-bottom certificate needs no probe");
        assert!(result.consistent);
        assert_eq!(result.unsatisfiable, vec![0]);
    }

    #[test]
    fn source_mode_does_not_promote_conjunctive_bottom_to_unit_bottom() {
        use crate::frontend::syntax::Concept as C;

        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            queries: vec![0, 1],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Name("A".into()))],
            clauses: vec![HtClause {
                body: vec![
                    HAtom::Concept {
                        neg: false,
                        c: 0,
                        t: 0,
                    },
                    HAtom::Concept {
                        neg: false,
                        c: 1,
                        t: 0,
                    },
                ],
                head: vec![],
            }],
            ..Default::default()
        };

        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(bridged.certified_unsatisfiable.is_empty());
    }

    #[test]
    fn non_source_unit_bottom_keeps_the_legacy_encoder_path() {
        let tin = TInput {
            concepts: vec!["A".into()],
            queries: vec![0],
            clauses: vec![HtClause {
                body: vec![HAtom::Concept {
                    neg: false,
                    c: 0,
                    t: 0,
                }],
                head: vec![],
            }],
            ..Default::default()
        };

        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(!bridged.source_tbox);
        assert!(bridged.certified_unsatisfiable.is_empty());
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("the legacy exact clause encoder still decides unit bottom");
        assert_eq!(result.unsatisfiable, vec![0]);
    }

    #[test]
    fn exact_atomic_datatype_fragment_retains_relation_and_mixed_clauses() {
        let tin = exact_atomic_datatype_input();
        assert!(exact_atomic_datatype_bridge_fragment(&tin, true));

        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert_eq!(bridged.unsupported, 0);
        assert_eq!(bridged.singleton_concepts.len(), 6);

        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("the checked 10621 atomic datatype fragment must stay routable");
        assert!(result.consistent);
        assert!(!result.unsatisfiable.contains(&0));
    }

    #[test]
    fn exact_atomic_datatype_fragment_checks_blank_data_node_axioms() {
        use crate::frontend::syntax::Concept as C;

        for bad_axiom in [
            source_subclass(C::Not(Box::new(C::Name("A".into()))), C::Bottom),
            crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::Equivalent,
                left: C::Top,
                right: C::Name("A".into()),
            },
            crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::Disjoint,
                left: C::Top,
                right: C::Top,
            },
        ] {
            let mut tin = exact_atomic_datatype_input();
            tin.source_axioms.push(bad_axiom);
            assert!(
                !exact_atomic_datatype_bridge_fragment(&tin, true),
                "an axiom false on a blank data node must reject the route"
            );
            assert!(
                bridged_classify_opts_with_trigger_absorption(&tin, false, false, true).is_none(),
                "an unsafe blank-data-node axiom reached classification"
            );
        }

        let mut safe = exact_atomic_datatype_input();
        safe.source_axioms.extend([
            source_subclass(C::Not(Box::new(C::Name("A".into()))), C::Top),
            crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::Equivalent,
                left: C::And(
                    [C::Name("A".into()), C::Name("Q_guard".into())]
                        .into_iter()
                        .collect(),
                ),
                right: C::Bottom,
            },
            crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::Disjoint,
                left: C::Or(
                    [C::Name("A".into()), C::Name("Q_guard".into())]
                        .into_iter()
                        .collect(),
                ),
                right: C::Top,
            },
        ]);
        assert!(
            exact_atomic_datatype_bridge_fragment(&safe, true),
            "Boolean axioms true on a blank data node must remain routable"
        );
    }

    #[test]
    fn exact_atomic_datatype_fragment_accepts_complex_object_domains() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let domain_left = C::Exists(R::Name("bool_value".into()), Box::new(C::Top));
        let mut complex_domain = exact_atomic_datatype_input();
        complex_domain.source_axioms.push(source_subclass(
            domain_left.clone(),
            C::Or(
                [C::Name("A".into()), C::Name("Q_guard".into())]
                    .into_iter()
                    .collect(),
            ),
        ));
        assert!(
            exact_atomic_datatype_bridge_fragment(&complex_domain, true),
            "a data-property domain may be an exact object-language expression"
        );

        let mut recursive_domain = exact_atomic_datatype_input();
        recursive_domain
            .source_axioms
            .push(source_subclass(domain_left.clone(), domain_left));
        assert!(
            !exact_atomic_datatype_bridge_fragment(&recursive_domain, true),
            "a domain RHS that recursively uses a data role stays outside the fragment"
        );
    }

    #[test]
    fn exact_atomic_datatype_fragment_accepts_only_safe_data_cardinalities() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let safe_bound = C::AtMost(
            1,
            R::Name("integer_value".into()),
            Box::new(C::Top),
        );
        let mut safe = exact_atomic_datatype_input();
        safe.source_axioms.push(source_equivalence(
            C::Name("A".into()),
            C::And(
                [
                    C::Name("Q_guard".into()),
                    C::AtLeast(
                        2,
                        R::Name("integer_value".into()),
                        Box::new(C::Top),
                    ),
                    safe_bound,
                ]
                .into_iter()
                .collect(),
            ),
        ));
        assert!(
            exact_atomic_datatype_bridge_fragment(&safe, true),
            "small data bounds are exact under objectification"
        );

        for unsafe_bound in [
            C::AtLeast(
                3,
                R::Name("integer_value".into()),
                Box::new(C::Top),
            ),
            C::AtMost(
                3,
                R::Name("integer_value".into()),
                Box::new(C::Top),
            ),
            C::AtMost(
                1,
                R::Name("integer_value".into()),
                Box::new(C::Name("A".into())),
            ),
        ] {
            let mut unsafe_tin = exact_atomic_datatype_input();
            unsafe_tin.source_axioms.push(source_subclass(
                C::Name("A".into()),
                unsafe_bound,
            ));
            assert!(
                !exact_atomic_datatype_bridge_fragment(&unsafe_tin, true),
                "uncertified data-property cardinality must remain fail-closed"
            );
        }

        let mut nested = exact_atomic_datatype_input();
        nested.source_axioms.push(source_subclass(
            C::Name("A".into()),
            C::Forall(
                R::Name("object_role".into()),
                Box::new(C::And(
                    [
                        C::AtLeast(
                            1,
                            R::Name("integer_value".into()),
                            Box::new(C::Top),
                        ),
                        C::AtMost(
                            1,
                            R::Name("integer_value".into()),
                            Box::new(C::Top),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                )),
            ),
        ));
        assert!(
            exact_atomic_datatype_bridge_fragment(&nested, true),
            "safe data bounds remain exact inside an ordinary-role filler"
        );
    }

    #[test]
    fn exact_atomic_datatype_fragment_recognises_boolean_two_value_range() {
        let mut tin = exact_atomic_datatype_input();
        tin.concepts[2] =
            "__dt__c__DataOneOf(\"false\"^^xsd:boolean \"true\"^^xsd:boolean)".into();
        assert!(
            exact_atomic_datatype_bridge_fragment(&tin, true),
            "the complete Boolean enumeration is extensionally xsd:boolean"
        );
    }

    #[test]
    fn exact_atomic_datatype_fragment_accepts_bare_datetime_range() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let mut tin = exact_atomic_datatype_input();
        tin.concepts.push("__dt__dateTime".into());
        tin.roles.push("timestamp".into());
        tin.source_axioms.extend([
            source_subclass(
                C::Top,
                C::Forall(
                    R::Name("timestamp".into()),
                    Box::new(C::Name("__dt__dateTime".into())),
                ),
            ),
            source_subclass(
                C::Name("A".into()),
                C::And(
                    [
                        C::AtLeast(2, R::Name("timestamp".into()), Box::new(C::Top)),
                        C::AtMost(2, R::Name("timestamp".into()), Box::new(C::Top)),
                    ]
                    .into_iter()
                    .collect(),
                ),
            ),
        ]);
        assert!(
            exact_atomic_datatype_bridge_fragment(&tin, true),
            "bare dateTime is a nonempty exact atomic range with at least two values"
        );

        *tin.concepts.last_mut().expect("dateTime concept") =
            "__dt__dateTimeStamp".into();
        assert!(
            !exact_atomic_datatype_bridge_fragment(&tin, true),
            "dateTimeStamp remains outside the exact atomic map"
        );
    }

    #[test]
    fn exact_atomic_datatype_fragment_requires_relation_evidence() {
        let mut tin = exact_atomic_datatype_input();
        tin.clauses
            .retain(|clause| !datatype_singleton_clause(clause, 3));
        assert!(!exact_atomic_datatype_bridge_fragment(&tin, true));
        assert!(
            bridged_classify_opts_with_trigger_absorption(&tin, false, false, true).is_none(),
            "missing value-singleton evidence must defer the route"
        );

        let mut no_cover = exact_atomic_datatype_input();
        no_cover.clauses.retain(|clause| {
            !matches!(
                (clause.body.as_slice(), clause.head.as_slice()),
                ([HAtom::Concept { c: 2, .. }], [_, _])
            )
        });
        assert!(!exact_atomic_datatype_bridge_fragment(&no_cover, true));

        let mut false_float_inclusion = exact_atomic_datatype_input();
        false_float_inclusion.clauses.push(HtClause {
            body: vec![HAtom::Concept {
                neg: false,
                c: 5,
                t: 0,
            }],
            head: vec![HAtom::Concept {
                neg: false,
                c: 11,
                t: 0,
            }],
        });
        assert!(
            !exact_atomic_datatype_bridge_fragment(&false_float_inclusion, true),
            "the route gate must reject integer-to-float under-typing"
        );
    }

    #[test]
    fn datatype_boolean_min_three_defers_outside_the_atomic_fragment() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let mut tin = exact_atomic_datatype_input();
        tin.source_axioms.push(source_subclass(
            C::Name("A".into()),
            C::AtLeast(
                3,
                R::Name("bool_value".into()),
                Box::new(C::Name("__dt__boolean".into())),
            ),
        ));
        assert!(!exact_atomic_datatype_bridge_fragment(&tin, true));
        assert!(
            bridged_classify_opts_with_trigger_absorption(&tin, false, false, true).is_none(),
            "a boolean cardinality outside the certified syntax must not be reported SAT"
        );
    }

    #[test]
    fn opaque_or_complex_datatype_defers_the_route() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        for datatype in [
            "__dt__opaque",
            "__dt__c__DataUnionOf(xsd:string xsd:boolean)",
        ] {
            let tin = TInput {
                concepts: vec!["A".into(), datatype.into()],
                roles: vec!["p".into()],
                queries: vec![0],
                source_axioms: vec![source_subclass(
                    C::Name("A".into()),
                    C::Exists(R::Name("p".into()), Box::new(C::Name(datatype.into()))),
                )],
                ..Default::default()
            };
            assert!(!exact_atomic_datatype_bridge_fragment(&tin, true));
            assert!(
                bridged_classify_opts_with_trigger_absorption(&tin, false, false, true).is_none(),
                "unsupported datatype reached classification: {datatype}"
            );
        }
    }

    #[test]
    fn empty_role_nominal_model_is_an_exact_positive_certificate() {
        let tin = empty_role_model_input();
        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(bridged.has_native_nominals());
        assert!(empty_role_nominal_model_certificate(&tin, &bridged));
    }

    #[test]
    fn empty_role_nominal_model_checks_every_source_axiom_kind() {
        use crate::frontend::syntax::Concept as C;

        let base = empty_role_model_input();
        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&base, true);
        for bad_axiom in [
            source_subclass(C::Top, C::Name("A".into())),
            crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::Equivalent,
                left: C::Top,
                right: C::Name("A".into()),
            },
            crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::Disjoint,
                left: C::Top,
                right: C::Top,
            },
        ] {
            let mut tin = base.clone();
            tin.source_axioms.push(bad_axiom);
            assert!(!empty_role_nominal_model_certificate(&tin, &bridged));
        }
    }

    #[test]
    fn empty_role_nominal_model_checks_assertions_and_inequalities() {
        use crate::frontend::syntax::Concept as C;

        let base = empty_role_model_input();
        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&base, true);

        let mut bad_assertion = base.clone();
        bad_assertion.nominal_abox.individuals[0].assertions = vec![C::Name("A".into())];
        assert!(!empty_role_nominal_model_certificate(
            &bad_assertion,
            &bridged
        ));

        let mut self_different = base;
        self_different
            .nominal_abox
            .different
            .push(("a".into(), "a".into()));
        assert!(!empty_role_nominal_model_certificate(
            &self_different,
            &bridged
        ));
    }

    #[test]
    fn empty_role_nominal_model_rejects_edge_forcing_and_top_roles() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let base = empty_role_model_input();
        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&base, true);

        let mut edge_forcing = base.clone();
        edge_forcing.clauses.push(HtClause {
            body: vec![],
            head: vec![HAtom::Role { r: 0, s: 0, t: 0 }],
        });
        assert!(!empty_role_nominal_model_certificate(
            &edge_forcing,
            &bridged
        ));

        for spelling in [
            "owl:topObjectProperty",
            "topObjectProperty",
            "topObjectProperty__owl",
            "http://www.w3.org/2002/07/owl#topObjectProperty",
            "<http://www.w3.org/2002/07/owl#topObjectProperty>",
            "owl:topDataProperty",
            "topDataProperty__owl",
            "__U__",
        ] {
            let mut top_role = base.clone();
            top_role.roles[0] = spelling.into();
            top_role.chains.push((0, 1, 1));
            // Both a guarded RBox occurrence and the source-level
            // `Top -> forall(topRole, Bottom)` counterexample must decline.
            top_role.source_axioms.push(source_subclass(
                C::Top,
                C::Forall(R::Name(spelling.into()), Box::new(C::Bottom)),
            ));
            assert!(
                !empty_role_nominal_model_certificate(&top_role, &bridged),
                "universal role spelling was certified: {spelling}"
            );
            assert!(
                bridged_classify_opts_with_trigger_absorption(&top_role, false, false, true)
                    .is_none(),
                "universal role spelling reached bridge classification: {spelling}"
            );
        }
    }

    #[test]
    fn empty_role_nominal_model_rejects_fixed_datatype_roots() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let base = empty_role_model_input();
        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&base, true);
        let mut datatype_definition = base;
        datatype_definition
            .source_axioms
            .push(crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::Equivalent,
                left: C::Name("__dt__custom".into()),
                right: C::Name("__dt__xsd_string".into()),
            });
        datatype_definition.source_axioms.push(source_subclass(
            C::Name("A".into()),
            C::AtLeast(
                2,
                R::Name("p".into()),
                Box::new(C::Name("__dt__custom".into())),
            ),
        ));
        assert!(!empty_role_nominal_model_certificate(
            &datatype_definition,
            &bridged
        ));
        assert!(
            bridged_classify_opts_with_trigger_absorption(
                &datatype_definition,
                false,
                false,
                true,
            )
            .is_none(),
            "a fixed datatype root must defer the whole bridge route"
        );
    }

    #[test]
    fn native_nominals_merge_without_una_and_clash_with_explicit_different() {
        use crate::frontend::syntax::Concept as C;

        let mut tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            queries: vec![0],
            source_axioms: vec![
                source_subclass(C::Name("A".into()), C::Nominal("a".into())),
                source_subclass(C::Name("A".into()), C::Nominal("b".into())),
            ],
            nominal_abox: native_nominal_meta(
                vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
                vec![],
            ),
            ..Default::default()
        };
        let open_world = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("native singleton equality must be decided");
        assert!(open_world.consistent);
        assert!(!open_world.unsatisfiable.contains(&0), "OWL has no UNA");

        tin.nominal_abox.different.push(("a".into(), "b".into()));
        let explicit_different =
            bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
                .expect("explicit inequality must be decided");
        assert!(explicit_different.consistent, "A may remain empty");
        assert!(explicit_different.unsatisfiable.contains(&0));
    }

    /// Native-nominal input with one existential over a named class, so
    /// `build_saturation_seeds` has a concept wave to install linkings for.
    fn native_saturation_coupling_input() -> TInput {
        use crate::frontend::syntax::Concept as C;
        use crate::frontend::syntax::Role as R;

        TInput {
            concepts: vec!["A".into(), "B".into(), "__nom__a".into()],
            roles: vec!["r".into()],
            queries: vec![0, 1],
            source_axioms: vec![
                source_subclass(
                    C::Name("A".into()),
                    C::Exists(R::Name("r".into()), Box::new(C::Name("B".into()))),
                ),
                source_subclass(C::Name("A".into()), C::Nominal("a".into())),
            ],
            nominal_abox: native_nominal_meta(vec![("a", "__nom__a", vec![])], vec![]),
            ..Default::default()
        }
    }

    /// The first (concept, saturation node) pair the coupling would resolve,
    /// walked exactly as `native_saturation_coupling_metadata_covered` walks it.
    fn first_resolved_saturation_node(
        ctx: &CalculationAlgorithmContextBase,
    ) -> super::super::process::SatNodeId {
        use super::super::model::concept_process::ConceptProcessDataId;

        for index in 0..ctx.ontology_arenas().concept_count() {
            let concept_data = ctx
                .ontology_arenas()
                .concept(ConceptId::new(index))
                .get_concept_data();
            if concept_data == INVALID {
                continue;
            }
            let ref_linking = ctx
                .ontology_arenas()
                .concept_process_data(ConceptProcessDataId::new(concept_data))
                .get_concept_reference_linking();
            if ref_linking.is_none() {
                continue;
            }
            let linking_data = ctx
                .ontology_arenas()
                .concept_saturation_reference_linking_data(ref_linking);
            for item in [
                linking_data.get_concept_saturation_reference_linking_data(false),
                linking_data.get_concept_saturation_reference_linking_data(true),
                linking_data.get_existential_successor_concept_saturation_reference_linking_data(),
            ] {
                if item.is_none() {
                    continue;
                }
                let node = ctx
                    .ontology_arenas()
                    .saturation_concept_reference_linking(item)
                    .get_individual_process_node_for_concept();
                if node.is_some() {
                    return node;
                }
            }
        }
        super::super::process::SatNodeId::NONE
    }

    /// The coupling may only be armed once the concept wave has actually
    /// installed resolvable linkings. Before `build_saturation_seeds` there is
    /// no saturation arena at all, so the gate must refuse.
    #[test]
    fn native_saturation_coupling_gate_refuses_without_a_saturation_wave() {
        let tin = native_saturation_coupling_input();
        let (_algo, ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(bridged.has_native_nominals());
        assert_eq!(ctx.process_context().sat_node_count(), 0);
        assert!(!native_saturation_coupling_metadata_covered(&ctx, &bridged));
    }

    /// After the concept wave the gate opens, and every linking it can follow
    /// resolves to a concept-test node — never to an ABox representation node.
    /// This is the separation the coupling's soundness argument rests on:
    /// `build_native_abox_saturation_seeds` installs no concept linkings.
    #[test]
    fn native_saturation_coupling_gate_opens_on_the_concept_wave_only() {
        let tin = native_saturation_coupling_input();
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        build_saturation_seeds(&mut ctx, &bridged);
        let abox_nodes = build_native_abox_saturation_seeds(
            &mut super::super::saturation::algorithm::SaturationTaskHandleAlgorithm::new(),
            &mut ctx,
            &bridged,
            None,
        )
        .expect("native ABox seeds must build");
        assert!(!abox_nodes.is_empty());
        assert!(native_saturation_coupling_metadata_covered(&ctx, &bridged));
        for &(_, node) in &abox_nodes {
            assert!(
                ctx.process_context()
                    .sat_node(node)
                    .is_abox_individual_representation_node(),
                "the ABox wave must mark its nodes as representation nodes"
            );
        }

        // And the configuration it enables keeps both nominal fail-closed legs.
        configure_native_nominal_completion_saturation_coupling(&mut algo);
        assert!(algo.conf_expand_created_successors_from_saturation);
        assert!(algo.conf_caching_blocking_from_saturation);
        assert!(
            !algo.conf_saturation_caching_with_nominals,
            "saturation caching with nominals needs the exact per-nominal dependency \
             record the bridge does not keep"
        );
        assert!(algo.conf_saturation_coupling_declines_nominal_connected);
        assert!(
            algo.conf_saturation_caching_testing_during_blocking_tests,
            "cpp ctor line 236 — Konclude re-tests the saturation caching of every \
             localized ancestor it walks in a blocking test (cpp 19101), which is \
             what keeps the block and the skipBlockerSearch short-circuit in sync"
        );
    }

    /// The saturation-blocking RETEST is only reachable with an installed
    /// saturation-node expansion cache HANDLER (`detect_individual_node_saturation_cached`,
    /// cpp 4769). Konclude constructs that handler for every completion task;
    /// the bridge must install it on the native-nominal route too, with the
    /// cache left EMPTY and both writing flags off, so the retest gets only its
    /// cache-independent re-confirmation and no cross-probe expansion replay.
    #[test]
    fn native_saturation_coupling_installs_an_empty_expansion_cache_handler() {
        let tin = native_saturation_coupling_input();
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        build_saturation_seeds(&mut ctx, &bridged);
        assert!(native_saturation_coupling_metadata_covered(&ctx, &bridged));
        assert!(
            !ctx.sat_node_exp_cache_handler.is_some(),
            "no handler before the install"
        );

        install_bridge_saturation_node_expansion_cache(&mut ctx);
        configure_native_nominal_completion_saturation_coupling(&mut algo);

        assert!(
            ctx.sat_node_exp_cache_handler.is_some(),
            "the retest gate in u21 reads exactly this handle"
        );
        assert!(
            algo.conf_saturation_expansion_cache_reading,
            "cpp ctor line 237 — without it the retest never consults the handler"
        );
        assert!(
            !algo.conf_saturation_satisfiabilitiy_expansion_cache_writing,
            "no completion probe may extend the cache on this route (u31.rs:155)"
        );
        assert!(
            !algo.conf_saturation_concept_unsatisfiability_saturated_cache_writing,
            "and no unsat write either, so no saturation node ever gains a cache entry"
        );
        // With nothing written, every saturation node stays entry-free, so the
        // cache ARM of `is_node_satisfiable_cached` and
        // `cached_deterministic_expansion_concepts` remain inert.
        for index in 0..ctx.process_context().sat_node_count() {
            assert!(
                ctx.process_context()
                    .sat_node(super::super::process::SatNodeId::new(index as Cint64))
                    .get_cache_expansion_data()
                    .is_none(),
                "installing the handler must not populate the cache"
            );
        }
    }

    /// If the two waves ever collided in the saturation-node id space — a
    /// concept linking resolving to an ABox representation node — the gate must
    /// fail closed rather than let an ABox-influenced label be replayed onto an
    /// unrelated successor.
    #[test]
    fn native_saturation_coupling_gate_refuses_an_abox_representation_node() {
        let tin = native_saturation_coupling_input();
        let (_algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        build_saturation_seeds(&mut ctx, &bridged);
        assert!(native_saturation_coupling_metadata_covered(&ctx, &bridged));

        let node = first_resolved_saturation_node(&ctx);
        assert!(node.is_some(), "the concept wave must install a linking");
        ctx.process_context_mut()
            .sat_node_mut(node)
            .set_abox_individual_representation_node(true);
        assert!(!native_saturation_coupling_metadata_covered(&ctx, &bridged));
    }

    #[test]
    fn native_different_individuals_are_negative_nominal_assertions() {
        let tin = TInput {
            concepts: vec!["__nom__a".into(), "__nom__b".into()],
            source_axioms: vec![source_subclass(
                crate::frontend::syntax::Concept::Top,
                crate::frontend::syntax::Concept::Top,
            )],
            nominal_abox: native_nominal_meta(
                vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
                vec![("a", "b")],
            ),
            ..Default::default()
        };
        let (_algo, ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        let a = &bridged.nominal_seeds[0];
        let b = &bridged.nominal_seeds[1];
        assert!(a.assertions.contains(&(b.nominal_concept, true)));
        assert!(b.assertions.contains(&(a.nominal_concept, true)));
        assert!(ctx
            .ontology_arenas()
            .individual(a.individual)
            .get_assertion_concept_linker()
            .contains(&ConceptAssertion {
                target: b.nominal_concept,
                negated: true,
            }));
        assert!(ctx
            .ontology_arenas()
            .individual(b.individual)
            .get_assertion_concept_linker()
            .contains(&ConceptAssertion {
                target: a.nominal_concept,
                negated: true,
            }));
    }

    #[test]
    fn native_representative_scheduler_selects_seven_incomplete_entries() {
        use crate::frontend::syntax::Concept as C;
        use crate::json_io::{NominalAboxMeta, NominalIndividualMeta};
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let mut concepts = vec!["A".to_owned()];
        concepts.extend((0..12).map(|index| format!("__nom__i{index}")));
        let individuals = (0..12)
            .map(|index| NominalIndividualMeta {
                individual: format!("i{index}"),
                proxies: vec![format!("__nom__i{index}")],
                assertions: Vec::new(),
                assertion_markers: Vec::new(),
            })
            .collect();
        let role_assertions = (0..11)
            .map(|index| nominal_role("r", &format!("i{index}"), &format!("i{}", index + 1)))
            .collect();
        let tin = TInput {
            concepts,
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: NominalAboxMeta {
                complete: true,
                individuals,
                same: Vec::new(),
                different: Vec::new(),
                role_assertions,
                negative_role_assertions: Vec::new(),
                unsupported: Vec::new(),
            },
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert_eq!(bridged.nominal_seeds.len(), 12);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        {
            let mut cache = bridged.native_representative_cache.borrow_mut();
            for entry in cache
                .as_mut()
                .expect("individual-saturation associations")
                .entries
                .values_mut()
            {
                entry.completely_handled = false;
                entry.insufficient = true;
            }
        }
        let selected =
            native_incomplete_abox_seed_batch(&bridged, NATIVE_REPRESENTATIVE_BATCH_SIZE)
                .expect("incomplete individual-saturation associations");
        assert_eq!(selected.len(), NATIVE_REPRESENTATIVE_BATCH_SIZE);
        let mut actual: Vec<_> = selected.iter().copied().collect();
        actual.sort_unstable();
        let mut expected: Vec<_> = bridged
            .nominal_seeds
            .iter()
            .map(|seed| seed.individual_tag)
            .collect();
        expected.sort_unstable();
        expected.truncate(NATIVE_REPRESENTATIVE_BATCH_SIZE);
        assert_eq!(actual, expected);

        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        assert!(initialize_native_nominal_state_for_tags(
            &mut algo,
            &mut ctx,
            &bridged,
            Some(&selected),
        ));
        assert!(bridged
            .nominal_seeds
            .iter()
            .filter(|seed| selected.contains(&seed.individual_tag))
            .all(|seed| {
                ctx.processing_data_box()
                    .individual_process_node_vector()
                    .get_data(-seed.individual_tag)
                    .is_some()
            }));
    }

    #[test]
    fn positive_and_negative_singletons_drive_exact_taxonomy() {
        use crate::frontend::syntax::Concept as C;

        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "__nom__a".into()],
            queries: vec![0, 1],
            source_axioms: vec![
                source_subclass(C::Name("A".into()), C::Nominal("a".into())),
                source_subclass(C::Nominal("a".into()), C::Name("B".into())),
            ],
            nominal_abox: native_nominal_meta(vec![("a", "__nom__a", vec![])], vec![]),
            ..Default::default()
        };
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("positive nominal taxonomy must be decided");
        assert!(result.consistent);
        assert!(result.subsumptions.contains(&(0, 1)), "A ⊆ {{a}} ⊆ B");

        let negative = TInput {
            concepts: vec!["A".into(), "__nom__a".into()],
            queries: vec![0],
            source_axioms: vec![
                source_subclass(C::Name("A".into()), C::Nominal("a".into())),
                source_subclass(
                    C::Name("A".into()),
                    C::Not(Box::new(C::Nominal("a".into()))),
                ),
            ],
            nominal_abox: native_nominal_meta(vec![("a", "__nom__a", vec![])], vec![]),
            ..Default::default()
        };
        let result = bridged_classify_opts_with_trigger_absorption(&negative, false, false, true)
            .expect("negative nominal clash must be decided");
        assert!(result.consistent);
        assert!(result.unsatisfiable.contains(&0));
    }

    #[test]
    fn native_abox_consistency_is_global_and_incomplete_metadata_defers() {
        use crate::frontend::syntax::Concept as C;

        let mut tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Bottom)],
            nominal_abox: native_nominal_meta(
                vec![("a", "__nom__a", vec![C::Name("A".into())])],
                vec![],
            ),
            ..Default::default()
        };
        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(
            !empty_role_nominal_model_certificate(&tin, &bridged),
            "a false finite-model candidate must fall through to completion"
        );
        let inconsistent = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("exact ABox clash must be decided");
        assert!(!inconsistent.consistent);
        assert!(inconsistent.unsatisfiable.is_empty());
        assert!(inconsistent.subsumptions.is_empty());

        tin.nominal_abox.complete = false;
        tin.nominal_abox.unsupported.push("test gap".into());
        assert!(
            bridged_classify_opts_with_trigger_absorption(&tin, false, false, true).is_none(),
            "an incomplete source certificate must DEFER"
        );
    }

    #[test]
    fn unsupported_abox_metadata_without_proxy_entries_defers() {
        let tin = TInput {
            concepts: vec!["A".into()],
            queries: vec![0],
            nominal_abox: crate::json_io::NominalAboxMeta {
                unsupported: vec!["source ABox has no nominal proxy mapping".into()],
                ..Default::default()
            },
            ..Default::default()
        };

        assert!(
            bridged_classify_opts_with_trigger_absorption(&tin, false, false, true).is_none(),
            "nonempty incomplete ABox metadata must never be mistaken for no ABox"
        );
    }

    #[test]
    fn native_nominal_inverse_fence_is_complete_or_defer() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "__nom__a".into()],
            roles: vec!["r".into()],
            queries: vec![0, 1],
            source_axioms: vec![
                source_subclass(C::Name("A".into()), C::Name("B".into())),
                source_subclass(
                    C::Name("A".into()),
                    C::Exists(R::Inverse("r".into()), Box::new(C::Nominal("a".into()))),
                ),
            ],
            inverse: true,
            fenced: vec![crate::orchestrate::cb_to_ht::Fenced {
                reason: "nominal+inverse(SHOI/SHOIQ)".into(),
                detail: "focused probe".into(),
            }],
            nominal_abox: native_nominal_meta(vec![("a", "__nom__a", vec![])], vec![]),
            ..Default::default()
        };
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect(
                "covered native nominal+inverse input must not be rejected by its legacy fence",
            );
        assert!(result.consistent);
        assert!(result.subsumptions.contains(&(0, 1)));
    }

    #[test]
    fn production_verifies_disjunctive_domain_subsumption_with_pair_probe() {
        use crate::frontend::syntax::{Concept as C, Role as R};
        use crate::json_io::{SourceAxiomKind, SourceAxiomMeta};

        // Every S has an r-successor.  The domain of r is C ⊔ B, while S
        // and C are disjoint, hence S ⊑ B.  This is the small logical shape
        // behind the ORE 10621 Flagellum ⊑ Organ_part residue: an
        // approximate pseudo-model may omit B, but only the complete S ⊓ ¬B
        // probe may decide the negative candidate.
        let tin = TInput {
            concepts: vec!["S".into(), "B".into(), "C".into(), "T".into()],
            roles: vec!["r".into()],
            queries: vec![0, 1, 2, 3],
            source_axioms: vec![
                source_subclass(
                    C::Name("S".into()),
                    C::Exists(R::Name("r".into()), Box::new(C::Name("T".into()))),
                ),
                source_subclass(
                    C::Exists(R::Name("r".into()), Box::new(C::Top)),
                    C::Or(
                        [C::Name("C".into()), C::Name("B".into())]
                            .into_iter()
                            .collect(),
                    ),
                ),
                SourceAxiomMeta {
                    kind: SourceAxiomKind::Disjoint,
                    left: C::Name("S".into()),
                    right: C::Name("C".into()),
                },
            ],
            ..Default::default()
        };

        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("disjunctive-domain input must classify");
        assert!(
            result.subsumptions.contains(&(0, 1)),
            "the complete pair probe must prove S ⊑ B"
        );
    }

    #[test]
    fn native_abox_role_metadata_is_fail_closed() {
        use crate::frontend::syntax::Concept as C;
        use crate::json_io::NominalRoleAssertionMeta;

        let mut tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            nominal_abox: native_nominal_meta(
                vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
                vec![],
            ),
            ..Default::default()
        };
        tin.nominal_abox
            .role_assertions
            .push(NominalRoleAssertionMeta {
                role: "r".into(),
                source: "a".into(),
                target: "b".into(),
            });
        assert!(native_nominal_metadata_covered(&tin, true));
        assert!(
            !native_nominal_metadata_covered(&tin, false),
            "typed role facts require the exact source-concept mode"
        );
        assert!(
            bridged_classify_opts_with_trigger_absorption(&tin, false, false, false).is_none(),
            "non-source mode must retain the historical role-array defer"
        );

        for (role, source, target) in [
            ("missing", "a", "b"),
            ("r", "missing", "b"),
            ("r", "a", "missing"),
            ("", "a", "b"),
        ] {
            let mut invalid = tin.clone();
            invalid.nominal_abox.role_assertions[0] = NominalRoleAssertionMeta {
                role: role.into(),
                source: source.into(),
                target: target.into(),
            };
            assert!(
                !native_nominal_metadata_covered(&invalid, true),
                "invalid role assertion metadata was accepted: {role}({source},{target})"
            );
            assert!(
                bridged_classify_opts_with_trigger_absorption(&invalid, false, false, true)
                    .is_none(),
                "invalid role assertion metadata reached bridge search"
            );
        }

        let mut duplicate_role = tin.clone();
        duplicate_role.roles.push("r".into());
        assert!(
            !native_nominal_metadata_covered(&duplicate_role, true),
            "duplicate role names make name-to-id resolution ambiguous"
        );

        for builtin in [
            "owl:topObjectProperty",
            "http://www.w3.org/2002/07/owl#topObjectProperty",
            "owl:bottomObjectProperty",
            "http://www.w3.org/2002/07/owl#bottomObjectProperty",
        ] {
            let mut invalid = tin.clone();
            invalid.roles = vec![builtin.into()];
            invalid.nominal_abox.role_assertions[0].role = builtin.into();
            assert!(
                !native_nominal_metadata_covered(&invalid, true),
                "builtin role assertion must not become an ordinary role: {builtin}"
            );
            assert!(
                bridged_classify_opts_with_trigger_absorption(&invalid, false, false, true)
                    .is_none(),
                "builtin role assertion reached bridge search: {builtin}"
            );
        }

        let mut incomplete = tin.clone();
        incomplete.nominal_abox.complete = false;
        assert!(!native_nominal_metadata_covered(&incomplete, true));
        assert!(
            bridged_classify_opts_with_trigger_absorption(&incomplete, false, false, true)
                .is_none()
        );

        let mut unsupported = tin.clone();
        unsupported
            .nominal_abox
            .unsupported
            .push("focused unsupported ABox axiom".into());
        assert!(!native_nominal_metadata_covered(&unsupported, true));
        assert!(
            bridged_classify_opts_with_trigger_absorption(&unsupported, false, false, true)
                .is_none()
        );

        let mut unresolved_proxy = tin;
        unresolved_proxy.nominal_abox.individuals[1].proxies[0] = "__nom__missing".into();
        assert!(!native_nominal_metadata_covered(&unresolved_proxy, true));
        assert!(bridged_classify_opts_with_trigger_absorption(
            &unresolved_proxy,
            false,
            false,
            true,
        )
        .is_none());
    }

    #[test]
    fn native_abox_representative_cache_carries_and_replays_full_labels() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let mut meta = native_nominal_meta(
            vec![
                ("a", "__nom__a", vec![C::Name("A".into())]),
                ("b", "__nom__b", vec![]),
                ("c", "__nom__c", vec![]),
            ],
            vec![],
        );
        meta.role_assertions.push(nominal_role("r", "a", "b"));
        meta.role_assertions.push(nominal_role("r", "b", "c"));
        let tin = TInput {
            concepts: vec![
                "A".into(),
                "B".into(),
                "C".into(),
                "__nom__a".into(),
                "__nom__b".into(),
                "__nom__c".into(),
            ],
            roles: vec!["r".into()],
            queries: vec![0, 1],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Name("B".into()))],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: meta,
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));

        let seed = &bridged.nominal_seeds[0];
        let target_tag = bridged.nominal_seeds[1].individual_tag;
        let final_tag = bridged.nominal_seeds[2].individual_tag;
        {
            let mut cache = bridged.native_representative_cache.borrow_mut();
            let cache = cache.as_mut().expect("representative cache written");
            assert!(!cache.association_write_aborted);
            // Value-backed assertion linkers correctly make the raw
            // saturation association insufficient. This focused replay test
            // supplies the post-representative status while retaining the
            // saturation-produced labels and neighbour-role values.
            for entry in cache.entries.values_mut() {
                entry.completely_saturated = true;
                entry.completely_handled = true;
                entry.completely_propagated = true;
                entry.insufficient = false;
            }
            let entry = cache
                .entries
                .get(&seed.individual_tag)
                .expect("source representative association");
            assert!(entry.concepts.contains(&(bridged.named[1], false)));
            assert!(entry.instantiated_roles.contains(&bridged.roles[0]));
            assert!(entry
                .neighbour_role_combinations
                .iter()
                .any(|combination| combination.neighbour_tag == target_tag
                    && combination.roles.contains(&(bridged.roles[0], false))));
            let target_entry = cache
                .entries
                .get(&target_tag)
                .expect("target representative association");
            assert!(target_entry
                .neighbour_role_combinations
                .iter()
                .find(|combination| combination.neighbour_tag == seed.individual_tag)
                .and_then(|combination| combination.role_values.as_ref())
                .is_some_and(|values| values.iter().any(|value| {
                    value.role == bridged.roles[0] && value.inversed && value.deterministic
                })));
            assert!(
                entry.reusable_for_full_completion(),
                "the simple saturation association should be replay-blockable"
            );
        }

        reset_probe_env(&mut algo, &mut ctx, &bridged, true);
        let node = ctx.get_up_to_date_individual_by_id(-seed.individual_tag);
        assert!(node.is_some());
        assert!(ctx
            .process_context()
            .node(node)
            .is_nominal_individual_representative_backend_data_loaded());
        let label = ctx.process_context().node(node).reapply_con_label_set;
        assert!(label.is_some());
        assert!(ctx
            .process_context()
            .label_set(label)
            .contains_concept_in_context(
                ctx.process_context(),
                ctx.ontology_arenas(),
                bridged.named[1],
                false,
            ));
        let blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED;
        let target = ctx.get_up_to_date_individual_by_id(-target_tag);
        let final_target = ctx.get_up_to_date_individual_by_id(-final_tag);
        assert!(target.is_some() && final_target.is_some());
        assert_eq!(
            ctx.process_context()
                .node(node)
                .processing_restriction_flags()
                & blocking_flags,
            blocking_flags,
            "a complete source association was not expansion-blocked"
        );
        assert_eq!(
            ctx.process_context()
                .node(target)
                .processing_restriction_flags()
                & blocking_flags,
            blocking_flags,
            "a complete incoming-role association was not expansion-blocked"
        );
        assert_eq!(
            ctx.process_context()
                .node(final_target)
                .processing_restriction_flags()
                & blocking_flags,
            blocking_flags,
            "the complete role-chain sink was not expansion-blocked"
        );
        assert!(
            algo.ht_role_successor_links(node, bridged.roles[0], &ctx)
                .is_empty(),
            "an expansion-blocked association eagerly rebuilt its cached edge"
        );

        // A concept missing from the cached source label schedules Konclude's
        // backend retest. `detectIndividualNodeBackendCacheSynchronized`
        // clears full/successor synchronization, but an atomic concept cannot
        // influence a role neighbour: the independent neighbour block and raw
        // assertion vectors remain valid and no edge is eagerly replayed.
        let base = ctx.get_or_create_base_dependency_track_point();
        let mut modified_source = node;
        algo.add_concept_to_individual(
            bridged.named[2],
            false,
            &mut modified_source,
            base,
            false,
            true,
            &mut ctx,
        );
        assert!(algo.process_native_nominal_backend_retest(node, &mut ctx));
        let successor_blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED;
        assert_eq!(
            ctx.process_context()
                .node(node)
                .processing_restriction_flags()
                & successor_blocking_flags,
            0,
        );
        assert!(!ctx
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            ));
        assert!(ctx
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
            ));
        assert_eq!(
            ctx.process_context()
                .node(target)
                .processing_restriction_flags()
                & blocking_flags,
            blocking_flags,
            "an exact cached incoming edge invalidated its neighbour"
        );
        assert!(
            algo.ht_role_successor_links(node, bridged.roles[0], &ctx)
                .is_empty(),
            "an uninfluenced cached edge was eagerly materialized"
        );

        // The same concept-only transition on the target preserves its cached
        // incoming/outgoing neighbour labels and leaves both raw vectors for a
        // later selective or fallback expansion.
        let mut modified_target = target;
        algo.add_concept_to_individual(
            bridged.named[2],
            false,
            &mut modified_target,
            base,
            false,
            true,
            &mut ctx,
        );
        assert!(algo.process_native_nominal_backend_retest(target, &mut ctx));
        assert_eq!(
            ctx.process_context()
                .node(target)
                .processing_restriction_flags()
                & successor_blocking_flags,
            0,
        );
        assert!(ctx
            .process_context()
            .node(target)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
            ));
        assert!(
            algo.ht_role_successor_links(target, bridged.roles[0], &ctx)
                .is_empty(),
            "an uninfluenced role-chain tail was eagerly materialized"
        );
    }

    #[test]
    fn conditional_full_class_probe_restores_all_root_consistency_base() {
        use crate::frontend::syntax::Concept as C;

        let mut mixed = cached_native_role_input();
        mixed.concepts.extend(["B".into(), "C".into()]);
        mixed.source_axioms.push(source_subclass(
            C::Top,
            C::Or([C::Name("B".into()), C::Name("C".into())].into()),
        ));
        let (mut algo, mut ctx, bridged) =
            fresh_bridge_env_with_trigger_absorption(&mixed, true);
        assert!(native_cardinality_abox_profile(
            &mixed,
            bridged.has_native_nominals()
        ));
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, true);
        ctx.processing_data_box_mut()
            .set_first_possible_individual_node_id(1_000);
        configure_production_search(&mut algo);
        assert_eq!(native_nominal_consistency(&mut algo, &mut ctx, &bridged), Some(true));

        let base_next_id = ctx
            .processing_data_box_mut()
            .next_individual_node_id(false);
        assert!(base_next_id > 0);
        let owned_epoch_count = algo
            .or_branch_stack
            .iter()
            .filter(|branch| branch.own_epoch)
            .count();
        assert!(
            owned_epoch_count > 0,
            "the regression fixture must exercise deterministic first-fork rollback"
        );
        let deterministic_branch_node = algo
            .or_branch_stack
            .first()
            .expect("forced disjunction branch")
            .parent_used_branch_node;
        assert_eq!(
            owned_epoch_count,
            ctx.process_context().branch_epoch_depth(),
            "every nondeterministic branch epoch must be represented by the retained branch stack"
        );
        while let Some(branch) = algo.or_branch_stack.pop() {
            if branch.own_epoch {
                ctx.pop_branch_epoch();
            }
        }
        assert_eq!(ctx.process_context().branch_epoch_depth(), 0);
        assert!(algo.or_branch_stack.is_empty());
        ctx.base.used_branch_tree_node = deterministic_branch_node;
        ctx.branch_tree_node = deterministic_branch_node;
        assert_eq!(ctx.base.used_branch_tree_node, deterministic_branch_node);
        assert_eq!(ctx.branch_tree_node, deterministic_branch_node);
        let base_node_count = ctx.process_context().node_count();
        let fixed_nodes: Vec<_> = bridged
            .nominal_seeds
            .iter()
            .map(|seed| {
                native_exact_nominal_process_node(&ctx, seed.individual_tag)
                    .expect("full consistency must retain every fixed root")
            })
            .collect();
        let branch_only = [
            bridged.named[mixed.concepts.len() - 2],
            bridged.named[mixed.concepts.len() - 1],
        ];
        for &node in &fixed_nodes {
            let label = ctx.process_context().node(node).reapply_con_label_set;
            assert!(label.is_some());
            for &concept in &branch_only {
                assert!(
                    !ctx
                        .process_context()
                        .label_set(label)
                        .contains_concept_in_context(
                            ctx.process_context(),
                            ctx.ontology_arenas(),
                            concept,
                            false,
                        ),
                    "the deterministic consistency base retained a branch-only disjunct"
                );
            }
        }
        let base_source_flags = ctx
            .process_context()
            .node(fixed_nodes[0])
            .processing_restriction_flags();
        let base_databox = ctx.processing_data_box().clone();
        ctx.push_branch_epoch();
        initialize_retained_classification_databox(&mut ctx, &base_databox, base_next_id);
        reset_classification_algorithm_on_retained_base(&mut algo, &bridged);

        let mut next_id = base_next_id;
        let (_, _, first_root) = bridged_classify_subject_with_root(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut next_id,
            0,
            mixed.concepts.len(),
        )
        .expect("first class probe");
        assert_eq!(ctx.process_context().node(first_root).individual_node_id(), base_next_id);
        assert!(fixed_nodes.iter().all(|node| node.is_some()));

        // The production reset: the whole previous class job is rolled back,
        // however many alternative epochs it left open.
        restore_retained_classification_base(
            &mut algo,
            &mut ctx,
            &bridged,
            &base_databox,
            deterministic_branch_node,
            base_next_id,
        )
        .expect("retained base must be restorable after the first class job");
        assert_eq!(
            ctx.process_context().branch_epoch_depth(),
            1,
            "exactly one class-job epoch stands on the retained base"
        );
        assert_eq!(ctx.process_context().node_count(), base_node_count);
        for seed in &bridged.nominal_seeds {
            assert!(native_exact_nominal_process_node(&ctx, seed.individual_tag).is_some());
        }

        let mut next_id = base_next_id;
        let (_, _, second_root) = bridged_classify_subject_with_root(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut next_id,
            0,
            mixed.concepts.len(),
        )
        .expect("second class probe");
        assert_eq!(
            ctx.process_context().node(second_root).individual_node_id(),
            base_next_id,
            "each isolated class job must reserve the same first positive id"
        );
        restore_retained_classification_base(
            &mut algo,
            &mut ctx,
            &bridged,
            &base_databox,
            deterministic_branch_node,
            base_next_id,
        )
        .expect("retained base must be restorable after the second class job");
        ctx.pop_branch_epoch();
        assert_eq!(ctx.process_context().node_count(), base_node_count);

        // The retained roots still consume the current final association.
        let source = &bridged.nominal_seeds[0];
        let current_update_id = bridged
            .native_representative_cache
            .borrow()
            .as_ref()
            .and_then(|cache| cache.entries.get(&source.individual_tag))
            .map(|entry| entry.association_update_id)
            .expect("completed source association");
        let source_node =
            algo.get_up_to_date_individual_by_id(-source.individual_tag, &mut ctx);
        assert!(source_node.is_some());
        assert_eq!(
            algo.native_nominal_backend_replay[&source.individual_tag].association_update_id,
            Some(current_update_id)
        );
        assert_eq!(
            ctx.process_context()
                .node(source_node)
                .processing_restriction_flags(),
            base_source_flags,
            "two isolated probes must restore the deterministic base flags exactly"
        );
        assert!(bridged.nominal_seeds[1..]
            .iter()
            .all(|seed| native_exact_nominal_process_node(&ctx, seed.individual_tag).is_some()));

        // A route backed by an actual consistency completion task keeps the
        // existing all-root reconstruction.
        let legacy_meta = native_nominal_meta(
            vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
            vec![],
        );
        let legacy = basic_native_role_input(&["r"], legacy_meta);
        let (mut legacy_algo, mut legacy_ctx, legacy_bridged) =
            fresh_bridge_env_with_trigger_absorption(&legacy, true);
        assert!(!native_cardinality_abox_profile(
            &legacy,
            legacy_bridged.has_native_nominals()
        ));
        reset_classification_probe_env(
            &mut legacy_algo,
            &mut legacy_ctx,
            &legacy_bridged,
            false,
            false,
        );
        assert!(legacy_bridged.nominal_seeds.iter().all(|seed| {
            native_exact_nominal_process_node(&legacy_ctx, seed.individual_tag).is_some()
        }));
    }

    /// A class job that ends SATISFIABLE returns with its OR stack still open,
    /// so under COW it leaves one branch epoch per surviving alternative behind.
    /// The retained-base reset must roll back ALL of them: popping a single
    /// epoch (the pre-fix `renew`) leaves the next job on the previous job's
    /// committed disjuncts and grows the journal stack once per probe, which is
    /// what defeated cheap ABox reuse on the 9540 conditional-full profile.
    #[test]
    fn retained_base_reset_rolls_back_every_leftover_alternative_epoch() {
        use crate::frontend::syntax::Concept as C;

        let mut mixed = cached_native_role_input();
        mixed.concepts.extend(["B".into(), "C".into()]);
        mixed.source_axioms.push(source_subclass(
            C::Top,
            C::Or([C::Name("B".into()), C::Name("C".into())].into()),
        ));
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&mixed, true);
        assert!(native_cardinality_abox_profile(
            &mixed,
            bridged.has_native_nominals()
        ));
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, true);
        ctx.processing_data_box_mut()
            .set_first_possible_individual_node_id(1_000);
        configure_production_search(&mut algo);
        assert_eq!(
            native_nominal_consistency(&mut algo, &mut ctx, &bridged),
            Some(true)
        );

        let base_next_id = ctx.processing_data_box_mut().next_individual_node_id(false);
        let deterministic_branch_node = algo
            .or_branch_stack
            .first()
            .expect("forced disjunction branch")
            .parent_used_branch_node;
        while let Some(branch) = algo.or_branch_stack.pop() {
            if branch.own_epoch {
                ctx.pop_branch_epoch();
            }
        }
        assert_eq!(ctx.process_context().branch_epoch_depth(), 0);
        ctx.base.used_branch_tree_node = deterministic_branch_node;
        ctx.branch_tree_node = deterministic_branch_node;
        install_native_nominal_backend_replay(&mut algo, &bridged);
        let base_node_count = ctx.process_context().node_count();
        let base_databox = ctx.processing_data_box().clone();
        let base_root_flags: Vec<_> = bridged
            .nominal_seeds
            .iter()
            .map(|seed| {
                let node = native_exact_nominal_process_node(&ctx, seed.individual_tag)
                    .expect("retained root");
                ctx.process_context()
                    .node(node)
                    .processing_restriction_flags()
            })
            .collect();
        ctx.push_branch_epoch();
        initialize_retained_classification_databox(&mut ctx, &base_databox, base_next_id);
        reset_classification_algorithm_on_retained_base(&mut algo, &bridged);

        // The production 9540 configuration runs the class jobs under COW
        // (KM_TRIGGER_ABSORB), so every open alternative owns an epoch. The
        // unit-test default leaves COW off, which is exactly why the existing
        // retained-base coverage never observed the leak.
        algo.conf_inprocess_cow = true;
        let mut next_id = base_next_id;
        assert!(bridged_classify_subject_with_root(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut next_id,
            0,
            mixed.concepts.len(),
        )
        .is_some());
        let leftover = algo
            .or_branch_stack
            .iter()
            .filter(|branch| branch.own_epoch)
            .count();
        assert!(
            leftover > 0,
            "the fixture must leave at least one open alternative epoch behind"
        );
        assert_eq!(
            ctx.process_context().branch_epoch_depth(),
            leftover + 1,
            "class-job epoch plus one epoch per surviving alternative"
        );

        restore_retained_classification_base(
            &mut algo,
            &mut ctx,
            &bridged,
            &base_databox,
            deterministic_branch_node,
            base_next_id,
        )
        .expect("retained base must be restorable");
        assert_eq!(
            ctx.process_context().branch_epoch_depth(),
            1,
            "the reset must leave exactly the next class job's own epoch"
        );
        assert!(algo.or_branch_stack.is_empty());
        assert_eq!(ctx.base.used_branch_tree_node, deterministic_branch_node);
        assert_eq!(ctx.branch_tree_node, deterministic_branch_node);
        ctx.pop_branch_epoch();
        assert_eq!(
            ctx.process_context().node_count(),
            base_node_count,
            "no node of the finished class job may survive into the next one"
        );
        for (seed, expected) in bridged.nominal_seeds.iter().zip(&base_root_flags) {
            let node = native_exact_nominal_process_node(&ctx, seed.individual_tag)
                .expect("retained root");
            assert_eq!(
                ctx.process_context()
                    .node(node)
                    .processing_restriction_flags(),
                *expected,
                "an ABox root kept the finished class job's backend-synchronisation state"
            );
        }
    }

    #[test]
    fn native_representative_batch_replays_incoming_assertion_vector() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let mut meta = native_nominal_meta(
            vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
            vec![],
        );
        meta.role_assertions.push(nominal_role("r", "a", "b"));
        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: meta,
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let source_seed = bridged.nominal_seeds[0].clone();
        let target_seed = bridged.nominal_seeds[1].clone();
        {
            let mut cache = bridged.native_representative_cache.borrow_mut();
            let target = cache
                .as_mut()
                .expect("representative cache")
                .entries
                .get_mut(&target_seed.individual_tag)
                .expect("target association");
            target.completely_handled = false;
            target.insufficient = true;
        }
        let selected = HashSet::from([target_seed.individual_tag]);
        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        assert!(initialize_native_nominal_state_for_tags(
            &mut algo,
            &mut ctx,
            &bridged,
            Some(&selected),
        ));
        let source = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-source_seed.individual_tag);
        let target = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-target_seed.individual_tag);
        assert!(
            source.is_none() && target.is_some(),
            "successful cached-neighbour blocking materialized the uninfluenced source"
        );
        assert!(
            !ctx.process_context()
                .node(target)
                .reverse_assertion_role_assertions()
                .is_empty(),
            "the selected target lost its incoming assertion vector"
        );
        assert!(
            ctx.process_context()
                .node(target)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                ),
            "the incomplete target association did not retain neighbour blocking"
        );
    }

    #[test]
    fn native_abox_named_assertion_resolve_copy_discharges_satisfied_disjunction() {
        use crate::frontend::syntax::Concept as C;

        // Konclude does not seed a named individual's raw assertions directly
        // into its final saturation node. It first builds an assertion-resolved
        // node from the separated TOP base. The asserted B below resolves the
        // global B-or-C choice for a, while the same choice remains genuinely
        // insufficient for b.
        let tin = TInput {
            concepts: vec![
                "Q".into(),
                "B".into(),
                "C".into(),
                "__nom__a".into(),
                "__nom__b".into(),
            ],
            queries: vec![0, 1, 2],
            source_axioms: vec![source_subclass(
                C::Top,
                C::Or(
                    [C::Name("B".into()), C::Name("C".into())]
                        .into_iter()
                        .collect(),
                ),
            )],
            nominal_abox: native_nominal_meta(
                vec![
                    ("a", "__nom__a", vec![C::Name("B".into())]),
                    ("b", "__nom__b", vec![]),
                ],
                vec![],
            ),
            ..Default::default()
        };
        let (_algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(bridged.nominal_seeds.iter().all(|seed| {
            ctx.ontology_arenas()
                .individual(seed.individual)
                .has_individual_name()
        }));
        assert!(run_bridged_saturation(&mut ctx, &bridged));

        let cache = bridged.native_representative_cache.borrow();
        let cache = cache.as_ref().expect("representative cache written");
        let a = cache
            .entries
            .get(&bridged.nominal_seeds[0].individual_tag)
            .expect("a association");
        let b = cache
            .entries
            .get(&bridged.nominal_seeds[1].individual_tag)
            .expect("b association");
        assert!(
            a.complete_for_precomputation(),
            "the asserted disjunct must discharge the approximate OR"
        );
        assert!(
            !b.complete_for_precomputation(),
            "an unresolved global disjunction must remain insufficient"
        );
    }

    #[test]
    fn native_abox_representative_cache_records_cardinality_and_indirect_nominals() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let meta = native_nominal_meta(
            vec![
                (
                    "a",
                    "__nom__a",
                    vec![
                        C::AtMost(1, R::Name("r".into()), Box::new(C::Top)),
                        C::Exists(R::Name("r".into()), Box::new(C::Nominal("b".into()))),
                    ],
                ),
                ("b", "__nom__b", vec![]),
            ],
            vec![],
        );
        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            nominal_abox: meta,
            ..Default::default()
        };
        let (_algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let cache = bridged.native_representative_cache.borrow();
        let entry = cache
            .as_ref()
            .expect("representative cache written")
            .entries
            .get(&bridged.nominal_seeds[0].individual_tag)
            .expect("source representative association");
        assert!(entry.at_most_cardinalities.contains(&(bridged.roles[0], 1)));
        assert!(entry.existential_roles.contains(&bridged.roles[0]));
        assert!(entry
            .indirect_nominal_connections
            .contains(&bridged.nominal_seeds[1].individual_tag));
        assert_eq!(
            entry.reusable_for_full_completion(),
            entry.completely_handled,
            "indirect nominal metadata must not invent an extra status gate"
        );
    }

    #[test]
    fn native_abox_association_status_matches_konclude_writer_predicate() {
        use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags as F;

        let completed = F::INDSATFLAGCOMPLETED;
        assert_eq!(
            native_abox_association_status(completed, completed),
            (true, true)
        );
        assert_eq!(
            native_abox_association_status(
                completed | F::INDSATFLAGPROPAGATIONINCOMPLETE,
                completed,
            ),
            (true, false),
            "propagation status is recorded separately from handled status"
        );
        assert_eq!(
            native_abox_association_status(
                completed
                    | F::INDSATFLAGINSUFFICIENT
                    | F::INDSATFLAGUNPROCESSED
                    | F::INDSATFLAGUNREGISTEREDPROPAGATION
                    | F::INDSATFLAGUNMARKEDROLEASSERTION,
                completed,
            ),
            (true, true),
            "Konclude's association writer does not fold direct flags into insufficiency"
        );
        assert_eq!(
            native_abox_association_status(completed, completed | F::INDSATFLAGINSUFFICIENT),
            (false, true)
        );
        assert_eq!(native_abox_association_status(0, completed), (false, true));
        assert_eq!(native_abox_association_status(completed, 0), (false, true));
    }

    #[test]
    fn native_precomputation_phase_order_is_strict() {
        let mut phase = NativePrecomputationPhase::Start;
        assert!(advance_native_precomputation_phase(
            &mut phase,
            NativePrecomputationPhase::IndividualSaturation,
        )
        .is_some());
        assert!(advance_native_precomputation_phase(
            &mut phase,
            NativePrecomputationPhase::FullConsistencyCompletion,
        )
        .is_some());
        assert!(advance_native_precomputation_phase(
            &mut phase,
            NativePrecomputationPhase::ConsistencyDeclared,
        )
        .is_some());

        for invalid_next in [
            NativePrecomputationPhase::FullConsistencyCompletion,
            NativePrecomputationPhase::ConsistencyDeclared,
        ] {
            let mut invalid = NativePrecomputationPhase::Start;
            assert!(
                advance_native_precomputation_phase(&mut invalid, invalid_next).is_none(),
                "a precomputation phase was skipped"
            );
            assert_eq!(invalid, NativePrecomputationPhase::Start);
        }
        let mut reordered = NativePrecomputationPhase::IndividualSaturation;
        assert!(advance_native_precomputation_phase(
            &mut reordered,
            NativePrecomputationPhase::ConsistencyDeclared,
        )
        .is_none());
        assert_eq!(reordered, NativePrecomputationPhase::IndividualSaturation);
    }

    #[test]
    fn native_representative_coordination_requires_clean_quiescence() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into()],
            roles: vec!["r".into()],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: native_nominal_meta(vec![("a", "__nom__a", vec![])], vec![]),
            ..Default::default()
        };
        let (_algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        assert!(native_representative_coordination_complete(
            &bridged,
            NativeRepresentativeCoordinationState::default(),
        ));
        for state in [
            NativeRepresentativeCoordinationState {
                running_tasks: 1,
                ..Default::default()
            },
            NativeRepresentativeCoordinationState {
                failed_tasks: 1,
                ..Default::default()
            },
            NativeRepresentativeCoordinationState {
                writeback_failed: true,
                ..Default::default()
            },
            NativeRepresentativeCoordinationState {
                clashed: true,
                ..Default::default()
            },
        ] {
            assert!(!native_representative_coordination_complete(
                &bridged, state
            ));
        }
        {
            let mut cache = bridged.native_representative_cache.borrow_mut();
            cache
                .as_mut()
                .expect("representative cache")
                .entries
                .get_mut(&bridged.nominal_seeds[0].individual_tag)
                .expect("nominal association")
                .completely_handled = false;
        }
        assert!(!native_representative_coordination_complete(
            &bridged,
            NativeRepresentativeCoordinationState::default(),
        ));
    }

    #[test]
    fn native_representative_writeback_rejects_stale_batch_atomically() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into()],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: native_nominal_meta(
                vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
                vec![],
            ),
            ..Default::default()
        };
        let (_algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let selected: HashSet<_> = bridged
            .nominal_seeds
            .iter()
            .map(|seed| seed.individual_tag)
            .collect();
        let mut cache = bridged.native_representative_cache.borrow_mut();
        let cache = cache.as_mut().expect("representative cache");
        let mut prepared = Vec::new();
        for &tag in &selected {
            let current = cache.entries.get(&tag).expect("association").clone();
            assert!(current.complete_for_precomputation());
            let mut replacement = current.clone();
            replacement.used_association_update_id = Some(current.association_update_id);
            replacement.scheduled_individual = Some(true);
            replacement.association_origin = Some(NativeAboxAssociationOrigin::CompletionWriteback);
            prepared.push((tag, replacement));
        }
        let stale_tag = *selected.iter().next().expect("selected tag");
        cache
            .entries
            .get_mut(&stale_tag)
            .expect("stale association")
            .association_update_id += 1;
        let before_ids: HashMap<_, _> = cache
            .entries
            .iter()
            .map(|(&tag, entry)| (tag, entry.association_update_id))
            .collect();
        let before_next = cache.next_association_update_id;
        assert!(
            commit_native_representative_association_batch(cache, prepared, &selected,).is_none()
        );
        assert_eq!(cache.next_association_update_id, before_next);
        assert_eq!(
            cache
                .entries
                .iter()
                .map(|(&tag, entry)| (tag, entry.association_update_id))
                .collect::<HashMap<_, _>>(),
            before_ids,
            "a stale member caused a partial cache publication"
        );
    }

    #[test]
    fn native_abox_representative_reuse_gate_has_every_backend_conjunct() {
        let mut entry = NativeAboxRepresentativeEntry {
            individual_tag: 1,
            concept_values: Some(Vec::new()),
            completely_saturated: true,
            completely_handled: true,
            completely_propagated: true,
            representative_same_individual_merging: Some(false),
            deterministic_same_individual_label_identity: Some(7),
            deterministic_merged_same_considered_label_identity: Some(7),
            deterministic_same_individuals: Some(Vec::new()),
            deterministic_merged_same_considered_individuals: Some(Vec::new()),
            nondeterministic_same_individuals: Some(Vec::new()),
            representative_same_individual_id: Some(1),
            deterministic_same_individual_id: Some(1),
            merge_identity_metadata_complete: true,
            role_metadata_complete: true,
            synchronization_metadata_complete: true,
            ..Default::default()
        };
        assert!(entry.reusable_for_full_completion());
        entry.nondeterministic_same_individuals = Some(vec![2, 3]);
        assert!(
            entry.reusable_for_full_completion(),
            "Konclude's full-block predicate does not reject a non-deterministic same-individual label"
        );
        entry.completely_propagated = false;
        assert!(
            entry.reusable_for_full_completion(),
            "propagation is not part of Konclude's expansion-blocking predicate"
        );
        entry.completely_handled = false;
        assert!(!entry.reusable_for_full_completion());
        entry.completely_handled = true;
        entry.representative_same_individual_merging = Some(true);
        assert!(!entry.reusable_for_full_completion());
        entry.representative_same_individual_merging = None;
        assert!(!entry.reusable_for_full_completion());
        entry.representative_same_individual_merging = Some(false);
        entry.deterministic_merged_same_considered_label_identity = Some(8);
        assert!(!entry.reusable_for_full_completion());
        entry.deterministic_merged_same_considered_label_identity = None;
        assert!(!entry.reusable_for_full_completion());
    }

    /// Stage 8. Konclude's `hasReuseableElements` (cpp 22884-22916) reads four
    /// non-deterministic association slots and, when any is set, queues the node
    /// for `reuseIndividualBackendExpansion` (cpp 25092-25373) — the replay that
    /// puts the consistency model's CHOSEN disjuncts, merges, links and
    /// distinctions back into a later task under ONE non-deterministic
    /// dependency track point. Every slot is INDEPENDENT of the full-block
    /// predicate above, so this pins the four reads separately.
    #[test]
    fn association_reusable_elements_read_the_four_nondeterministic_slots() {
        let base = NativeAboxRepresentativeEntry {
            individual_tag: 1,
            concept_values: Some(vec![NativeAboxConceptValue {
                concept: ConceptId::new(0),
                negated: false,
                deterministic: true,
            }]),
            completely_handled: true,
            ..Default::default()
        };
        assert!(
            !base.has_reusable_elements(),
            "a purely deterministic association has nothing to reuse"
        );
        assert!(!base.has_nondeterministic_neighbour_roles());

        let mut nondeterministic_concept = base.clone();
        nondeterministic_concept
            .concept_values
            .as_mut()
            .expect("concept values")
            .push(NativeAboxConceptValue {
                concept: ConceptId::new(1),
                negated: false,
                deterministic: false,
            });
        assert!(nondeterministic_concept.has_reusable_elements());

        // The 86-of-198 slot in the Stage-2 trace: a neighbour-role value the
        // consistency model created non-deterministically.
        let mut nondeterministic_neighbour = base.clone();
        nondeterministic_neighbour
            .neighbour_role_combinations
            .push(NativeAboxNeighbourRoleSet {
                neighbour_tag: 2,
                roles: vec![(RoleId::new(0), false)],
                role_values: Some(vec![NativeAboxRoleValue {
                    role: RoleId::new(0),
                    inversed: false,
                    deterministic: false,
                }]),
                merged_alias_deterministic: Some(false),
            });
        assert!(nondeterministic_neighbour.has_nondeterministic_neighbour_roles());
        assert!(nondeterministic_neighbour.has_reusable_elements());

        // A neighbour label whose every value is deterministic is NOT the
        // non-deterministic slot, even though the label itself exists.
        let mut deterministic_neighbour = base.clone();
        deterministic_neighbour
            .neighbour_role_combinations
            .push(NativeAboxNeighbourRoleSet {
                neighbour_tag: 2,
                roles: vec![(RoleId::new(0), false)],
                role_values: Some(vec![NativeAboxRoleValue {
                    role: RoleId::new(0),
                    inversed: false,
                    deterministic: true,
                }]),
                merged_alias_deterministic: Some(true),
            });
        assert!(!deterministic_neighbour.has_nondeterministic_neighbour_roles());
        assert!(!deterministic_neighbour.has_reusable_elements());

        // The 60-of-198 slot.
        let mut nondeterministic_same = base.clone();
        nondeterministic_same.nondeterministic_same_individuals = Some(vec![1, 2]);
        assert!(nondeterministic_same.has_reusable_elements());
        nondeterministic_same.nondeterministic_same_individuals = Some(Vec::new());
        assert!(!nondeterministic_same.has_reusable_elements());

        let mut nondeterministic_different = base.clone();
        nondeterministic_different.nondeterministic_different_individuals = Some(vec![1, 3]);
        assert!(nondeterministic_different.has_reusable_elements());

        let cache = NativeAboxRepresentativeCache {
            entries: HashMap::from([
                (1, base),
                (2, nondeterministic_concept),
                (3, nondeterministic_neighbour),
                (4, deterministic_neighbour),
                (5, nondeterministic_different),
            ]),
            ..Default::default()
        };
        let stats = native_association_nondeterminism_stats(&cache);
        assert_eq!(stats.total, 5);
        assert_eq!(stats.nondeterministic_concepts, 1);
        assert_eq!(stats.nondeterministic_neighbour_roles, 1);
        assert_eq!(stats.nondeterministic_same_individuals, 0);
        assert_eq!(stats.nondeterministic_different_individuals, 1);
        assert_eq!(stats.reusable_elements, 3);
    }

    /// Stage 8. The completion writeback publishes the model's
    /// non-deterministic half, and the per-task replay record carries it —
    /// but `deterministic_cached_concepts`, the ONLY list
    /// `replay_native_representative_cache` reads, drops it.
    ///
    /// This is the exact missing retained state: KM writes what Konclude's
    /// `reuseIndividualBackendExpansion` consumes and has no consumer for it
    /// (`completion::u25::reuse_individual_backend_expansion` is a PORT-PENDING
    /// stub). Nothing here asserts that the non-deterministic values SHOULD be
    /// replayed unconditionally — they must not be; upstream replays them under
    /// a branch alternative, never as base facts.
    #[test]
    fn replay_record_carries_nondeterministic_values_but_the_replay_list_drops_them() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into()],
            roles: vec!["r".into()],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: native_nominal_meta(vec![("a", "__nom__a", vec![])], vec![]),
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        assert!(native_representative_coordination_complete(
            &bridged,
            NativeRepresentativeCoordinationState::default(),
        ));
        let seed = bridged.nominal_seeds[0].clone();

        // Flip one published value's determinism bit in place. Rewriting the
        // bit keeps `concepts` and the value ordering intact, so the entry stays
        // well-formed under `native_cache_entry_covers_seed` — asserted below,
        // because an ill-formed entry would make the replay record empty and
        // the test vacuous.
        let nondeterministic = {
            let mut cache = bridged.native_representative_cache.borrow_mut();
            let entry = cache
                .as_mut()
                .expect("representative cache")
                .entries
                .get_mut(&seed.individual_tag)
                .expect("nominal association");
            let values = entry.concept_values.as_mut().expect("concept values");
            assert!(!values.is_empty(), "no published concept value to flip");
            let flipped = values[0];
            assert!(flipped.deterministic);
            values[0].deterministic = false;
            assert!(entry.has_reusable_elements());
            assert!(
                native_cache_entry_covers_seed(entry, &seed),
                "flipping the determinism bit invalidated the association"
            );
            (flipped.concept, flipped.negated)
        };

        install_native_nominal_backend_replay(&mut algo, &bridged);
        let replay = algo
            .native_nominal_backend_replay
            .get(&seed.individual_tag)
            .expect("typed replay record");
        assert!(
            replay
                .cached_concept_values
                .iter()
                .any(|&(concept, negated, deterministic)| (concept, negated) == nondeterministic
                    && !deterministic),
            "the replay record lost the non-deterministic association value"
        );
        assert!(
            !replay.deterministic_cached_concepts.contains(&nondeterministic),
            "a non-deterministic value entered the unconditional replay list"
        );
    }

    #[test]
    fn incomplete_native_neighbour_stays_blocked_with_both_linkers_retained() {
        let tin = cached_native_role_input();
        let (mut algo, mut ctx, bridged) =
            fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let source = bridged.nominal_seeds[0].clone();
        force_native_association_incomplete(&bridged, source.individual_tag, true);
        bridged
            .native_representative_cache
            .borrow_mut()
            .as_mut()
            .expect("representative cache")
            .entries
            .get_mut(&source.individual_tag)
            .expect("source association")
            .role_metadata_complete = false;

        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        let source_node =
            algo.get_up_to_date_individual_by_id(-source.individual_tag, &mut ctx);
        assert!(source_node.is_some());
        let source_ref = ctx.process_context().node(source_node);
        assert!(source_ref.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
        ));
        assert!(!source_ref.assertion_role_assertions().is_empty());
        assert!(!source_ref.reverse_assertion_role_assertions().is_empty());
        assert!(!source_ref.has_role_assertions_initialized());
        assert!(!source_ref.has_reverse_role_assertions_initialized());
        for untouched in &bridged.nominal_seeds[1..] {
            assert!(
                ctx.processing_data_box()
                    .individual_process_node_vector()
                    .get_data(-untouched.individual_tag)
                    .is_none(),
                "an incomplete association recursively materialized an uninfluenced neighbour"
            );
        }
    }

    #[test]
    fn native_critical_concept_unblocks_only_the_influenced_neighbour() {
        let tin = cached_native_role_input();
        let (mut algo, mut ctx, bridged) =
            fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let source = bridged.nominal_seeds[0].clone();
        let forward_target = bridged.nominal_seeds[1].individual_tag;
        let reverse_source = bridged.nominal_seeds[2].individual_tag;
        force_native_association_incomplete(&bridged, source.individual_tag, true);

        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        let source_node =
            algo.get_up_to_date_individual_by_id(-source.individual_tag, &mut ctx);
        let mut universal = Concept::new();
        universal
            .set_concept_tag(20_001)
            .set_operator_code(op::CCALL)
            .set_role(bridged.roles[0])
            .add_operand_linker(bridged.named[0], false)
            .set_operand_count(1);
        let universal = ctx.ontology_arenas_mut().alloc_concept(universal);
        let dependency = ctx.get_or_create_base_dependency_track_point();
        let mut source_mut = source_node;
        algo.add_concept_to_individual(
            universal,
            false,
            &mut source_mut,
            dependency,
            false,
            true,
            &mut ctx,
        );
        assert!(algo.process_native_nominal_backend_retest(source_node, &mut ctx));
        assert!(
            ctx.processing_data_box()
                .individual_process_node_vector()
                .get_data(-forward_target)
                .is_some(),
            "the universal's affected forward neighbour was not materialized"
        );
        assert!(
            ctx.processing_data_box()
                .individual_process_node_vector()
                .get_data(-reverse_source)
                .is_none(),
            "an unrelated incoming neighbour was materialized"
        );
        let source_ref = ctx.process_context().node(source_node);
        assert!(!source_ref.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
        ));
        assert!(!source_ref.has_role_assertions_initialized());
        assert!(!source_ref.has_reverse_role_assertions_initialized());
    }

    #[test]
    fn native_cardinality_criticality_releases_neighbour_only_block() {
        let tin = cached_native_role_input();
        let (mut algo, mut ctx, bridged) =
            fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let source = bridged.nominal_seeds[0].clone();
        force_native_association_incomplete(&bridged, source.individual_tag, true);

        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        let source_node =
            algo.get_up_to_date_individual_by_id(-source.individual_tag, &mut ctx);
        let neighbour_block =
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED;
        let successor_block =
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED;
        assert!(
            ctx.process_context()
                .node(source_node)
                .has_partial_processing_restriction_flags(neighbour_block),
            "Konclude blocks neighbour expansion even for an incomplete association"
        );
        assert!(
            !ctx.process_context()
                .node(source_node)
                .has_partial_processing_restriction_flags(successor_block),
            "an incomplete association must not acquire full successor blocking"
        );
        let mut at_most = Concept::new();
        at_most
            .set_concept_tag(20_002)
            .set_operator_code(op::CCATMOST)
            .set_parameter(0)
            .set_role(bridged.roles[0])
            .add_operand_linker(ctx.processing_data_box().ontology_top_concept(), false)
            .set_operand_count(1);
        let at_most = ctx.ontology_arenas_mut().alloc_concept(at_most);
        let dependency = ctx.get_or_create_base_dependency_track_point();
        let mut source_mut = source_node;
        algo.add_concept_to_individual(
            at_most,
            false,
            &mut source_mut,
            dependency,
            false,
            true,
            &mut ctx,
        );
        assert!(algo.process_native_nominal_backend_retest(source_node, &mut ctx));
        assert!(
            !ctx.process_context()
                .node(source_node)
                .has_partial_processing_restriction_flags(neighbour_block),
            "critical at-most did not release neighbour expansion blocking"
        );
        assert!(
            !ctx.process_context()
                .node(source_node)
                .has_partial_processing_restriction_flags(successor_block),
            "selective expansion fabricated successor blocking"
        );
        assert!(ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-bridged.nominal_seeds[1].individual_tag)
            .is_some());
        assert!(!ctx
            .process_context()
            .node(source_node)
            .has_role_assertions_initialized());
    }

    /// Demote every forward cached neighbour-role value of `individual_tag` towards
    /// `neighbour_tag` to NON-deterministic — the shape the 9540 completion writer
    /// produces for any edge with a non-deterministically merged endpoint
    /// (`native_completion_role_metadata`'s
    /// `edge_deterministic = source_merge_deterministic && target_merge_deterministic`;
    /// the Stage-2 trace records 86 of 198 roots with a populated
    /// `NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL`).
    fn demote_cached_neighbour_role_values(
        bridged: &Bridged,
        individual_tag: Cint64,
        neighbour_tag: Cint64,
    ) {
        let mut cache = bridged.native_representative_cache.borrow_mut();
        let entry = cache
            .as_mut()
            .expect("representative cache")
            .entries
            .get_mut(&individual_tag)
            .expect("source association");
        let mut demoted = false;
        for combination in &mut entry.neighbour_role_combinations {
            if combination.neighbour_tag != neighbour_tag {
                continue;
            }
            for value in combination.role_values.iter_mut().flatten() {
                if !value.inversed {
                    value.deterministic = false;
                    demoted = true;
                }
            }
        }
        assert!(
            demoted,
            "the fixture must carry a forward cached neighbour-role value"
        );
    }

    /// A/B leg of [`asserted_edge_survives_nondeterministic_cache_marking`]: with
    /// `conf_native_selective_neighbour_per_value_decline = false` the pre-fix
    /// per-NODE latch is restored — one unjustifiable neighbour value consumes both
    /// assertion linkers, marks the node fully expanded and drops every
    /// cached-association blocking bit. Konclude's caller shape (cpp 8938) is
    /// `if (!backendSyncData || !expandDirectlyInfluenced…()) { clearAssertionRoles();
    /// … addRoleAssertion(…) }`, so this IS the declined-path contract; what the fix
    /// changes is only WHEN the route declines.
    #[test]
    fn raw_assertion_replay_runs_only_when_selective_cache_expansion_declines() {
        let tin = cached_native_role_input();
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let source = bridged.nominal_seeds[0].clone();
        let forward_target = bridged.nominal_seeds[1].individual_tag;
        let reverse_source = bridged.nominal_seeds[2].individual_tag;
        force_native_association_incomplete(&bridged, source.individual_tag, true);
        demote_cached_neighbour_role_values(&bridged, source.individual_tag, forward_target);

        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        algo.conf_native_selective_neighbour_per_value_decline = false;
        let source_node = algo.get_up_to_date_individual_by_id(-source.individual_tag, &mut ctx);
        assert!(source_node.is_some());
        assert!(ctx
            .process_context()
            .node(source_node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
            ));
        assert!(!ctx
            .process_context()
            .node(source_node)
            .has_role_assertions_initialized());

        // A universal over the cached role is neighbour-critical, so the block is
        // released and the selective expansion is attempted first.
        let mut universal = Concept::new();
        universal
            .set_concept_tag(20_003)
            .set_operator_code(op::CCALL)
            .set_role(bridged.roles[0])
            .add_operand_linker(bridged.named[0], false)
            .set_operand_count(1);
        let universal = ctx.ontology_arenas_mut().alloc_concept(universal);
        let dependency = ctx.get_or_create_base_dependency_track_point();
        let mut source_mut = source_node;
        algo.add_concept_to_individual(
            universal,
            false,
            &mut source_mut,
            dependency,
            false,
            true,
            &mut ctx,
        );
        assert!(algo.process_native_nominal_backend_retest(source_node, &mut ctx));

        let source_ref = ctx.process_context().node(source_node);
        assert!(
            source_ref.has_role_assertions_initialized()
                && source_ref.has_reverse_role_assertions_initialized(),
            "a declined selective expansion did not fall back to the raw replay"
        );
        assert!(
            source_ref.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION,
            ),
            "the raw replay did not mark the node fully expanded"
        );
        let native_blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED;
        assert_eq!(
            source_ref.processing_restriction_flags() & native_blocking_flags,
            0,
            "a materialized node kept cached-association blocking bits"
        );
        // Both directions are replayed by the fallback — that is exactly what the
        // selective route exists to avoid.
        assert!(ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-forward_target)
            .is_some());
        assert!(ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-reverse_source)
            .is_some());
    }

    /// An ABox role assertion holds in every model, so a NON-deterministic cache
    /// marking on it (which only records that an ENDPOINT was merged
    /// non-deterministically) must not cost the node its association block.
    ///
    /// This is the 9540 latch: the Stage-2 trace shows `corridorTI_3` (node -42, the
    /// individual `Image_type ≡ {corridorTI_3}` reduces to) carrying
    /// `nondetNeighbourRoles=new/sig:208/count:6` and all 59 `corridorTI_3_RS_*`
    /// roots `nondetMergedInto=-38`
    /// (`diagnostics/9540-konclude-trace/run-49428590/trace.log`), while Konclude
    /// keeps every one of them cache-backed for the whole classification
    /// (`rawRoleAssertionReplay=0`, ONE `expandIndividualNeighbourNodeFromBackendCache`
    /// in the entire `Image_type` subsumption test). Before the fix KM turned each
    /// of those roots into a fully materialized, `PRF_INVALIDBLOCKINGORCACHING` node
    /// during the single full-consistency completion, i.e. BEFORE the retained
    /// classification base is snapshotted, so every later class job inherited an
    /// ABox with all named edges installed and no blocking left to re-establish.
    #[test]
    fn asserted_edge_survives_nondeterministic_cache_marking() {
        let tin = cached_native_role_input();
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let source = bridged.nominal_seeds[0].clone();
        let forward_target = bridged.nominal_seeds[1].individual_tag;
        let reverse_source = bridged.nominal_seeds[2].individual_tag;
        force_native_association_incomplete(&bridged, source.individual_tag, true);
        // `r(a, b)` is asserted by `cached_native_role_input`.
        demote_cached_neighbour_role_values(&bridged, source.individual_tag, forward_target);

        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        assert!(
            algo.conf_native_selective_neighbour_per_value_decline,
            "the per-value decline is the production default"
        );
        let source_node = algo.get_up_to_date_individual_by_id(-source.individual_tag, &mut ctx);
        assert!(source_node.is_some());

        // A universal over the cached role is neighbour-critical, so the block is
        // released and the selective expansion is attempted first.
        let mut universal = Concept::new();
        universal
            .set_concept_tag(20_004)
            .set_operator_code(op::CCALL)
            .set_role(bridged.roles[0])
            .add_operand_linker(bridged.named[0], false)
            .set_operand_count(1);
        let universal = ctx.ontology_arenas_mut().alloc_concept(universal);
        let dependency = ctx.get_or_create_base_dependency_track_point();
        let mut source_mut = source_node;
        algo.add_concept_to_individual(
            universal,
            false,
            &mut source_mut,
            dependency,
            false,
            true,
            &mut ctx,
        );
        assert!(algo.process_native_nominal_backend_retest(source_node, &mut ctx));
        assert!(
            !algo.native_selective_neighbour_expansion_declined,
            "an asserted edge with a non-deterministic cache marking declined the route"
        );

        let source_ref = ctx.process_context().node(source_node);
        assert!(
            !source_ref.has_role_assertions_initialized()
                && !source_ref.has_reverse_role_assertions_initialized(),
            "the selective route fell back to the raw bidirectional replay"
        );
        assert!(
            !source_ref.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION
                    | IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            ),
            "the node was latched out of cached-association blocking"
        );
        // The asserted, influenced neighbour IS materialized — the edge itself is
        // entailed and is installed on the base dependency exactly as the raw replay
        // would have installed it.
        assert!(
            ctx.processing_data_box()
                .individual_process_node_vector()
                .get_data(-forward_target)
                .is_some(),
            "the asserted forward edge was dropped"
        );
        // The unrelated incoming neighbour stays cache-backed — the whole point.
        assert!(
            ctx.processing_data_box()
                .individual_process_node_vector()
                .get_data(-reverse_source)
                .is_none(),
            "an uninfluenced neighbour was materialized anyway"
        );
    }

    /// The complement: a cached neighbour-role value that is NOT an ABox assertion
    /// and is marked non-deterministic is skipped, and skipping it costs nothing —
    /// the raw replay fallback (`materialize_native_role_assertion_vectors`) replays
    /// the assertion chains only, so it would not have installed that edge either.
    /// The node keeps its association block and its other neighbours stay cached.
    #[test]
    fn derived_nondeterministic_cached_neighbour_is_skipped_without_losing_the_node_cache() {
        let tin = cached_native_role_input();
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let source = bridged.nominal_seeds[0].clone();
        let forward_target = bridged.nominal_seeds[1].individual_tag;
        let unrelated = bridged.nominal_seeds[2].individual_tag;
        force_native_association_incomplete(&bridged, source.individual_tag, true);

        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        // Inject a DERIVED non-deterministic `r(a, c)` into the replay journal: `c`
        // is a neighbour of `a` only through the asserted `s(c, a)`, so `r(a, c)` is
        // not asserted in either direction.
        {
            let replay = algo
                .native_nominal_backend_replay
                .get_mut(&source.individual_tag)
                .expect("replay journal installed for the source individual");
            assert!(
                !replay.role_assertions.contains(&(bridged.roles[0], unrelated)),
                "the fixture must not assert the injected derived edge"
            );
            replay
                .cached_neighbour_roles
                .push((unrelated, bridged.roles[0], false, false));
            replay.cached_neighbour_roles.sort_unstable_by_key(
                |(neighbour, role, inversed, deterministic)| {
                    (*neighbour, role.raw, *inversed, *deterministic)
                },
            );
        }
        let source_node = algo.get_up_to_date_individual_by_id(-source.individual_tag, &mut ctx);
        assert!(source_node.is_some());

        let mut universal = Concept::new();
        universal
            .set_concept_tag(20_005)
            .set_operator_code(op::CCALL)
            .set_role(bridged.roles[0])
            .add_operand_linker(bridged.named[0], false)
            .set_operand_count(1);
        let universal = ctx.ontology_arenas_mut().alloc_concept(universal);
        let dependency = ctx.get_or_create_base_dependency_track_point();
        let mut source_mut = source_node;
        algo.add_concept_to_individual(
            universal,
            false,
            &mut source_mut,
            dependency,
            false,
            true,
            &mut ctx,
        );
        assert!(algo.process_native_nominal_backend_retest(source_node, &mut ctx));
        assert!(
            !algo.native_selective_neighbour_expansion_declined,
            "a skippable derived value declined the whole node's cache"
        );

        let source_ref = ctx.process_context().node(source_node);
        assert!(
            !source_ref.has_role_assertions_initialized()
                && !source_ref.has_reverse_role_assertions_initialized(),
            "the selective route fell back to the raw bidirectional replay"
        );
        assert!(
            !source_ref.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION
                    | IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            ),
            "the node was latched out of cached-association blocking"
        );
        assert!(
            ctx.processing_data_box()
                .individual_process_node_vector()
                .get_data(-forward_target)
                .is_some(),
            "the deterministic asserted neighbour was not expanded"
        );
        assert!(
            ctx.processing_data_box()
                .individual_process_node_vector()
                .get_data(-unrelated)
                .is_none(),
            "an unentailed derived edge was installed on the base dependency"
        );
    }

    /// Minimized `ore_ont_9540` shape, from the Stage-2 Konclude trace
    /// (`diagnostics/9540-konclude-trace/ANALYSIS.md`):
    ///
    /// ```text
    /// ImageType     ≡ {a}
    /// ImageWithDoor ≡ ∃contains.Door ⊓ ImageType
    /// ClassAssertion(ImageType a)              contains(a, d)
    /// ```
    ///
    /// `ImageType ⊑ ImageWithDoor` must NOT hold: nothing forces `a` to contain a
    /// `Door`, so the pair is SATISFIABLE — the answer the traced probe gives
    /// (`classifier.pairresult … taskSatisfiable=1 subsumptionHolds=0`). The
    /// at-most assertion puts the ontology on the cardinality+ABox profile, i.e. the
    /// cache-backed root route this change touches.
    #[test]
    fn minimized_9540_nominal_class_pair_stays_satisfiable() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let mut meta = native_nominal_meta(
            vec![
                (
                    "a",
                    "__nom__a",
                    vec![
                        C::Name("ImageType".into()),
                        C::AtMost(5, R::Name("contains".into()), Box::new(C::Top)),
                    ],
                ),
                ("d", "__nom__d", vec![]),
            ],
            vec![],
        );
        meta.role_assertions.push(nominal_role("contains", "a", "d"));
        let door = C::Exists(
            R::Name("contains".into()),
            Box::new(C::Name("Door".into())),
        );
        let tin = TInput {
            concepts: vec![
                "ImageType".into(),
                "ImageWithDoor".into(),
                "Door".into(),
                "__nom__a".into(),
                "__nom__d".into(),
            ],
            roles: vec!["contains".into()],
            queries: vec![0, 1, 2],
            number: true,
            source_axioms: vec![
                source_subclass(C::Name("ImageType".into()), C::Nominal("a".into())),
                source_subclass(C::Nominal("a".into()), C::Name("ImageType".into())),
                source_subclass(
                    C::Name("ImageWithDoor".into()),
                    C::And([door.clone(), C::Name("ImageType".into())].into_iter().collect()),
                ),
                source_subclass(
                    C::And([door, C::Name("ImageType".into())].into_iter().collect()),
                    C::Name("ImageWithDoor".into()),
                ),
            ],
            nominal_abox: meta,
            ..Default::default()
        };
        let result = bridged_classify_opts_with_trigger_absorption(&tin, true, false, true)
            .expect("the minimized 9540 pair must be decided");
        assert!(result.consistent);
        assert!(result.unsatisfiable.is_empty());
        assert!(
            !result.subsumptions.contains(&(0, 1)),
            "ImageType ⊑ ImageWithDoor must stay satisfiable: no Door container is asserted"
        );
    }

    /// Minimized ore_ont_9540 `UJI_Wall ⊑ Possible_UJI_Wall` shape.
    ///
    /// `Upper` and `Lower` are defined over the SAME conjuncts, with `Upper`'s
    /// conjunct set a strict subset of `Lower`'s, and one shared conjunct is a
    /// disjunction — so the reverse absorbed implication for `Upper` is carried
    /// only by the branch a single completion model commits to, which is exactly
    /// why the model-based candidate set missed the pair on 9540. `Lower` also
    /// carries a told superclass, like `UJI_Wall`, so its equivalence cannot be
    /// hosted as one direct definition. `Chain` puts a told subclass underneath
    /// `Lower` so transitivity is covered too.
    fn definition_containment_input() -> TInput {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let choice = C::Or(
            [C::Name("P".into()), C::Name("Q".into())]
                .into_iter()
                .collect(),
        );
        let shared = C::Exists(R::Name("r".into()), Box::new(C::Name("B".into())));
        let extra = C::Exists(R::Name("s".into()), Box::new(C::Name("B".into())));
        let upper = C::And(
            [C::Name("A".into()), choice.clone(), shared.clone()]
                .into_iter()
                .collect(),
        );
        let lower = C::And(
            [C::Name("A".into()), choice, shared, extra]
                .into_iter()
                .collect(),
        );
        TInput {
            concepts: vec![
                "A".into(),
                "P".into(),
                "Q".into(),
                "B".into(),
                "Upper".into(),
                "Lower".into(),
                "Chain".into(),
            ],
            roles: vec!["r".into(), "s".into()],
            queries: vec![0, 1, 2, 3, 4, 5, 6],
            source_axioms: vec![
                source_equivalence(C::Name("Upper".into()), upper),
                source_equivalence(C::Name("Lower".into()), lower),
                source_subclass(C::Name("Lower".into()), C::Name("A".into())),
                source_subclass(C::Name("Chain".into()), C::Name("Lower".into())),
            ],
            ..Default::default()
        }
    }

    #[test]
    fn source_closure_derives_definition_containment_transitively_without_the_converse() {
        let tin = definition_containment_input();
        let closure = source_named_subsumer_closure(&tin);
        let (a, upper, lower, chain) = (0usize, 4usize, 5usize, 6usize);

        let mut derived: Vec<(usize, usize)> = closure.iter().copied().collect();
        derived.sort_unstable();
        let mut expected = vec![
            (upper, a),
            (lower, a),
            (lower, upper),
            (chain, a),
            (chain, lower),
            (chain, upper),
        ];
        expected.sort_unstable();
        assert_eq!(
            derived, expected,
            "the exact source closure must derive the definition-containment \
             subsumer, its transitive closure, and nothing else"
        );
        // Conjunct containment holds in ONE direction only: `Lower`'s conjuncts
        // cover `Upper`'s definition, never the other way round.
        assert!(!closure.contains(&(upper, lower)));
        assert!(!closure.contains(&(upper, chain)));
        assert!(!closure.contains(&(a, upper)));
    }

    #[test]
    fn definition_containment_subsumers_reach_the_classification_output() {
        let tin = definition_containment_input();
        let (a, upper, lower, chain) = (0usize, 4usize, 5usize, 6usize);
        let entailed = [
            (lower, upper),
            (chain, upper),
            (chain, lower),
            (upper, a),
            (lower, a),
            (chain, a),
        ];
        let unentailed = [(upper, lower), (upper, chain), (a, upper), (a, lower)];

        // The 9540 route: source mode with trigger absorption, saturation folded
        // off (native nominals do that there, an empty ABox does it here), so
        // the KPSet seeds come from the exact closure.
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("the minimized definition-containment TBox must be decided");
        assert!(result.consistent);
        assert!(result.unsatisfiable.is_empty());
        for pair in entailed {
            assert!(
                result.subsumptions.contains(&pair),
                "entailed pair {pair:?} missing from the classification output"
            );
        }
        for pair in unentailed {
            assert!(
                !result.subsumptions.contains(&pair),
                "unentailed pair {pair:?} must not be emitted"
            );
        }

        // Same requirement on the saturation route. A defer there is a different
        // failure mode (budget/fragment) and is covered by its own tests; what
        // this asserts is that the route cannot LOSE the closure pairs.
        let saturated = bridged_classify_opts_with_trigger_absorption(&tin, true, true, true);
        if let Some(saturated) = saturated {
            for pair in entailed {
                assert!(
                    saturated.subsumptions.contains(&pair),
                    "the saturation route dropped entailed pair {pair:?}"
                );
            }
            for pair in unentailed {
                assert!(
                    !saturated.subsumptions.contains(&pair),
                    "the saturation route emitted unentailed pair {pair:?}"
                );
            }
        }
    }

    #[test]
    fn native_abox_replay_blocks_then_invalidates_on_new_concept() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let meta = native_nominal_meta(vec![("a", "__nom__a", vec![C::Name("A".into())])], vec![]);
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "__nom__a".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: meta,
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let seed = bridged.nominal_seeds[0].clone();
        {
            let mut cache = bridged.native_representative_cache.borrow_mut();
            let entry = cache
                .as_mut()
                .expect("representative cache written")
                .entries
                .get_mut(&seed.individual_tag)
                .expect("representative entry");
            entry.completely_saturated = true;
            entry.completely_handled = true;
            entry.completely_propagated = true;
            entry.insufficient = false;
            entry.representative_same_individual_merging = Some(false);
            entry.deterministic_same_individual_label_identity = Some(11);
            entry.deterministic_merged_same_considered_label_identity = Some(11);
            assert!(entry.concepts.contains(&(bridged.named[0], false)));
            assert!(entry.reusable_for_full_completion());
        }
        let blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED;

        reset_probe_env(&mut algo, &mut ctx, &bridged, true);
        let node = ctx.get_up_to_date_individual_by_id(-seed.individual_tag);
        assert!(node.is_some());
        assert!(
            algo.native_nominal_backend_replay[&seed.individual_tag].expansion_blocking_candidate,
            "the complete typed association was not eligible for replay"
        );
        assert_eq!(
            ctx.process_context()
                .node(node)
                .processing_restriction_flags()
                & blocking_flags,
            blocking_flags,
            "representative replay did not install the exact blocking flags"
        );
        assert!(
            try_establish_native_backend_expansion_blocking(
                &mut algo, &mut ctx, &bridged, &seed, node,
            ),
            "the bridge-level blocking helper rejected a synchronized association"
        );
        let base = ctx.get_or_create_base_dependency_track_point();
        let mut modified = node;
        algo.add_concept_to_individual(
            bridged.named[1],
            false,
            &mut modified,
            base,
            false,
            true,
            &mut ctx,
        );
        assert!(
            algo.process_native_nominal_backend_retest(node, &mut ctx),
            "native backend retest failed"
        );
        let successor_blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED;
        assert_eq!(
            ctx.process_context()
                .node(node)
                .processing_restriction_flags()
                & successor_blocking_flags,
            0,
            "a changed concept label retained stale successor blocking"
        );
        assert!(ctx
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
            ));
        assert!(!ctx
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            ),
            "a concept-only retest invalidated the reusable neighbour labels"
        );
        let label = ctx.process_context().node(node).reapply_con_label_set;
        assert!(label.is_some());
        assert!(ctx
            .process_context()
            .label_set(label)
            .contains_concept_in_context(
                ctx.process_context(),
                ctx.ontology_arenas(),
                bridged.named[1],
                false,
            ));
    }

    #[test]
    fn successful_completion_writeback_is_transactional_and_enables_next_replay() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: native_nominal_meta(
                vec![("a", "__nom__a", vec![C::Name("A".into())])],
                vec![],
            ),
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let seed = bridged.nominal_seeds[0].clone();
        {
            let mut cache = bridged.native_representative_cache.borrow_mut();
            let entry = cache
                .as_mut()
                .expect("saturation association")
                .entries
                .get_mut(&seed.individual_tag)
                .expect("nominal association");
            // Force representative recomputation while retaining a well-typed
            // source association for deterministic label replay.
            entry.completely_handled = false;
            entry.insufficient = true;
            entry.synchronization_metadata_complete = false;
        }
        let selected = HashSet::from([seed.individual_tag]);
        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        let frozen_used_association_update_ids =
            freeze_native_representative_association_versions(&algo);
        assert!(initialize_native_nominal_state_for_tags(
            &mut algo,
            &mut ctx,
            &bridged,
            Some(&selected),
        ));
        algo.probe_budget = Some(std::time::Duration::from_secs(10));
        configure_production_search(&mut algo);
        assert_eq!(
            native_nominal_consistency(&mut algo, &mut ctx, &bridged),
            Some(true)
        );

        let node = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-seed.individual_tag);
        assert!(node.is_some());
        let old_update_id = bridged
            .native_representative_cache
            .borrow()
            .as_ref()
            .expect("representative cache")
            .entries[&seed.individual_tag]
            .association_update_id;

        // A task can finish without a usable consumed-association version.
        // Declining that shape must not partially replace the old incomplete
        // entry.
        let mut missing_used_association_update_ids = frozen_used_association_update_ids.clone();
        assert!(missing_used_association_update_ids
            .remove(&seed.individual_tag)
            .is_some());
        assert!(write_completed_native_representative_associations(
            &ctx,
            &bridged,
            NativeSuccessfulRepresentativeTask {
                selected_individuals: &selected,
                used_association_update_ids: &missing_used_association_update_ids,
            },
        )
        .is_none());
        {
            let cache = bridged.native_representative_cache.borrow();
            let old_entry =
                &cache.as_ref().expect("representative cache").entries[&seed.individual_tag];
            assert_eq!(old_entry.association_update_id, old_update_id);
            assert_eq!(
                old_entry.association_origin,
                Some(NativeAboxAssociationOrigin::IndividualSaturation)
            );
            assert!(!old_entry.synchronization_metadata_complete);
        }

        // A frozen task version that no longer equals the cache version must
        // also abort before the first association mutation.
        let mut stale_used_association_update_ids = frozen_used_association_update_ids.clone();
        *stale_used_association_update_ids
            .get_mut(&seed.individual_tag)
            .expect("frozen task association version") += 1;
        assert!(write_completed_native_representative_associations(
            &ctx,
            &bridged,
            NativeSuccessfulRepresentativeTask {
                selected_individuals: &selected,
                used_association_update_ids: &stale_used_association_update_ids,
            },
        )
        .is_none());
        assert_eq!(
            bridged
                .native_representative_cache
                .borrow()
                .as_ref()
                .expect("representative cache")
                .entries[&seed.individual_tag]
                .association_update_id,
            old_update_id,
            "a stale frozen task version changed the cache"
        );

        let updated = write_completed_native_representative_associations(
            &ctx,
            &bridged,
            NativeSuccessfulRepresentativeTask {
                selected_individuals: &selected,
                used_association_update_ids: &frozen_used_association_update_ids,
            },
        )
        .expect("complete task association writeback");
        assert_eq!(updated, selected);
        {
            let cache = bridged.native_representative_cache.borrow();
            let written =
                &cache.as_ref().expect("representative cache").entries[&seed.individual_tag];
            assert!(written.reusable_for_full_completion());
            assert_eq!(
                written.association_origin,
                Some(NativeAboxAssociationOrigin::CompletionWriteback)
            );
            assert!(written.association_update_id > old_update_id);
            assert_eq!(written.used_association_update_id, Some(old_update_id));
            assert_eq!(written.scheduled_individual, Some(true));
        }

        let blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED;
        reset_probe_env(&mut algo, &mut ctx, &bridged, true);
        let replayed = ctx.get_up_to_date_individual_by_id(-seed.individual_tag);
        assert_eq!(
            ctx.process_context()
                .node(replayed)
                .processing_restriction_flags()
                & blocking_flags,
            blocking_flags,
            "valid writeback was not expansion-blocked on the next task"
        );
        assert!(
            ctx.process_context()
                .node(replayed)
                .is_nominal_individual_representative_backend_data_loaded(),
            "valid writeback was not replayed into the next task"
        );
    }

    #[test]
    fn selective_writeback_preserves_untouched_neighbour_labels_and_versions() {
        let tin = cached_native_role_input();
        let (mut algo, mut ctx, bridged) =
            fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let source = bridged.nominal_seeds[0].clone();
        force_native_association_incomplete(&bridged, source.individual_tag, true);
        let (old_source_neighbours, untouched_versions) = {
            let cache = bridged.native_representative_cache.borrow();
            let cache = cache.as_ref().expect("representative cache");
            (
                cache.entries[&source.individual_tag]
                    .neighbour_role_combinations
                    .clone(),
                bridged.nominal_seeds[1..]
                    .iter()
                    .map(|seed| {
                        (
                            seed.individual_tag,
                            cache.entries[&seed.individual_tag].association_update_id,
                        )
                    })
                    .collect::<HashMap<_, _>>(),
            )
        };

        let selected = HashSet::from([source.individual_tag]);
        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        let frozen = freeze_native_representative_association_versions(&algo);
        assert!(initialize_native_nominal_state_for_tags(
            &mut algo,
            &mut ctx,
            &bridged,
            Some(&selected),
        ));
        algo.probe_budget = Some(std::time::Duration::from_secs(10));
        configure_production_search(&mut algo);
        assert_eq!(
            native_nominal_consistency(&mut algo, &mut ctx, &bridged),
            Some(true)
        );
        for untouched in &bridged.nominal_seeds[1..] {
            assert!(ctx
                .processing_data_box()
                .individual_process_node_vector()
                .get_data(-untouched.individual_tag)
                .is_none());
        }

        let updated = write_completed_native_representative_associations(
            &ctx,
            &bridged,
            NativeSuccessfulRepresentativeTask {
                selected_individuals: &selected,
                used_association_update_ids: &frozen,
            },
        )
        .expect("selective association writeback");
        assert_eq!(updated, selected);
        let cache = bridged.native_representative_cache.borrow();
        let cache = cache.as_ref().expect("representative cache");
        assert_eq!(
            cache.entries[&source.individual_tag].neighbour_role_combinations,
            old_source_neighbours,
            "an unexpanded neighbour label was reconstructed instead of reused"
        );
        for (tag, version) in untouched_versions {
            assert_eq!(
                cache.entries[&tag].association_update_id, version,
                "an untouched neighbour association version advanced"
            );
        }
    }

    #[test]
    fn sparse_writeback_ignores_unselected_tag_zero_alias_but_rejects_selected_mismatch() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: native_nominal_meta(
                vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
                vec![],
            ),
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) =
            fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let untouched = bridged.nominal_seeds[0].clone();
        let selected_seed = bridged.nominal_seeds[1].clone();
        assert_eq!(untouched.individual_tag, 0);
        force_native_association_incomplete(&bridged, selected_seed.individual_tag, true);
        let selected = HashSet::from([selected_seed.individual_tag]);

        reset_probe_env_impl(&mut algo, &mut ctx, &bridged, true, false);
        let frozen = freeze_native_representative_association_versions(&algo);
        assert!(initialize_native_nominal_state_for_tags(
            &mut algo,
            &mut ctx,
            &bridged,
            Some(&selected),
        ));
        algo.probe_budget = Some(std::time::Duration::from_secs(10));
        configure_production_search(&mut algo);
        assert_eq!(
            native_nominal_consistency(&mut algo, &mut ctx, &bridged),
            Some(true)
        );

        // `-0 == 0`: emulate the generated-node value that shares the
        // double-dynamic vector key with an unmaterialized tag-zero nominal.
        let alias = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        ctx.process_context_mut()
            .node_mut(alias)
            .set_individual_node_id(0);
        ctx.processing_data_box_mut()
            .individual_process_node_vector_mut()
            .set_local_data(0, alias);
        assert_eq!(
            ctx.processing_data_box()
                .individual_process_node_vector()
                .get_data(0),
            alias
        );
        assert!(
            native_exact_nominal_process_node(&ctx, untouched.individual_tag).is_none(),
            "a generated node was mistaken for the untouched tag-zero nominal"
        );

        let untouched_before = bridged
            .native_representative_cache
            .borrow()
            .as_ref()
            .expect("representative cache")
            .entries[&untouched.individual_tag]
            .clone();
        let updated = write_completed_native_representative_associations(
            &ctx,
            &bridged,
            NativeSuccessfulRepresentativeTask {
                selected_individuals: &selected,
                used_association_update_ids: &frozen,
            },
        )
        .expect("tag-zero alias must not poison selective writeback");
        assert_eq!(updated, selected);
        assert_eq!(
            bridged
                .native_representative_cache
                .borrow()
                .as_ref()
                .expect("representative cache")
                .entries[&untouched.individual_tag],
            untouched_before,
            "an untouched association or its update id changed"
        );

        // Conversely, a selected association must still have an exact
        // materialized ontology individual. Reject a mismatched slot before
        // any cache entry or monotone update counter changes.
        ctx.processing_data_box_mut()
            .individual_process_node_vector_mut()
            .set_local_data(-selected_seed.individual_tag, alias);
        let cache_before_failure = bridged
            .native_representative_cache
            .borrow()
            .as_ref()
            .expect("representative cache")
            .clone();
        assert!(
            write_completed_native_representative_associations(
                &ctx,
                &bridged,
                NativeSuccessfulRepresentativeTask {
                    selected_individuals: &selected,
                    used_association_update_ids: &frozen,
                },
            )
            .is_none(),
            "a selected association with the wrong individual identity was accepted"
        );
        assert_eq!(
            bridged
                .native_representative_cache
                .borrow()
                .as_ref()
                .expect("representative cache"),
            &cache_before_failure,
            "failed selected writeback partially mutated the cache"
        );
    }

    #[test]
    fn native_abox_positive_role_assertion_is_exact_existential() {
        use crate::frontend::syntax::{Concept as C, Role as R};
        use crate::json_io::NominalRoleAssertionMeta;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let mut meta = native_nominal_meta(
            vec![
                (
                    "a",
                    "__nom__a",
                    vec![C::Forall(
                        R::Name("r".into()),
                        Box::new(C::Not(Box::new(C::Nominal("b".into())))),
                    )],
                ),
                ("b", "__nom__b", vec![]),
            ],
            vec![],
        );
        meta.role_assertions.push(NominalRoleAssertionMeta {
            role: "r".into(),
            source: "a".into(),
            target: "b".into(),
        });
        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            nominal_abox: meta,
            ..Default::default()
        };
        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(
            !empty_role_nominal_model_certificate(&tin, &bridged),
            "a positive role assertion must prevent the empty-role shortcut"
        );
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("positive native role assertion must be decided");
        assert!(
            !result.consistent,
            "R(a,b) must clash with a : forall R.not {{b}}"
        );

        let mut direct_tin = tin.clone();
        // `card_defs` is only an encoding side channel. Production routing
        // uses `TInput::number`, which remains true even when
        // KM_NO_HT_CARD keeps the clausal encoding and emits no card_defs.
        direct_tin.number = true;
        direct_tin.card_defs.push(CardDefJson {
            marker: 0,
            min: false,
            n: 2,
            role: 0,
            filler: 0,
        });
        let (mut direct_algo, mut direct_ctx, direct) =
            fresh_bridge_env_with_trigger_absorption(&direct_tin, true);
        assert!(direct.direct_native_role_assertions);
        let source_seed = &direct.nominal_seeds[0];
        assert!(
            !source_seed.assertions.iter().any(|&(concept, negated)| {
                !negated
                    && direct_ctx
                        .ontology_arenas()
                        .concept(concept)
                        .get_operator_code()
                        == op::CCSOME
                    && direct_ctx.ontology_arenas().concept(concept).get_role() == direct.roles[0]
            }),
            "the generated positive role assertion leaked back into completion concepts"
        );
        let source = direct_ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-source_seed.individual_tag);
        let target = direct_ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-direct.nominal_seeds[1].individual_tag);
        assert!(
            direct_algo
                .ht_role_successor_links(source, direct.roles[0], &direct_ctx)
                .iter()
                .any(|&(_, successor)| successor == target),
            "the typed role assertion was not installed as a named edge"
        );
        configure_production_search(&mut direct_algo);
        assert_eq!(
            native_nominal_consistency(&mut direct_algo, &mut direct_ctx, &direct),
            Some(false),
            "the direct named edge must preserve the assertion clash"
        );
    }

    #[test]
    fn native_direct_role_assertion_defers_on_multihop_target_merge() {
        use crate::frontend::syntax::Concept as C;
        use crate::orchestrate::cb_to_ht::CardDefJson;

        let tin = TInput {
            concepts: vec![
                "A".into(),
                "__nom__a".into(),
                "__nom__b".into(),
                "__nom__c".into(),
                "__nom__d".into(),
            ],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 0,
            }],
            nominal_abox: native_nominal_meta(
                vec![
                    ("a", "__nom__a", vec![]),
                    ("b", "__nom__b", vec![]),
                    ("c", "__nom__c", vec![]),
                    ("d", "__nom__d", vec![]),
                ],
                vec![],
            ),
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        let source = ctx.get_up_to_date_individual_by_id(-bridged.nominal_seeds[0].individual_tag);
        let target = ctx.get_up_to_date_individual_by_id(-bridged.nominal_seeds[1].individual_tag);
        let middle = ctx.get_up_to_date_individual_by_id(-bridged.nominal_seeds[2].individual_tag);
        let representative =
            ctx.get_up_to_date_individual_by_id(-bridged.nominal_seeds[3].individual_tag);
        let middle_id = ctx.process_context().node(middle).individual_node_id();
        let representative_id = ctx
            .process_context()
            .node(representative)
            .individual_node_id();
        let merge_track = ctx.get_or_create_base_dependency_track_point();
        ctx.process_context_mut()
            .node_mut(target)
            .set_merged_into_individual_node_id(middle_id)
            .set_merged_dependency_track_point(merge_track);
        ctx.process_context_mut()
            .node_mut(middle)
            .set_merged_into_individual_node_id(representative_id)
            .set_merged_dependency_track_point(merge_track);

        assert!(
            !algo.install_native_role_assertion_edge(
                source,
                bridged.roles[0],
                bridged.nominal_seeds[1].individual_tag,
                merge_track,
                &mut ctx,
            ),
            "a multi-hop target merge was accepted without Konclude's combined merging hash"
        );
        assert!(
            algo.ht_role_successor_links(source, bridged.roles[0], &ctx)
                .is_empty(),
            "the failed-closed multi-hop assertion installed an under-justified edge"
        );
    }

    #[test]
    fn native_abox_role_handshake_does_not_propagate_late_peer_status() {
        use crate::frontend::syntax::Concept as C;

        let mut meta = native_nominal_meta(
            vec![
                ("a", "__nom__a", vec![]),
                (
                    "b",
                    "__nom__b",
                    vec![C::Or(
                        [C::Name("B".into()), C::Name("C".into())]
                            .into_iter()
                            .collect(),
                    )],
                ),
            ],
            vec![],
        );
        // a initializes first. The reverse face on a must wait for b; otherwise
        // b's later disjunction-insufficiency propagates through an initializing
        // backward link and contaminates a's representative association.
        meta.role_assertions.push(nominal_role("r", "b", "a"));
        let tin = TInput {
            concepts: vec![
                "A".into(),
                "B".into(),
                "C".into(),
                "__nom__a".into(),
                "__nom__b".into(),
            ],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            nominal_abox: meta,
            ..Default::default()
        };
        let (_algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let cache = bridged.native_representative_cache.borrow();
        let cache = cache.as_ref().expect("representative cache");
        let a = &cache.entries[&bridged.nominal_seeds[0].individual_tag];
        let b = &cache.entries[&bridged.nominal_seeds[1].individual_tag];
        assert!(
            !a.insufficient,
            "the earlier role target inherited its later peer's status"
        );
        assert!(
            b.insufficient,
            "the disjunctive peer must remain insufficient"
        );
    }

    #[test]
    fn native_abox_negative_role_assertion_is_exact_universal() {
        use crate::frontend::syntax::{Concept as C, Role as R};
        use crate::json_io::NominalRoleAssertionMeta;

        let mut meta = native_nominal_meta(
            vec![
                (
                    "a",
                    "__nom__a",
                    vec![C::Exists(
                        R::Name("r".into()),
                        Box::new(C::Nominal("b".into())),
                    )],
                ),
                ("b", "__nom__b", vec![]),
            ],
            vec![],
        );
        meta.negative_role_assertions
            .push(NominalRoleAssertionMeta {
                role: "r".into(),
                source: "a".into(),
                target: "b".into(),
            });
        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            nominal_abox: meta,
            ..Default::default()
        };
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("negative native role assertion must be decided");
        assert!(
            !result.consistent,
            "!R(a,b) must clash with a : exists R.{{b}}"
        );
    }

    #[test]
    fn native_abox_same_positive_and_negative_role_fact_clashes() {
        let mut meta = native_nominal_meta(
            vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
            vec![],
        );
        let fact = nominal_role("r", "a", "b");
        meta.role_assertions.push(fact.clone());
        meta.negative_role_assertions.push(fact);
        let tin = basic_native_role_input(&["r"], meta);
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("opposite assertions of the same role fact must be decided");
        assert!(
            !result.consistent,
            "R(a,b) and !R(a,b) must make the ontology inconsistent"
        );
    }

    #[test]
    fn native_abox_negative_role_fact_alone_has_empty_role_model() {
        let mut meta = native_nominal_meta(
            vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
            vec![],
        );
        meta.negative_role_assertions
            .push(nominal_role("r", "a", "b"));
        let tin = basic_native_role_input(&["r"], meta);
        let (_algo, _ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(
            empty_role_nominal_model_certificate(&tin, &bridged),
            "a negative role fact is true in the empty-role model"
        );
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("negative-only native role fact must be decided");
        assert!(result.consistent);
    }

    #[test]
    fn native_abox_positive_self_edge_is_not_dropped() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let mut meta = native_nominal_meta(
            vec![(
                "a",
                "__nom__a",
                vec![C::Forall(
                    R::Name("r".into()),
                    Box::new(C::Not(Box::new(C::Nominal("a".into())))),
                )],
            )],
            vec![],
        );
        meta.role_assertions.push(nominal_role("r", "a", "a"));
        let tin = basic_native_role_input(&["r"], meta);
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("native role self-edge must be decided");
        assert!(
            !result.consistent,
            "R(a,a) must clash with a : forall R.not {{a}}"
        );
    }

    #[test]
    fn native_abox_role_assertion_respects_inverse_roles() {
        use crate::frontend::syntax::{Concept as C, Role as R};
        use crate::json_io::NominalRoleAssertionMeta;

        let mut meta = native_nominal_meta(
            vec![
                ("a", "__nom__a", vec![]),
                (
                    "b",
                    "__nom__b",
                    vec![C::Forall(
                        R::Inverse("r".into()),
                        Box::new(C::Not(Box::new(C::Nominal("a".into())))),
                    )],
                ),
            ],
            vec![],
        );
        meta.role_assertions.push(NominalRoleAssertionMeta {
            role: "r".into(),
            source: "a".into(),
            target: "b".into(),
        });
        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            inverse: true,
            nominal_abox: meta,
            ..Default::default()
        };
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("inverse consequence of native role assertion must be decided");
        assert!(
            !result.consistent,
            "R(a,b) must clash with b : forall inverse(R).not {{a}}"
        );
    }

    #[test]
    fn native_abox_role_assertion_respects_role_supers() {
        use crate::frontend::syntax::Concept as C;
        use crate::json_io::NominalRoleAssertionMeta;

        let mut meta = native_nominal_meta(
            vec![("a", "__nom__a", vec![]), ("b", "__nom__b", vec![])],
            vec![],
        );
        meta.role_assertions.push(NominalRoleAssertionMeta {
            role: "r".into(),
            source: "a".into(),
            target: "b".into(),
        });
        meta.negative_role_assertions
            .push(NominalRoleAssertionMeta {
                role: "s".into(),
                source: "a".into(),
                target: "b".into(),
            });
        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into(), "__nom__b".into()],
            roles: vec!["r".into(), "s".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            clauses: vec![HtClause {
                body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
                head: vec![HAtom::Role { r: 1, s: 0, t: 1 }],
            }],
            nominal_abox: meta,
            ..Default::default()
        };
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("role-super consequence of native assertion must be decided");
        assert!(
            !result.consistent,
            "R(a,b), R subPropertyOf S, and !S(a,b) must clash"
        );
    }

    #[test]
    fn native_abox_role_assertion_respects_domain_and_range() {
        use crate::frontend::syntax::Concept as C;

        let make = |domain: bool| {
            let entries = if domain {
                vec![
                    ("a", "__nom__a", vec![C::Not(Box::new(C::Name("D".into())))]),
                    ("b", "__nom__b", vec![]),
                ]
            } else {
                vec![
                    ("a", "__nom__a", vec![]),
                    ("b", "__nom__b", vec![C::Not(Box::new(C::Name("E".into())))]),
                ]
            };
            let mut meta = native_nominal_meta(entries, vec![]);
            meta.role_assertions.push(nominal_role("r", "a", "b"));
            TInput {
                concepts: vec![
                    "A".into(),
                    "D".into(),
                    "E".into(),
                    "__nom__a".into(),
                    "__nom__b".into(),
                ],
                roles: vec!["r".into()],
                queries: vec![0],
                source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
                role_domains: domain.then_some((0, 1)).into_iter().collect(),
                role_ranges: (!domain).then_some((0, 2)).into_iter().collect(),
                nominal_abox: meta,
                ..Default::default()
            }
        };

        let domain = make(true);
        let result = bridged_classify_opts_with_trigger_absorption(&domain, false, false, true)
            .expect("role-domain consequence on native edge must be decided");
        assert!(
            !result.consistent,
            "R(a,b) and Domain(R,D) must clash with not D(a)"
        );

        let range = make(false);
        let result = bridged_classify_opts_with_trigger_absorption(&range, false, false, true)
            .expect("role-range consequence on native edge must be decided");
        assert!(
            !result.consistent,
            "R(a,b) and Range(R,E) must clash with not E(b)"
        );
    }

    #[test]
    fn native_abox_role_assertion_respects_role_chains() {
        let mut meta = native_nominal_meta(
            vec![
                ("a", "__nom__a", vec![]),
                ("b", "__nom__b", vec![]),
                ("c", "__nom__c", vec![]),
            ],
            vec![],
        );
        meta.role_assertions
            .extend([nominal_role("p", "a", "c"), nominal_role("q", "c", "b")]);
        meta.negative_role_assertions
            .push(nominal_role("r", "a", "b"));
        let mut tin = basic_native_role_input(&["p", "q", "r"], meta);
        tin.chains.push((0, 1, 2));
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("role-chain consequence of native edges must be decided");
        assert!(
            !result.consistent,
            "p(a,c), q(c,b), p o q subPropertyOf r, and !r(a,b) must clash"
        );
    }

    #[test]
    fn native_abox_role_assertion_respects_transitivity() {
        let mut meta = native_nominal_meta(
            vec![
                ("a", "__nom__a", vec![]),
                ("b", "__nom__b", vec![]),
                ("c", "__nom__c", vec![]),
            ],
            vec![],
        );
        meta.role_assertions
            .extend([nominal_role("r", "a", "b"), nominal_role("r", "b", "c")]);
        meta.negative_role_assertions
            .push(nominal_role("r", "a", "c"));
        let mut tin = basic_native_role_input(&["r"], meta);
        tin.transitive.push(0);
        let result = bridged_classify_opts_with_trigger_absorption(&tin, false, false, true)
            .expect("transitive consequence of native edges must be decided");
        assert!(
            !result.consistent,
            "r(a,b), r(b,c), Transitive(r), and !r(a,c) must clash"
        );
    }

    #[test]
    fn native_abox_nondeterministic_atmost_merge_completes_without_direct_blocking() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let mut meta = native_nominal_meta(
            vec![
                (
                    "a",
                    "__nom__a",
                    vec![C::AtMost(1, R::Name("r".into()), Box::new(C::Top))],
                ),
                ("b", "__nom__b", vec![]),
                ("c", "__nom__c", vec![]),
            ],
            vec![],
        );
        meta.role_assertions
            .extend([nominal_role("r", "a", "b"), nominal_role("r", "a", "c")]);
        let tin = basic_native_role_input(&["r"], meta);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        assert_eq!(
            precompute_native_representative_batches(&mut algo, &mut ctx, &bridged, true, 10,),
            Some(true)
        );
        let cache = bridged.native_representative_cache.borrow();
        let cache = cache.as_ref().expect("representative cache");
        let source_seed = &bridged.nominal_seeds[0];
        let source_entry = cache
            .entries
            .get(&source_seed.individual_tag)
            .expect("source representative association");
        assert!(native_cache_entry_covers_seed(source_entry, source_seed));
        for target in &bridged.nominal_seeds[1..] {
            assert!(
                source_entry
                    .neighbour_role_combinations
                    .iter()
                    .any(|combination| combination.neighbour_tag == target.individual_tag),
                "the merged neighbour alias disappeared from the role association"
            );
        }
        let alias_index = source_entry
            .neighbour_role_combinations
            .iter()
            .position(|combination| combination.merged_alias_deterministic == Some(false))
            .expect("one at-most merged alias must be nondeterministic");
        assert!(
            source_entry
                .neighbour_role_combinations
                .iter()
                .any(
                    |combination| combination.merged_alias_deterministic == Some(true)
                        && combination
                            .role_values
                            .as_ref()
                            .is_some_and(|values| values.iter().any(|value| value.deterministic))
                ),
            "the unmerged asserted neighbour lost its deterministic role value"
        );
        assert!(source_entry.neighbour_role_combinations[alias_index]
            .role_values
            .as_ref()
            .is_some_and(|values| values.iter().all(|value| !value.deterministic)));
        let mut falsely_deterministic_alias = source_entry.clone();
        for value in falsely_deterministic_alias.neighbour_role_combinations[alias_index]
            .role_values
            .as_mut()
            .expect("typed role values")
        {
            value.deterministic = true;
        }
        assert!(
            !native_cache_entry_covers_seed(&falsely_deterministic_alias, source_seed),
            "a nondeterministically merged neighbour alias was accepted as deterministic"
        );

        let nondeterministically_merged = cache
            .entries
            .values()
            .find(|entry| {
                entry
                    .nondeterministic_same_individuals
                    .as_ref()
                    .is_some_and(|individuals| individuals.len() > 1)
            })
            .expect("at-most model must serialize its nondeterministic merge");
        let mut expected_same: Vec<Cint64> = bridged.nominal_seeds[1..]
            .iter()
            .map(|seed| seed.individual_tag)
            .collect();
        expected_same.sort_unstable();
        assert_eq!(
            nondeterministically_merged
                .nondeterministic_same_individuals
                .as_ref(),
            Some(&expected_same)
        );
        assert!(
            nondeterministically_merged
                .deterministic_same_individuals
                .as_ref()
                .is_some_and(Vec::is_empty),
            "the at-most branch choice was promoted to deterministic equality"
        );
        assert!(nondeterministically_merged.complete_for_precomputation());
        assert!(
            nondeterministically_merged.reusable_for_full_completion(),
            "Konclude's production full-block gate accepts branch-local same-individual contents"
        );
    }

    #[test]
    fn native_abox_inferred_live_successor_is_serialized_separately_from_assertion_journal() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let meta = native_nominal_meta(
            vec![(
                "a",
                "__nom__a",
                vec![C::Exists(R::Name("r".into()), Box::new(C::Top))],
            )],
            vec![],
        );
        let tin = TInput {
            concepts: vec!["A".into(), "__nom__a".into()],
            roles: vec!["r".into()],
            queries: vec![0],
            source_axioms: vec![source_subclass(C::Name("A".into()), C::Top)],
            nominal_abox: meta,
            ..Default::default()
        };
        let (mut algo, mut ctx, bridged) = fresh_bridge_env_with_trigger_absorption(&tin, true);
        configure_production_search(&mut algo);
        assert_eq!(
            native_nominal_consistency(&mut algo, &mut ctx, &bridged),
            Some(true)
        );

        let seed = &bridged.nominal_seeds[0];
        assert!(
            seed.role_assertions.is_empty(),
            "the inferred edge was accidentally inserted into the assertion journal"
        );
        let original = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_data(-seed.individual_tag);
        let deterministic_node =
            native_completion_merge_target(&ctx, original, true).expect("deterministic root");
        let extraction_node =
            native_completion_merge_target(&ctx, deterministic_node, false).expect("model root");
        assert!(
            ctx.process_context()
                .node_successor_iterator(extraction_node)
                .has_next(),
            "the existential did not leave a live completion successor"
        );
        let (concept_values, _) =
            native_completion_label_values(&ctx, extraction_node, deterministic_node)
                .expect("completion label");
        let metadata = native_completion_role_metadata(
            &ctx,
            extraction_node,
            &concept_values,
            &bridged,
            seed,
        )
        .expect("live-successor role metadata");
        assert!(
            metadata
                .instantiated_role_values
                .iter()
                .any(|value| value.role == bridged.roles[0]
                    && !value.inversed
                    && value.deterministic),
            "the inferred-only live edge was not serialized"
        );
    }

    #[test]
    fn native_abox_atmost_respects_different_and_no_una() {
        use crate::frontend::syntax::{Concept as C, Role as R};

        let make = |different: bool, reverse: bool| {
            let mut meta = native_nominal_meta(
                vec![
                    (
                        "a",
                        "__nom__a",
                        vec![C::AtMost(1, R::Name("r".into()), Box::new(C::Top))],
                    ),
                    ("b", "__nom__b", vec![]),
                    ("c", "__nom__c", vec![]),
                ],
                if different { vec![("b", "c")] } else { vec![] },
            );
            meta.role_assertions
                .extend([nominal_role("r", "a", "b"), nominal_role("r", "a", "c")]);
            if reverse {
                meta.role_assertions.reverse();
            }
            basic_native_role_input(&["r"], meta)
        };

        let distinct = make(true, false);
        let result = bridged_classify_opts_with_trigger_absorption(&distinct, false, false, true)
            .expect("at-most plus explicit inequality must be decided");
        assert!(
            !result.consistent,
            "at-most 1 R, R(a,b), R(a,c), and b different c must clash"
        );

        let mergeable = make(false, false);
        let result = bridged_classify_opts_with_trigger_absorption(&mergeable, false, false, true)
            .expect("at-most without UNA must be decided");
        assert!(
            result.consistent,
            "without DifferentIndividuals, b and c may merge"
        );

        let reversed = make(false, true);
        let reversed_result =
            bridged_classify_opts_with_trigger_absorption(&reversed, false, false, true)
                .expect("reordered native assertions must be decided");
        assert_eq!(reversed_result.consistent, result.consistent);
        assert_eq!(reversed_result.unsatisfiable, result.unsatisfiable);
        assert_eq!(reversed_result.subsumptions, result.subsumptions);

        let (mut reused_algo, mut reused_ctx, reused_bridged) =
            fresh_bridge_env_with_trigger_absorption(&mergeable, true);
        configure_production_search(&mut reused_algo);
        let cold = native_nominal_consistency(&mut reused_algo, &mut reused_ctx, &reused_bridged);
        reset_probe_env(&mut reused_algo, &mut reused_ctx, &reused_bridged, false);
        configure_production_search(&mut reused_algo);
        let reset = native_nominal_consistency(&mut reused_algo, &mut reused_ctx, &reused_bridged);

        let (mut fresh_algo, mut fresh_ctx, fresh_bridged) =
            fresh_bridge_env_with_trigger_absorption(&mergeable, true);
        configure_production_search(&mut fresh_algo);
        let fresh = native_nominal_consistency(&mut fresh_algo, &mut fresh_ctx, &fresh_bridged);
        assert_eq!(cold, Some(true));
        assert_eq!(reset, cold, "reset/reused nominal state changed verdict");
        assert_eq!(fresh, cold, "fresh and reused environments disagree");
    }

    #[test]
    fn inverse_negative_existential_mirrors_defer_before_bridge_search() {
        use crate::frontend::syntax::{Concept, Role};

        let mirror_name = Concept::Name("N".into());
        let mirror_definition = Concept::Forall(
            Role::Name("hasPart".into()),
            Box::new(Concept::Not(Box::new(Concept::Name("F".into())))),
        );
        let mut unsafe_input = TInput {
            inverse: true,
            source_axioms: vec![source_equivalence(
                mirror_name.clone(),
                mirror_definition.clone(),
            )],
            ..TInput::default()
        };
        assert!(has_unhandled_inverse_negative_existential_mirror(
            &unsafe_input
        ));
        assert!(!bridge_input_guard(&unsafe_input));
        assert!(bridged_saturate(&unsafe_input).is_none());
        assert!(bridged_classify(&unsafe_input).is_none());
        assert!(bridged_classify_opts(&unsafe_input, false, false).is_none());

        // The source equivalence is symmetric, so either serialized operand
        // order must hit the same fail-closed gate.
        unsafe_input.source_axioms = vec![source_equivalence(mirror_definition, mirror_name)];
        assert!(has_unhandled_inverse_negative_existential_mirror(
            &unsafe_input
        ));

        // Without any representation of inverse-role feedback this particular
        // guard is not needed; the ordinary bridge fragment remains available.
        unsafe_input.inverse = false;
        assert!(!has_unhandled_inverse_negative_existential_mirror(
            &unsafe_input
        ));

        // cb_to_ht deliberately leaves `inverse=false` when inverse semantics
        // are carried by a swapped role bridge. Every public TInput entry point
        // must still defer before bridge construction or certificate reuse.
        unsafe_input.roles = vec!["hasPart".into(), "partOf".into()];
        unsafe_input.clauses = vec![HtClause {
            body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
            head: vec![HAtom::Role { r: 1, s: 1, t: 0 }],
        }];
        assert!(has_unhandled_inverse_negative_existential_mirror(
            &unsafe_input
        ));
        assert!(!bridge_input_guard(&unsafe_input));
        assert!(bridged_saturate(&unsafe_input).is_none());
        assert!(bridged_classify(&unsafe_input).is_none());
        assert!(bridged_classify_opts(&unsafe_input, false, false).is_none());

        // A source-level inverse role is the third independent feedback signal.
        unsafe_input.clauses.clear();
        unsafe_input.source_axioms = vec![source_equivalence(
            Concept::Name("NInv".into()),
            Concept::Forall(
                Role::Inverse("hasPart".into()),
                Box::new(Concept::Not(Box::new(Concept::Name("F".into())))),
            ),
        )];
        assert!(has_unhandled_inverse_negative_existential_mirror(
            &unsafe_input
        ));

        // A positive existential definition is not a complemented mirror.
        unsafe_input.inverse = true;
        unsafe_input.source_axioms = vec![source_equivalence(
            Concept::Name("P".into()),
            Concept::Exists(
                Role::Name("hasPart".into()),
                Box::new(Concept::Name("F".into())),
            ),
        )];
        assert!(!has_unhandled_inverse_negative_existential_mirror(
            &unsafe_input
        ));

        // N ≡ ¬∃R.⊤ normalises to N ≡ ∀R.⊥ and must also defer.
        unsafe_input.source_axioms = vec![source_equivalence(
            Concept::Name("NTop".into()),
            Concept::Forall(Role::Name("hasPart".into()), Box::new(Concept::Bottom)),
        )];
        assert!(has_unhandled_inverse_negative_existential_mirror(
            &unsafe_input
        ));
    }

    fn trigger_test_roles(b: &mut Builder) -> (RoleId, RoleId, HashMap<RoleId, RoleId>) {
        let role = b.ctx.ontology_arenas_mut().alloc_role(Role::new());
        let mut inverse_obj = Role::new();
        inverse_obj.set_inverse_role(role);
        let inverse = b.ctx.ontology_arenas_mut().alloc_role(inverse_obj);
        b.ctx
            .ontology_arenas_mut()
            .role_mut(role)
            .set_inverse_role(inverse);
        let map = HashMap::from([(role, inverse), (inverse, role)]);
        (role, inverse, map)
    }

    #[test]
    fn saturation_extractor_reports_only_valid_intermediate_substitute_concepts() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let queried = b.atom(TAG_BASE + 1);
        let reported = b.atom(TAG_BASE + 2);
        let negated = b.atom(TAG_BASE + 3);
        let role_range = b.atom(TAG_BASE + 4);
        let range_role = b.ctx.ontology_arenas_mut().alloc_role(Role::new());
        drop(b);

        let make_node = |ctx: &mut CalculationAlgorithmContextBase,
                         individual_id: Cint64,
                         concept: ConceptId,
                         negation: bool,
                         role: RoleId| {
            let mut item = ExtendedConceptReferenceLinkingData::new();
            item.init_concept_saturation_testing_item(concept, negation, role);
            let item = ctx
                .process_context_mut()
                .alloc_extended_con_ref_linking_data(item);
            let node = ctx
                .process_context_mut()
                .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
            ctx.process_context_mut()
                .sat_node_mut(node)
                .init_individual_saturation_process_node(individual_id, item, Id::NONE);
            node
        };

        // Konclude excludes the base node and the queried concept even when it
        // appears again on an intermediate substitute node.
        let base = make_node(&mut ctx, 1, reported, false, RoleId::NONE);
        let queried_again = make_node(&mut ctx, 2, queried, false, RoleId::NONE);
        let positive = make_node(&mut ctx, 3, reported, false, RoleId::NONE);
        let negative = make_node(&mut ctx, 4, negated, true, RoleId::NONE);
        let ranged = make_node(&mut ctx, 5, role_range, false, range_role);
        let terminal = make_node(&mut ctx, 6, role_range, false, RoleId::NONE);
        for (from, to) in [
            (base, queried_again),
            (queried_again, positive),
            (positive, negative),
            (negative, ranged),
            (ranged, terminal),
        ] {
            ctx.process_context_mut()
                .sat_node_mut(from)
                .set_substitute_individual_node(to);
        }

        let named_index = HashMap::from([
            (queried, 0usize),
            (reported, 1usize),
            (negated, 2usize),
            (role_range, 3usize),
        ]);
        let mut subsumers = Vec::new();
        let resolved =
            resolve_saturation_substitute_chain(&ctx, base, queried, &named_index, &mut subsumers);

        assert_eq!(resolved, terminal);
        assert_eq!(subsumers, vec![1]);
    }

    #[test]
    fn binary_absorber_combines_triggers_like_konclude() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let left = b.atom(TAG_BASE + 1);
        let right = b.atom(TAG_BASE + 2);
        let mut caches = TriggerCaches::default();
        let combined = combine_absorption_triggers(
            &mut b,
            vec![
                AbsorptionTrigger {
                    concept: left,
                    complexity: 1,
                },
                AbsorptionTrigger {
                    concept: right,
                    complexity: 1,
                },
            ],
            &mut caches,
        )
        .expect("binary trigger");
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(combined.concept)
                .get_operator_code(),
            op::CCIMPLTRIG
        );
        // Equal-complexity triggers follow CConceptTriggerLinker's decreasing
        // pointer order; the later arena id is the implication host.
        let right_concept = b.ctx.ontology_arenas().concept(right);
        assert_eq!(right_concept.get_operator_code(), op::CCSUB);
        let implication = right_concept.get_operand_list()[0].target;
        let implication_concept = b.ctx.ontology_arenas().concept(implication);
        assert_eq!(implication_concept.get_operator_code(), op::CCIMPL);
        assert_eq!(
            implication_concept.get_operand_list()[0].target,
            combined.concept
        );
        assert_eq!(implication_concept.get_operand_list()[1].target, left);
        assert!(implication_concept.get_operand_list()[1].negated);
    }

    #[test]
    fn nominal_absorption_trigger_is_asserted_on_named_individual() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let individual = b
            .ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(0));
        let nominal = b.atom(TAG_BASE + 1);
        b.ctx
            .ontology_arenas_mut()
            .concept_mut(nominal)
            .set_operator_code(op::CCNOMINAL)
            .set_nominal_individual(individual);

        let mut caches = TriggerCaches::default();
        let trigger =
            full_absorption_trigger(&mut b, (nominal, false), &HashMap::new(), &mut caches)
                .expect("positive nominal trigger");
        assert_eq!(trigger.complexity, 1);
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(trigger.concept)
                .get_operator_code(),
            op::CCIMPLTRIG
        );
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .individual(individual)
                .get_assertion_concept_linker(),
            &[ConceptAssertion {
                target: trigger.concept,
                negated: false,
            }]
        );

        let reused =
            full_absorption_trigger(&mut b, (nominal, false), &HashMap::new(), &mut caches)
                .expect("cached nominal trigger");
        assert_eq!(reused.concept, trigger.concept);
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .individual(individual)
                .get_assertion_concept_linker()
                .len(),
            1,
            "the cached trigger must not duplicate the ABox assertion"
        );
        assert!(
            full_absorption_trigger(&mut b, (nominal, true), &HashMap::new(), &mut caches)
                .is_none(),
            "Konclude's absorber supports only the positive nominal polarity"
        );
    }

    #[test]
    fn existential_trigger_uses_inverse_implall_propagation() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let filler = b.atom(TAG_BASE + 1);
        let (role, inverse, inverses) = trigger_test_roles(&mut b);
        let some = b.some(role, (filler, false));
        let trigger = full_absorption_trigger(
            &mut b,
            (some, false),
            &inverses,
            &mut TriggerCaches::default(),
        )
        .expect("existential trigger");
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(trigger.concept)
                .get_operator_code(),
            op::CCIMPLTRIG
        );
        let filler_concept = b.ctx.ontology_arenas().concept(filler);
        assert_eq!(filler_concept.get_operator_code(), op::CCSUB);
        let propagation = filler_concept.get_operand_list()[0].target;
        let propagation_concept = b.ctx.ontology_arenas().concept(propagation);
        assert_eq!(propagation_concept.get_operator_code(), op::CCIMPLALL);
        assert_eq!(propagation_concept.get_role(), inverse);
        assert_eq!(
            propagation_concept.get_operand_list()[0].target,
            trigger.concept
        );
    }

    #[test]
    fn full_gci_keeps_named_condition_on_final_implication() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let named_condition = b.atom(TAG_BASE + 1);
        let filler = b.atom(TAG_BASE + 2);
        let implied = b.atom(TAG_BASE + 3);
        let (role, _, inverses) = trigger_test_roles(&mut b);
        let existential = b.some(role, (filler, false));
        let conjunction = b.and_of(&[(named_condition, false), (existential, false)]);
        assert!(absorb_concept_disjunction(
            &mut b,
            &[conjunction],
            &[(implied, false)],
            &inverses,
            &mut TriggerCaches::default(),
        ));

        let filler_unfolding = b.ctx.ontology_arenas().concept(filler).get_operand_list()[0].target;
        let structural_trigger = b
            .ctx
            .ontology_arenas()
            .concept(filler_unfolding)
            .get_operand_list()[0]
            .target;
        let binary_implication = b
            .ctx
            .ontology_arenas()
            .concept(structural_trigger)
            .get_operand_list()[0]
            .target;
        let binary = b.ctx.ontology_arenas().concept(binary_implication);
        assert_eq!(binary.get_operator_code(), op::CCIMPL);
        assert_eq!(binary.get_operand_count(), 2);
        let combined_trigger = binary.get_operand_list()[0].target;
        assert_eq!(binary.get_operand_list()[1].target, named_condition);
        assert!(binary.get_operand_list()[1].negated);
        let combined = b.ctx.ontology_arenas().concept(combined_trigger);
        assert_eq!(combined.get_operator_code(), op::CCIMPLTRIG);
        assert_eq!(combined.get_operand_list()[0].target, implied);
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(named_condition)
                .get_operand_count(),
            0,
            "the weaker named condition must not host the implication"
        );
    }

    #[test]
    fn full_or_trigger_uses_konclude_rounded_average_complexity() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let atom = b.atom(TAG_BASE + 1);
        let filler = b.atom(TAG_BASE + 2);
        let (role, _, inverses) = trigger_test_roles(&mut b);
        let exists = b.some(role, (filler, false));
        let disjunction = b.or_of(&[(atom, false), (exists, false)]);
        let trigger = full_absorption_trigger(
            &mut b,
            disjunction,
            &inverses,
            &mut TriggerCaches::default(),
        )
        .expect("fully absorbable disjunction");
        assert_eq!(trigger.complexity, 2, "Konclude computes (1 + 2 + 1) / 2");
    }

    #[test]
    fn ore_3215_common_condition_does_not_host_reverse_definitions() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let common = b.atom(TAG_BASE + 1);
        let alternative = b.atom(TAG_BASE + 2);
        let filler = b.atom(TAG_BASE + 3);
        let implied = b.atom(TAG_BASE + 4);
        let (role, _, inverses) = trigger_test_roles(&mut b);
        let exists = b.some(role, (filler, false));
        let disjunction = b.or_of(&[(alternative, false), (exists, false)]);
        let definition = b.and_of(&[(common, false), disjunction]);
        assert!(absorb_concept_disjunction(
            &mut b,
            &[definition],
            &[(implied, false)],
            &inverses,
            &mut TriggerCaches::default(),
        ));
        assert_eq!(
            b.ctx.ontology_arenas().concept(common).get_operand_count(),
            0,
            "the stronger rounded-average OR trigger must host the binary chain"
        );
    }

    #[test]
    fn branch_trigger_preprocess_installs_role_domain_marker() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let filler = b.atom(TAG_BASE + 1);
        let alternative = b.atom(TAG_BASE + 2);
        let (role, _, _) = trigger_test_roles(&mut b);
        let all = b.all(role, (filler, false));
        b.or_of(&[(all, false), (alternative, false)]);

        let count = install_branch_role_domain_triggers(&mut b, &mut TriggerCaches::default());
        assert_eq!(count, 1);
        let marker = b.ctx.ontology_arenas().role(role).domain_linker[0].target;
        let marker = b.ctx.ontology_arenas().concept(marker);
        assert_eq!(marker.get_operator_code(), op::CCIMPLTRIG);
        assert_eq!(marker.get_operand_count(), 0);
    }

    #[test]
    fn higher_cardinality_uses_partial_not_full_trigger() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let filler = b.atom(TAG_BASE + 1);
        let (role, inverse, inverses) = trigger_test_roles(&mut b);
        let atmost = b.atmost_q(role, 2, (filler, false));
        let mut caches = TriggerCaches::default();
        assert!(full_absorption_trigger(&mut b, (atmost, true), &inverses, &mut caches).is_none());
        let trigger = partial_absorption_trigger(&mut b, (atmost, true), &inverses, &mut caches)
            .expect("partial cardinality trigger");
        let filler_concept = b.ctx.ontology_arenas().concept(filler);
        let propagation = filler_concept.get_operand_list()[0].target;
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(propagation)
                .get_operator_code(),
            op::CCIMPLALL
        );
        assert_eq!(
            b.ctx.ontology_arenas().concept(propagation).get_role(),
            inverse
        );
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(trigger.concept)
                .get_operator_code(),
            op::CCIMPLTRIG
        );
    }

    #[test]
    fn common_disjunct_preprocess_materializes_replacement_data() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let common = b.atom(TAG_BASE + 1);
        let left_only = b.atom(TAG_BASE + 2);
        let right_only = b.atom(TAG_BASE + 3);
        let left = b.and_of(&[(common, false), (left_only, false)]);
        let right = b.and_of(&[(common, false), (right_only, false)]);
        let disjunction = b.or_of(&[left, right]).0;
        drop(b);

        assert!(extract_common_disjunct_replacements(&mut ctx) >= 1);
        let process_data = Id::new(
            ctx.ontology_arenas()
                .concept(disjunction)
                .get_concept_data(),
        );
        let replacement = ctx
            .ontology_arenas()
            .concept_process_data(process_data)
            .get_replacement_data();
        assert!(replacement.is_some());
        assert!(ctx
            .ontology_arenas()
            .replacement_data(replacement)
            .common_disjunct_concepts
            .iter()
            .any(|link| link.target == common && !link.negated));
    }

    #[test]
    fn common_disjunct_preprocess_reuses_nested_disjunction_cache_exactly() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let common = b.atom(TAG_BASE + 1);
        let left_only = b.atom(TAG_BASE + 2);
        let right_only = b.atom(TAG_BASE + 3);
        let outer_only = b.atom(TAG_BASE + 4);
        let left = b.and_of(&[(common, false), (left_only, false)]);
        let right = b.and_of(&[(common, false), (right_only, false)]);
        let shared = b.or_of(&[left, right]);
        let outer_right = b.and_of(&[(common, false), (outer_only, false)]);
        let outer = b.or_of(&[shared, outer_right]).0;
        let shared = shared.0;
        drop(b);

        assert!(extract_common_disjunct_replacements(&mut ctx) >= 2);
        for disjunction in [shared, outer] {
            let process_data = Id::new(
                ctx.ontology_arenas()
                    .concept(disjunction)
                    .get_concept_data(),
            );
            let replacement = ctx
                .ontology_arenas()
                .concept_process_data(process_data)
                .get_replacement_data();
            assert!(replacement.is_some());
            let common_links = &ctx
                .ontology_arenas()
                .replacement_data(replacement)
                .common_disjunct_concepts;
            assert!(
                common_links
                    .iter()
                    .any(|link| link.target == common && !link.negated),
                "shared and cached outer disjunction both retain the common concept"
            );
        }
    }

    struct BridgeEnv {
        tin: crate::orchestrate::cb_to_ht::TInput,
        con_id: std::collections::HashMap<String, usize>,
        // populated by the most recent probe (kept for diagnostics)
        ctx: Option<CalculationAlgorithmContextBase>,
        unsupported: usize,
    }

    /// Same as [`bridge_ofn`] but reads the ontology from a file path.
    fn bridge_ofn_path(path: &str) -> BridgeEnv {
        let text = std::fs::read_to_string(path).expect("readable ontology");
        bridge_ofn(&text)
    }

    /// ofn → clauses → TInput (the future production route input).
    fn bridge_ofn(text: &str) -> BridgeEnv {
        let fr = crate::frontend::ofn_to_clauses(text).expect("in fragment");
        let named: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        let con_id = tin
            .concepts
            .iter()
            .enumerate()
            .map(|(i, n)| (n.clone(), i))
            .collect();
        BridgeEnv {
            tin,
            con_id,
            ctx: None,
            unsupported: 0,
        }
    }

    #[test]
    fn production_rbox_compiles_symmetric_role_as_self_inverse() {
        let env = bridge_ofn(
            "Prefix(:=<http://example.org/>)\n\
             Ontology(\n\
               Declaration(ObjectProperty(:r))\n\
               SymmetricObjectProperty(:r)\n\
             )",
        );
        assert!(env.tin.fenced.is_empty());
        assert!(env.tin.inverse);
    }

    #[test]
    fn production_rbox_marks_functional_role_for_successor_extension() {
        let env = bridge_ofn(
            "Prefix(:=<http://example.org/>)\n\
             Ontology(\n\
               Declaration(ObjectProperty(:r))\n\
               FunctionalObjectProperty(:r)\n\
             )",
        );
        let (_, ctx, bridged) = fresh_bridge_env(&env.tin);
        assert!(ctx.ontology_arenas().role(bridged.roles[0]).is_functional());
    }

    #[test]
    fn saturation_construction_ports_special_reference_and_exist_flags() {
        use super::super::model::concept_process::SATURATION_SUBSTITUTE_MODE;

        let env = bridge_ofn(
            "Prefix(:=<http://example.org/>)\n\
             Ontology(\n\
               Declaration(Class(:A)) Declaration(Class(:B))\n\
               Declaration(Class(:C)) Declaration(Class(:X))\n\
               Declaration(ObjectProperty(:r))\n\
               SubClassOf(:A :B)\n\
               SubClassOf(:X ObjectSomeValuesFrom(:r :C))\n\
             )",
        );
        let (_algo, mut ctx, mut bridged) = fresh_bridge_env(&env.tin);
        let a = bridged.named[env.con_id["A"]];
        let b = bridged.named[env.con_id["B"]];
        let c = bridged.named[env.con_id["C"]];
        let x = bridged.named[env.con_id["X"]];
        let r = bridged.roles[0];
        let next_tag = (0..ctx.ontology_arenas().concept_count())
            .map(|index| {
                ctx.ontology_arenas()
                    .concept(ConceptId::new(index))
                    .get_concept_tag()
            })
            .max()
            .unwrap_or(TAG_BASE)
            + 1;
        let (some, disjunction) = {
            let mut builder = Builder {
                ctx: &mut ctx,
                next_tag,
            };
            let some = builder.some(r, (c, false));
            let disjunction = builder.or_of(&[(a, false), (c, false)]).0;
            (some, disjunction)
        };
        // A is also a positive named disjunct. Konclude keeps A's ordinary
        // A -> B special reference in this case.
        bridged.tbox.push(disjunction);
        ctx.ontology_arenas_mut()
            .concept_mut(a)
            .set_operator_code(op::CCSUB)
            .set_operand_list(vec![super::super::model::NegLink {
                target: b,
                negated: false,
            }])
            .set_operand_count(1);
        ctx.ontology_arenas_mut()
            .concept_mut(x)
            .set_operator_code(op::CCSUB)
            .set_operand_list(vec![super::super::model::NegLink {
                target: some,
                negated: false,
            }])
            .set_operand_count(1);
        build_saturation_seeds(&mut ctx, &bridged);

        let item_for = |name: &str, ctx: &CalculationAlgorithmContextBase| {
            let named_index = env.con_id[name];
            let concept = bridged.named[named_index];
            let process_data = super::super::model::concept_process::ConceptProcessDataId::new(
                ctx.ontology_arenas().concept(concept).get_concept_data(),
            );
            let reference_data = ctx
                .ontology_arenas()
                .concept_process_data(process_data)
                .get_concept_reference_linking();
            ctx.ontology_arenas()
                .concept_saturation_reference_linking_data(reference_data)
                .get_concept_saturation_reference_linking_data(false)
        };
        let a_item = item_for("A", &ctx);
        let b_item = item_for("B", &ctx);
        let c_item = item_for("C", &ctx);
        let a_data = ctx
            .ontology_arenas()
            .saturation_concept_reference_linking(a_item);
        assert_eq!(a_data.get_special_item_reference(), b_item);
        assert_eq!(
            a_data.get_special_reference_mode(),
            SATURATION_SUBSTITUTE_MODE
        );
        let a_node = a_data.get_individual_process_node_for_concept();
        let b_node = ctx
            .ontology_arenas()
            .saturation_concept_reference_linking(b_item)
            .get_individual_process_node_for_concept();
        assert!(
            ctx.process_context().sat_node(b_node).get_individual_id()
                > ctx.process_context().sat_node(a_node).get_individual_id(),
            "Konclude's reversed construction list gives dependencies higher priority IDs"
        );
        assert!(!a_data.is_potentially_exist_initialization_concept());
        assert!(ctx
            .ontology_arenas()
            .saturation_concept_reference_linking(c_item)
            .is_potentially_exist_initialization_concept());
    }

    impl BridgeEnv {
        /// One probe = one fresh context + bridged terminology. Per-probe
        /// isolation: an UNSAT probe leaves clash-laden nodes + queued work
        /// behind, which would leak spurious clashes into the next probe.
        /// Konclude isolates probes via per-task databox COW (the unported
        /// Task layer); the v1 driver rebuilds instead — same verdicts,
        /// O(TBox) per probe.
        fn subsumes(&mut self, sub: &str, sup: &str) -> bool {
            self.try_subsumes(sub, sup)
                .unwrap_or_else(|| panic!("probe {sub} ⊑ {sup} raised STOP (undecided)"))
        }

        /// Like [`Self::subsumes`] but surfaces STOP/DEFER as `None` instead
        /// of panicking — for tests asserting "must not answer WRONG"
        /// (a defer is acceptable, a wrong verdict is not).
        fn try_subsumes(&mut self, sub: &str, sup: &str) -> Option<bool> {
            let mut algo = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo);
            let mut ctx = CalculationAlgorithmContextBase::new();
            ctx.base.used_concept_priority_strategy =
                Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
            let top = {
                let mut c = Concept::new();
                c.set_concept_tag(1);
                c.set_operator_code(op::CCTOP);
                ctx.ontology_arenas_mut().alloc_concept(c)
            };
            ctx.processing_data_box_mut().ontology_top_concept = top;
            let bridged = bridge_tinput(&mut ctx, &self.tin);
            algo.singleton_concepts = bridged.singleton_concepts.clone();
            self.unsupported = bridged.unsupported;
            let idx = |s: &str| -> usize {
                *self
                    .con_id
                    .get(s)
                    .unwrap_or_else(|| panic!("concept {s} not in TInput"))
            };
            let a = bridged.named[idx(sub)];
            let b = bridged.named[idx(sup)];
            let mut next_indi_id = 0i64;
            let r = bridged_unsat(
                &mut algo,
                &mut ctx,
                &bridged,
                &mut next_indi_id,
                &[(a, false), (b, true)],
            );
            self.ctx = Some(ctx);
            r
        }
    }

    const PREFIX: &str = "Prefix(:=<http://km.test/>)\nOntology(<http://km.test/o>\n";

    #[test]
    fn bridge_subsumption_chain() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             SubClassOf(:A :B)\n\
             SubClassOf(:B :C)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(env.subsumes("A", "B"), "A ⊑ B (direct)");
        assert_eq!(env.unsupported, 0, "chain TBox fully bridged");
        assert!(env.subsumes("A", "C"), "A ⊑ C (chained)");
        assert!(!env.subsumes("C", "A"), "C ⊑ A must NOT hold");
    }

    #[test]
    fn source_absorber_registers_unabsorbed_equivalent_non_candidate() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:H)) Declaration(Class(:M)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             EquivalentClasses(:H ObjectIntersectionOf(\
                 :M ObjectAllValuesFrom(:r :C)))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // `ofn_to_clauses` emits this side channel only when the production
        // environment enables trigger absorption. Supply the normalized axiom
        // directly so this unit test is independent of process-global env vars.
        env.tin.source_axioms = vec![crate::json_io::SourceAxiomMeta {
            kind: crate::json_io::SourceAxiomKind::Equivalent,
            left: SourceConcept::Name("H".into()),
            right: SourceConcept::And(std::collections::BTreeSet::from([
                SourceConcept::Name("M".into()),
                SourceConcept::Forall(
                    SourceRole::Name("r".into()),
                    Box::new(SourceConcept::Name("C".into())),
                ),
            ])),
        }];
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut top = Concept::new();
        top.set_concept_tag(1);
        top.set_operator_code(op::CCTOP);
        let top = ctx.ontology_arenas_mut().alloc_concept(top);
        ctx.processing_data_box_mut().ontology_top_concept = top;

        let bridged = bridge_tinput_with_trigger_absorption(&mut ctx, &env.tin, true);
        let host = bridged.named[*env.con_id.get("H").expect("H in TInput")];
        assert_eq!(
            ctx.ontology_arenas().concept(host).get_operator_code(),
            op::CCEQ,
            "the positive universal prevents full equivalence absorption"
        );
        assert!(
            ctx.ontology_arenas()
                .get_equivalent_concept_non_candidate_set()
                .expect("absorber creates Konclude's TBox set")
                .contains(&host),
            "the retained CCEQ host remains a classification possible-subsumer"
        );
    }

    #[test]
    fn source_tbox_retains_rbox_domain_for_existential_saturation() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |cc: usize, t: usize| HAtom::Concept {
            neg: false,
            c: cc,
            t,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "D".into(), "T".into(), "X".into()],
            roles: vec!["r".into()],
            clauses: vec![
                // Clausified copy of the source axiom. Source mode suppresses
                // this because the native source concept below replaces it.
                HtClause {
                    body: vec![c(0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 2,
                        t: 0,
                    }],
                },
                // Simple ObjectPropertyDomain(r D), emitted outside the source
                // class-axiom side channel and retained as a CRole linker.
                HtClause {
                    body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
                    head: vec![c(1, 0)],
                },
                // The same guarded shape can be generated from an ordinary
                // class axiom. It is not a native role domain without RBox
                // provenance and must stay suppressed in source mode.
                HtClause {
                    body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
                    head: vec![c(3, 0)],
                },
            ],
            role_domains: vec![(0, 1)],
            source_axioms: vec![crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::SubClass,
                left: SourceConcept::Name("A".into()),
                right: SourceConcept::Exists(
                    SourceRole::Name("r".into()),
                    Box::new(SourceConcept::Name("T".into())),
                ),
            }],
            ..Default::default()
        };

        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let mut top = Concept::new();
        top.set_concept_tag(1);
        top.set_operator_code(op::CCTOP);
        let top = ctx.ontology_arenas_mut().alloc_concept(top);
        ctx.processing_data_box_mut().ontology_top_concept = top;

        let bridged = bridge_tinput_with_trigger_absorption(&mut ctx, &tin, true);
        assert!(bridged.source_tbox);
        assert_eq!(bridged.unsupported, 0);
        assert!(
            ctx.ontology_arenas()
                .role(bridged.roles[0])
                .get_domain_concept_list()
                .iter()
                .any(|link| link.target == bridged.named[1] && !link.negated),
            "source mode must install D on r's native domain linker"
        );
        assert!(
            !ctx.ontology_arenas()
                .role(bridged.roles[0])
                .get_domain_concept_list()
                .iter()
                .any(|link| link.target == bridged.named[3]),
            "guarded clause shape alone must not manufacture a native domain"
        );

        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let out = extract_saturation_outcome(&mut ctx, &bridged);
        assert_eq!(out.sat_verdict[0], Some(false));
        assert!(
            out.certain_subsumers[0]
                .as_ref()
                .is_some_and(|subsumers| subsumers.contains(&1)),
            "A ⊆ ∃r.T and Domain(r,D) must saturate A ⊆ D"
        );
        assert!(
            !out.known_subsumers[0].contains(&3),
            "the non-RBox guarded clause must not saturate A ⊆ X"
        );
        assert!(
            out.label_certified(0),
            "a sufficient pure-TBox node keeps its label reusable as certified edges"
        );
    }

    /// Regression (ore_ont_9540, 18 spurious family-collapsing subsumptions):
    /// a saturation label may become an UNCONDITIONAL taxonomy edge or a
    /// probe-free trusted KPSet subsumer only when the extracting node is
    /// certified. Branch-dependent / native-ABox influenced nodes surface as
    /// insufficient or EQ-problematic — verdict unknown — and must fail the
    /// certification, while UNSAT-certain and sufficient SAT-certain labels
    /// remain consumable.
    #[test]
    fn saturation_label_certification_gates_unconditional_edges() {
        let outcome = SaturationOutcome {
            sat_verdict: vec![None, Some(false), Some(false), Some(true)],
            certain_subsumers: vec![None, Some(vec![2]), None, None],
            known_subsumers: vec![vec![1, 2], vec![2], vec![1], vec![0]],
        };
        // Insufficient/unprocessed (native-ABox influenced) node: unknown
        // verdict — its label carries individual/branch facts, NOT certified.
        assert!(!outcome.label_certified(0));
        // Sufficient node with the exact extracted set: certified.
        assert!(outcome.label_certified(1));
        // SAT-certain without an exact set is not a complete-label
        // certificate — fail closed.
        assert!(!outcome.label_certified(2));
        // UNSAT-certain subject: every pair is vacuously entailed.
        assert!(outcome.label_certified(3));
        // Out-of-range subjects fail closed.
        assert!(!outcome.label_certified(4));
    }

    #[test]
    fn source_tbox_propagates_complex_role_domain_back_through_chain() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |cc: usize, t: usize| HAtom::Concept {
            neg: false,
            c: cc,
            t,
        };
        let exists = |body: usize, role: usize, filler: usize| HtClause {
            body: vec![c(body, 0)],
            head: vec![HAtom::Exist {
                r: role,
                neg: false,
                c: filler,
                t: 0,
            }],
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into(), "D".into()],
            roles: vec!["r".into(), "s".into(), "t".into()],
            clauses: vec![
                // Clausified copies are suppressed in source mode.
                exists(0, 0, 1),
                exists(1, 1, 2),
                // ObjectPropertyDomain(t D) remains a native CRole linker.
                HtClause {
                    body: vec![HAtom::Role { r: 2, s: 0, t: 1 }],
                    head: vec![c(3, 0)],
                },
            ],
            chains: vec![(0, 1, 2)],
            role_domains: vec![(2, 3)],
            source_axioms: vec![
                crate::json_io::SourceAxiomMeta {
                    kind: crate::json_io::SourceAxiomKind::SubClass,
                    left: SourceConcept::Name("A".into()),
                    right: SourceConcept::Exists(
                        SourceRole::Name("r".into()),
                        Box::new(SourceConcept::Name("B".into())),
                    ),
                },
                crate::json_io::SourceAxiomMeta {
                    kind: crate::json_io::SourceAxiomKind::SubClass,
                    left: SourceConcept::Name("B".into()),
                    right: SourceConcept::Exists(
                        SourceRole::Name("s".into()),
                        Box::new(SourceConcept::Name("C".into())),
                    ),
                },
            ],
            ..Default::default()
        };

        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let mut top = Concept::new();
        top.set_concept_tag(1);
        top.set_operator_code(op::CCTOP);
        let top = ctx.ontology_arenas_mut().alloc_concept(top);
        ctx.processing_data_box_mut().ontology_top_concept = top;

        let bridged = bridge_tinput_with_trigger_absorption(&mut ctx, &tin, true);
        assert!(bridged.source_tbox);
        assert_eq!(bridged.unsupported, 0);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let out = extract_saturation_outcome(&mut ctx, &bridged);
        assert_eq!(out.sat_verdict[0], Some(false));
        assert!(
            out.certain_subsumers[0]
                .as_ref()
                .is_some_and(|subsumers| subsumers.contains(&3)),
            "A ⊑ ∃r.B, B ⊑ ∃s.C, r∘s ⊑ t, Domain(t,D) must saturate A ⊑ D"
        );
    }

    #[test]
    fn bridge_materializes_transitive_role_for_automata_preprocessing() {
        let mut tin = TInput {
            concepts: vec!["A".to_string()],
            roles: vec!["r".to_string()],
            ..TInput::default()
        };
        let role_index = 0;
        tin.transitive.push(role_index);
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut top = Concept::new();
        top.set_concept_tag(1);
        top.set_operator_code(op::CCTOP);
        let top = ctx.ontology_arenas_mut().alloc_concept(top);
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let bridged = bridge_tinput(&mut ctx, &tin);
        assert_eq!(bridged.unsupported, 0);
        assert_eq!(ctx.ontology_arenas().role_chain_count(), 2);
        assert!(ctx
            .ontology_arenas()
            .role(bridged.roles[role_index])
            .is_complex_role());
        let role = ctx.ontology_arenas().role(bridged.roles[role_index]);
        assert!(role
            .get_indirect_super_role_list()
            .iter()
            .any(|link| link.target == bridged.roles[role_index] && !link.negated));
        assert_eq!(role.get_role_chain_super_sharing_linker().len(), 1);
        assert!(ctx
            .ontology_arenas()
            .role(role.get_inverse_role())
            .is_complex_role());
    }

    #[test]
    fn structural_markers_are_not_classification_or_saturation_items() {
        let tin = TInput {
            concepts: vec!["A".to_string(), "Q_1".to_string()],
            queries: vec![0],
            ..TInput::default()
        };
        let (_algo, mut ctx, bridged) = fresh_bridge_env(&tin);
        assert!(ctx
            .ontology_arenas()
            .concept(bridged.named[0])
            .has_class_name());
        assert!(!ctx
            .ontology_arenas()
            .concept(bridged.named[1])
            .has_class_name());

        build_saturation_seeds(&mut ctx, &bridged);
        assert!(super::super::saturation::algorithm::SaturationTaskHandleAlgorithm::s07_concept_reference_node(
            bridged.named[0],
            false,
            &mut ctx,
        )
        .is_some());
        assert!(super::super::saturation::algorithm::SaturationTaskHandleAlgorithm::s07_concept_reference_node(
            bridged.named[1],
            false,
            &mut ctx,
        )
        .is_none());

        let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &[None, None],
            &[None, None],
            &[Vec::new(), Vec::new()],
            &[false, false],
            &[0],
            ctx.ontology_arenas().concepts(),
        );
        assert!(state.item_ids[0].is_some());
        assert!(state.item_ids[1].is_none());
        assert_eq!(state.ordered_subjects, vec![0]);
    }

    #[test]
    fn production_role_automata_solves_mini7914_unsat() {
        let mut env = bridge_ofn(include_str!(
            "../../../tests/completeness-gaps/mini7914_unsat.ofn"
        ));
        let hp = env
            .tin
            .roles
            .iter()
            .position(|role| role.rsplit(['#', '/']).next() == Some("hp"))
            .expect("hp in mini7914 role signature");
        assert!(
            env.tin.transitive.contains(&hp),
            "the frontend must retain Functional Syntax transitivity"
        );
        let x = *env.con_id.get("X").expect("X in mini7914 signature");
        let completion = bridged_classify_opts(&env.tin, false, false)
            .expect("mini7914 completion must classify without deferring");
        assert!(
            completion.unsatisfiable.contains(&x),
            "production role automata must make X unsatisfiable in completion"
        );
        let result = bridged_classify_opts(&env.tin, true, true)
            .expect("mini7914 must classify without deferring");
        assert!(
            result.unsatisfiable.contains(&x),
            "common consequences of both disjuncts must make X unsatisfiable"
        );
        assert!(
            result.subsumptions.iter().all(|(subject, _)| *subject != x),
            "unsatisfiable subjects are represented by #UNSAT, not redundant pairs"
        );
    }

    #[test]
    fn production_inverse_chain_automata_solves_7914_recognition_core() {
        let mut env = bridge_ofn(include_str!(
            "../../../tests/completeness-gaps/mini7914_chain_recognition.ofn"
        ));
        let r = env
            .tin
            .roles
            .iter()
            .position(|role| role.rsplit(['#', '/']).next() == Some("r"))
            .expect("r in recognition-core role signature");
        assert!(env.tin.transitive.contains(&r));
        assert_eq!(env.tin.chains.len(), 2);
        assert!(
            env.subsumes("X", "Target"),
            "inverse-trigger recognition must traverse forward and inverse chains"
        );
        let x = env.con_id["X"];
        let target = env.con_id["Target"];
        let saturation = bridged_saturate(&env.tin).expect("recognition core is bridge-supported");
        if std::env::var_os("KM_SAT_DEBUG").is_some() {
            let mut names: Vec<_> = env.con_id.iter().collect();
            names.sort_unstable_by_key(|(_, index)| **index);
            eprintln!(
                "MINI7914-SAT x={} target={} verdict={:?} known={:?} certain={:?} names={:?}",
                x,
                target,
                saturation.sat_verdict[x],
                saturation.known_subsumers[x],
                saturation.certain_subsumers[x],
                names
            );
        }
        assert_eq!(saturation.sat_verdict[x], Some(false));
        assert!(
            saturation.known_subsumers[x].contains(&target),
            "signed inverse-super links must carry AQ recognition back to X"
        );
        assert!(
            saturation.certain_subsumers[x]
                .as_ref()
                .is_some_and(|subsumers| subsumers.contains(&target)),
            "Konclude's extractor trusts the completed, sufficient automata label"
        );
    }

    #[test]
    fn production_read_off_populates_persistent_kpset_messages() {
        let ofn = format!(
            "{PREFIX}\\
             Declaration(Class(:A)) Declaration(Class(:B))\n\\
             SubClassOf(:A :B)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        configure_production_search(&mut algo);
        let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let n = bridged.named.len();
        let mut state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &vec![None; n],
            &vec![None; n],
            &vec![Vec::new(); n],
            &vec![false; n],
            &(0..n).collect::<Vec<_>>(),
            ctx.ontology_arenas().concepts(),
        );
        let a = env.con_id["A"];
        let b = env.con_id["B"];
        let mut next_id = 1_000;
        let (_, _, root) =
            bridged_classify_subject_with_root(&mut algo, &mut ctx, &bridged, &mut next_id, a, n)
                .expect("deterministic A read-off");
        analyse_kpset_completion_model(&mut classifier, &mut state, a, root, &mut ctx);

        let a_item = &state
            .ontology_item
            .get_concept_satisfiable_test_item_container()[state.item_ids[a].index()];
        assert!(a_item.has_subsumer_concept_item(state.item_ids[b]));
        assert!(a_item.is_class_pseudo_model_initalized());
    }

    #[test]
    fn production_read_off_keeps_open_or_disjuncts_nondeterministic() {
        let ofn = format!(
            "{PREFIX}\\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\\
             SubClassOf(:A ObjectUnionOf(:B :C))\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        configure_production_search(&mut algo);
        assert!(algo.conf_build_dependencies);
        assert!(
            !algo.conf_dependency_backjumping,
            "the production classifier builds dependencies independently of DDB"
        );
        let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let n = bridged.named.len();
        let mut state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &vec![None; n],
            &vec![None; n],
            &vec![Vec::new(); n],
            &vec![false; n],
            &(0..n).collect::<Vec<_>>(),
            ctx.ontology_arenas().concepts(),
        );
        let (a, b, c) = (env.con_id["A"], env.con_id["B"], env.con_id["C"]);
        let mut next_id = 1_000;
        let (_, authoritative, root) =
            bridged_classify_subject_with_root(&mut algo, &mut ctx, &bridged, &mut next_id, a, n)
                .expect("A has an open disjunctive model");
        assert!(
            !authoritative,
            "an opened OR branch is not a canonical model"
        );
        analyse_kpset_completion_model(&mut classifier, &mut state, a, root, &mut ctx);

        let a_item = &state
            .ontology_item
            .get_concept_satisfiable_test_item_container()[state.item_ids[a].index()];
        assert!(
            !a_item.has_subsumer_concept_item(state.item_ids[b])
                && !a_item.has_subsumer_concept_item(state.item_ids[c]),
            "a selected OR alternative must not be reported as a deterministic subsumer"
        );
        for candidate in [b, c] {
            assert!(
                !state
                    .candidate_state(a, candidate)
                    .is_some_and(|(confirmed, _)| confirmed),
                "an untested OR alternative must remain unconfirmed"
            );
        }
    }

    #[test]
    fn production_read_off_populates_other_node_possible_subsumptions() {
        let ofn = format!(
            "{PREFIX}\\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\\
             Declaration(ObjectProperty(:R))\n\\
             SubClassOf(:A ObjectSomeValuesFrom(:R :B))\n\\
             SubClassOf(:B :C)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        configure_production_search(&mut algo);
        let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let n = bridged.named.len();
        let mut state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &vec![None; n],
            &vec![None; n],
            &vec![Vec::new(); n],
            &vec![false; n],
            &(0..n).collect::<Vec<_>>(),
            ctx.ontology_arenas().concepts(),
        );
        let a = env.con_id["A"];
        let b = env.con_id["B"];
        let c = env.con_id["C"];
        let mut next_id = 1_000;
        let (_, _, root) =
            bridged_classify_subject_with_root(&mut algo, &mut ctx, &bridged, &mut next_id, a, n)
                .expect("deterministic A read-off");
        analyse_kpset_completion_model(&mut classifier, &mut state, a, root, &mut ctx);

        let b_item = &state
            .ontology_item
            .get_concept_satisfiable_test_item_container()[state.item_ids[b].index()];
        let possible = b_item
            .get_possible_subsumption_map_ref()
            .expect("the live other-node analyser initializes B's possible map");
        assert!(possible.contains(bridged.named[c]));
    }

    /// KM_HT_UNSATCACHE integration: the learned-nogood store survives
    /// `reset_probe_env` and never flips a verdict. Drives the SAME env
    /// lifecycle as `bridged_classify` (fresh env → probe → reset → probe)
    /// with the handler installed and the DDB+unsat-cache flags set
    /// programmatically (env-var-independent, so the test is meaningful in
    /// every suite mode). Asserts: (1) an UNSAT probe stays UNSAT when
    /// re-probed against the warm cache; (2) a SAT probe on overlapping
    /// vocabulary is NOT corrupted by cache entries learned from the UNSAT
    /// one (the critical soundness control — a nogood must only fire on a
    /// label that genuinely contains it).
    #[test]
    fn unsat_cache_warm_probes_keep_verdicts() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:X)) Declaration(Class(:Y))\n\
             Declaration(Class(:A1)) Declaration(Class(:A2))\n\
             Declaration(Class(:Z))\n\
             SubClassOf(:X ObjectUnionOf(:A1 :A2))\n\
             SubClassOf(:A1 :Y)\n\
             SubClassOf(:A2 :Y)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        assert_eq!(bridged.unsupported, 0, "fully bridged");
        install_bridge_unsat_cache(&mut ctx);
        let set_flags = |algo: &mut CompletionTaskHandleAlgorithm| {
            algo.conf_build_dependencies = true;
            algo.conf_dependency_backjumping = true;
            algo.conf_atomic_semantic_branching = true;
            algo.conf_write_unsat_caching = true;
            algo.conf_test_occur_unsat_cached = true;
        };
        set_flags(&mut algo);
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        let (x, y, z) = (
            bridged.named[idx("X")],
            bridged.named[idx("Y")],
            bridged.named[idx("Z")],
        );
        let mut id = 0i64;
        // Probe 1: X ⊓ ¬Y — UNSAT (X ⊑ Y through both disjuncts); the DDB
        // analysis may write nogoods into the shared cache here.
        let cold = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id,
            &[(x, false), (y, true)],
        );
        assert_eq!(cold, Some(true), "X ⊑ Y must hold (cold cache)");
        // Probe 2 (warm): the same seed re-probed after the classify-style
        // reset — the carried cache must reproduce the verdict.
        reset_probe_env(&mut algo, &mut ctx, &bridged, false);
        set_flags(&mut algo);
        let warm = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id,
            &[(x, false), (y, true)],
        );
        assert_eq!(warm, Some(true), "X ⊑ Y must hold (warm cache)");
        // Probe 3 (warm, SAT control): X ⊓ ¬Z is satisfiable — a nogood
        // learned from the ¬Y run must not fire on this overlapping label.
        reset_probe_env(&mut algo, &mut ctx, &bridged, false);
        set_flags(&mut algo);
        let sat = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id,
            &[(x, false), (z, true)],
        );
        assert_eq!(sat, Some(false), "X ⊑ Z must NOT hold (warm cache)");
        // The handler must still be installed after the resets (the carry).
        assert!(
            ctx.base.take_used_unsatisfiable_cache_handler().is_some(),
            "unsat-cache handler must survive reset_probe_env"
        );
    }

    /// Miniature of the ore_ont_12653 wrong-root-cancel (memory
    /// project_km_bridge_disjunction_probe cont-11): a TOP covering
    /// `⊤ ⊑ A ⊔ B` with A,B disjoint; `A ⊑ ≤2 r.E` kills the A-branch on X
    /// (X has three pairwise-disjoint E-successors); the B-branch adds three
    /// FRESH pairwise-disjoint E-successors, and X's `≤3 r.E` then forces a
    /// 6→3 CROSS-GROUP merge matching — which EXISTS (cross pairs are
    /// compatible), so **X is SATISFIABLE** (the B-branch model) and X ⊑ Y
    /// must NOT hold for an unrelated Y. The 12653 kernel bug: the u29
    /// all-siblings-refuted propagation reads the pairing deaths' remainders
    /// as deterministic-only and wrongly ROOT-CANCELS, declaring X unsat
    /// (⇒ X ⊑ everything). Run plain AND with
    /// `KM_HT_COW=1 KM_HT_DDB=1 KM_HT_DDB_REFUTED_DISCARD=1` (the fast
    /// path that reaches the propagation); both must pass once u29's
    /// before-proc-tag remainder is fixed. `#[ignore]` while env-driven.
    #[test]
    #[ignore]
    fn covering_atmost_cross_merge_sat() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:E))\n\
             Declaration(Class(:D1)) Declaration(Class(:D2)) Declaration(Class(:D3))\n\
             Declaration(Class(:E1)) Declaration(Class(:E2)) Declaration(Class(:E3))\n\
             Declaration(Class(:X)) Declaration(Class(:Y))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(owl:Thing ObjectUnionOf(:A :B))\n\
             DisjointClasses(:A :B)\n\
             SubClassOf(:A ObjectMaxCardinality(2 :r :E))\n\
             SubClassOf(:B ObjectIntersectionOf(ObjectSomeValuesFrom(:r :D1) \
             ObjectSomeValuesFrom(:r :D2) ObjectSomeValuesFrom(:r :D3)))\n\
             DisjointClasses(:D1 :D2 :D3)\n\
             SubClassOf(:D1 :E) SubClassOf(:D2 :E) SubClassOf(:D3 :E)\n\
             SubClassOf(:X ObjectIntersectionOf(ObjectSomeValuesFrom(:r :E1) \
             ObjectSomeValuesFrom(:r :E2) ObjectSomeValuesFrom(:r :E3) \
             ObjectMaxCardinality(3 :r :E)))\n\
             DisjointClasses(:E1 :E2 :E3)\n\
             SubClassOf(:E1 :E) SubClassOf(:E2 :E) SubClassOf(:E3 :E)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(
            !env.subsumes("X", "Y"),
            "X must be satisfiable (B-branch cross-merge model) — a spurious \
             X ⊑ Y means the search wrongly refuted every covering branch \
             (the u29 wrong-root-cancel in miniature)"
        );
    }

    /// ddmin-minimal ore_ont_12653 wrong-root-cancel oracle (the leftover
    /// poisoning defect): under an Or on a successor node, alternative 1
    /// fires the node's own ≥2-expansion (creates successor nodes), so the
    /// advance cannot restore the single-node label snapshot — alt-1's
    /// disjunct SURVIVES into alternative 2's world. Alt-2's ⊥-derivation
    /// then carries connection dependencies to BOTH alternatives' track
    /// points, the u29 all-siblings-refuted propagation reads the decision
    /// as fully refuted with root-level externals only, and ROOT-CANCELS ⇒
    /// spurious AlternativePath ⊑ PathOfLength2 (a Path with three elements
    /// is a countermodel). Fixed by gating the u29 analysis — not just the
    /// DDB stack walk — on `unrestored_advance_count == 0` (u02). Passes in
    /// plain mode by construction; the KM_HT_DDB=1 matrix leg is the
    /// regression proof.
    #[test]
    fn unrestored_advance_leftover_no_root_cancel() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:AlternativePath)) Declaration(Class(:Path))\n\
             Declaration(Class(:MainPath)) Declaration(Class(:PathElement))\n\
             Declaration(Class(:PathOfLength2))\n\
             Declaration(ObjectProperty(:hasPathElement))\n\
             SubClassOf(:AlternativePath :Path)\n\
             EquivalentClasses(:MainPath ObjectIntersectionOf(\
             ObjectComplementOf(:AlternativePath) :Path))\n\
             SubClassOf(:Path ObjectMinCardinality(2 :hasPathElement :PathElement))\n\
             DisjointClasses(:Path :PathElement)\n\
             EquivalentClasses(:PathOfLength2 ObjectExactCardinality(2 :hasPathElement :PathElement))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // Under the plain-mode multi-node completeness gate this probe's SAT
        // verdict becomes a DEFER (None) — acceptable. The regression this
        // test guards is the WRONG UNSAT (Some(true)) from the poisoned u29
        // analysis.
        assert_ne!(
            env.try_subsumes("AlternativePath", "PathOfLength2"),
            Some(true),
            "AlternativePath ⊑ PathOfLength2 must NOT hold (3-element Path \
             countermodel) — a spurious UNSAT here means the u29 analysis ran \
             on leftover-poisoned state after an unrestored advance"
        );
    }

    #[test]
    fn bridge_disjunction_by_cases() {
        // A ⊑ B ⊔ C, B ⊑ D, C ⊑ D ⇒ A ⊑ D — exercises the OR rule + the
        // sound same-node backtrack through the BRIDGED encoding.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             SubClassOf(:A ObjectUnionOf(:B :C))\n\
             SubClassOf(:B :D)\n\
             SubClassOf(:C :D)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(env.subsumes("A", "D"), "A ⊑ D by reasoning by cases");
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
    }

    #[test]
    fn bridge_disjunction_open_branch() {
        // Drop C ⊑ D: the C branch stays open ⇒ A ⊑ D must NOT hold (the
        // negative control that pinned the chronological-backtrack bug).
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             SubClassOf(:A ObjectUnionOf(:B :C))\n\
             SubClassOf(:B :D)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(
            !env.subsumes("A", "D"),
            "A ⊑ D must NOT hold (C branch open)"
        );
    }

    /// Dump every node's label tags (diagnostic, used on failure only).
    fn dump_nodes(env: &mut BridgeEnv, label: &str) {
        let ctx = env.ctx.as_mut().expect("a probe ran");
        let n = ctx.process_context().node_count();
        eprintln!("DBG {label}: {n} nodes");
        for i in 0..n {
            let node = super::super::process::NodeId::new(i as Cint64);
            let ls = ctx
                .process_context_mut()
                .node_reapply_concept_label_set(node);
            let mut tags: Vec<_> = ctx
                .process_context()
                .label_set(ls)
                .concept_des_dep_map
                .keys()
                .copied()
                .collect();
            tags.sort_unstable();
            eprintln!("DBG   node {i}: tags {tags:?}");
        }
    }

    #[test]
    fn bridge_exists_forall_clash() {
        // A ⊑ ∃R.B, A ⊑ ∀R.C, B ⊓ C ⊑ ⊥(via D/¬D)  ⇒ A unsatisfiable ⇒ A ⊑ E
        // for the probe; simpler direct check: A ⊑ ∃R.B and ∀R.¬B ⇒ A ⊓ that
        // ∀ is unsat. Encode as: A ⊑ ∃R.B, F ⊑ ∀R.C with B ⊓ C contradictory.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:R))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :B))\n\
             SubClassOf(:A ObjectAllValuesFrom(:R :C))\n\
             SubClassOf(:B ObjectComplementOf(:C))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // A forces an R-successor with B (∃), propagates C (∀), and B ⊑ ¬C
        // clashes on the successor ⇒ A is unsatisfiable ⇒ A ⊑ B holds
        // vacuously (any subsumption from an unsat concept).
        let holds = env.subsumes("A", "B");
        if !holds {
            dump_nodes(&mut env, "after A⊑B probe");
        }
        assert!(holds, "A unsat ⇒ A ⊑ B vacuously");
        let bc = env.subsumes("B", "C");
        if bc {
            // XXX-DBG: spurious unsat — show the TInput + the final graph
            for (i, n) in env.tin.concepts.iter().enumerate() {
                eprintln!("DBG concept {i} = {n}");
            }
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                }
            };
            for (i, cl) in env.tin.clauses.iter().enumerate() {
                let b: Vec<String> = cl.body.iter().map(show).collect();
                let h: Vec<String> = cl.head.iter().map(show).collect();
                eprintln!("DBG clause {i}: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            }
            dump_nodes(&mut env, "after B⊑C probe");
        }
        assert!(!bc, "B ⊑ C must NOT hold");
    }

    #[test]
    fn bridge_role_hierarchy_forall() {
        // R ⊑ S: A ⊑ ∃R.D, A ⊑ ∀S.C, D ⊑ ¬C — the ∀S restriction must reach
        // the R-successor via the hierarchy ⇒ A unsatisfiable. The bridged
        // counterpart of the `role_hierarchy_forall` selftest, driven from
        // real OWL through the indirect-super-role linkers pass.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:R)) Declaration(ObjectProperty(:S))\n\
             SubObjectPropertyOf(:R :S)\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :D))\n\
             SubClassOf(:A ObjectAllValuesFrom(:S :C))\n\
             SubClassOf(:D ObjectComplementOf(:C))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        let holds = env.subsumes("A", "D");
        if !holds {
            dump_nodes(&mut env, "after A⊑D probe (hierarchy)");
        }
        assert!(holds, "A unsat via R⊑S hierarchy ⇒ A ⊑ D vacuously");
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
    }

    /// Role DOMAIN through a forced successor (the ore_ont_9635 gap):
    /// `Domain(r, D)` + `A ⊑ ∃r.⊤` entails `A ⊑ D` DETERMINISTICALLY —
    /// the successor's existence fires the domain clause on the edge.
    /// The 9635 shape adds exact cardinality; test both.
    #[test]
    fn bridge_domain_via_forced_successor() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D)) Declaration(Class(:T))\n\
             Declaration(ObjectProperty(:r))\n\
             ObjectPropertyDomain(:r :D)\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :T))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(
            env.subsumes("A", "D"),
            "A ⊑ D via domain(r)=D and A's forced r-successor"
        );
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
        // the 9635 shape: exact cardinality forces the successor
        let ofn2 = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r))\n\
             ObjectPropertyDomain(:r :D)\n\
             SubClassOf(:A ObjectExactCardinality(1 :r))\n)"
        );
        let mut env2 = bridge_ofn(&ofn2);
        assert!(
            env2.subsumes("A", "D"),
            "A ⊑ D via domain(r)=D and A's =1 r-successor"
        );
    }

    /// The ore_ont_9635 completeness gap (ddmin, 294 → 2+2 axioms): the
    /// domain entailment `A ⊑ =1 r` + `Domain(r, D)` ⇒ `A ⊑ D` (covered
    /// bare by `bridge_domain_via_forced_successor`) MUST survive the
    /// presence of unrelated DataHasValue axioms — their value-identity
    /// clausification introduces singleton concepts, and the singleton
    /// path broke the pairwise probe (`unsat(A ⊓ ¬D)` found a spurious
    /// model: pairwise=false while readoff_has=true).
    #[test]
    fn bridge_domain_survives_datatype_singletons() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D)) Declaration(Class(:I))\n\
             Declaration(Class(:P)) Declaration(Class(:L)) Declaration(Class(:RL))\n\
             Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:h))\n\
             Declaration(DataProperty(:v))\n\
             SubClassOf(:A ObjectExactCardinality(1 :r))\n\
             ObjectPropertyDomain(:r :D)\n\
             EquivalentClasses(:P ObjectIntersectionOf(\
             DataHasValue(:v \"true\"^^xsd:boolean) :I))\n\
             EquivalentClasses(:L ObjectIntersectionOf(\
             ObjectAllValuesFrom(:h :P) :RL))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // The cross-branch wipe DETECTOR turns the previously-WRONG SAT
        // verdict into a DEFER (None) — acceptable: the production driver
        // then defers the subject and the caller falls back to a complete
        // arm. `Some(false)` (the wrong verdict) is the regression.
        let verdict = env.try_subsumes("A", "D");
        let holds = verdict == Some(true);
        if verdict == Some(false) {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => format!(
                        "{}{}({t})",
                        if *neg { "¬" } else { "" },
                        env.tin.concepts.get(*c).map(String::as_str).unwrap_or("?")
                    ),
                    HAtom::Role { r, s, t } => {
                        format!(
                            "{}({s},{t})",
                            env.tin.roles.get(*r).map(String::as_str).unwrap_or("?")
                        )
                    }
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => format!(
                        "∃{}.{}{}({t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?"),
                        if *neg { "¬" } else { "" },
                        env.tin.concepts.get(*c).map(String::as_str).unwrap_or("?")
                    ),
                }
            };
            for (i, cl) in env.tin.clauses.iter().enumerate() {
                let b: Vec<String> = cl.body.iter().map(show).collect();
                let h: Vec<String> = cl.head.iter().map(show).collect();
                eprintln!("DBG clause {i}: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            }
            for (i, n) in env.tin.concepts.iter().enumerate() {
                eprintln!("DBG concept idx {i} = tag {} = {n}", 10 + i);
            }
            for (i, n) in env.tin.roles.iter().enumerate() {
                eprintln!("DBG role idx {i} = arena-tag {} = {n}", 100 + i);
            }
            dump_nodes(&mut env, "after A⊑D probe (datatype singleton)");
        }
        assert_ne!(
            verdict,
            Some(false),
            "A ⊑ D holds (domain via forced successor): answering NOT-subsumed is unsound; \
             DEFER (None) is the acceptable degradation, deriving it the aspirational fix"
        );
        let _ = holds;
        assert_ne!(
            env.try_subsumes("D", "A"),
            Some(true),
            "D ⊑ A must NOT hold"
        );
    }

    #[test]
    fn bridge_exists_recognition_inverse() {
        // ∃R.B ⊑ Q (the definer-recognition / absorption shape, frontend-
        // clausified to `B(y) ∧ R(x,y) → Q(x)`, bridged as `B ⊑ ∀R⁻.Q`):
        // A ⊑ ∃R.B and Q ⊑ E ⊢ A ⊑ E — the Q lands on A through the
        // inverse-edge propagation, not through any forward unfold.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:Q)) Declaration(Class(:E))\n\
             Declaration(ObjectProperty(:R))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :B))\n\
             SubClassOf(ObjectSomeValuesFrom(:R :B) :Q)\n\
             SubClassOf(:Q :E)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        let holds = env.subsumes("A", "E");
        if !holds {
            dump_nodes(&mut env, "after A⊑E probe (recognition)");
        }
        assert!(
            holds,
            "A ⊑ E via ∃R.B ⊑ Q recognition over the inverse edge"
        );
        assert!(!env.subsumes("E", "A"), "E ⊑ A must NOT hold");
    }

    /// Scale smoke-test on a REAL ontology: bridge `KM_BRIDGE_ONT` and run
    /// satisfiability probes for the first `KM_BRIDGE_PROBES` (default 3)
    /// named non-internal concepts, timing each. Measures whether the ported
    /// engine + re-drive harness converge at real-TBox scale and what a probe
    /// costs — the data for the classify-driver design (per-task databox vs
    /// per-probe rebuild, reapply-queue priority). Diagnostic only.
    #[test]
    #[ignore]
    fn bridge_scale_probe() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let n_probes: usize = std::env::var("KM_BRIDGE_PROBES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3);
        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named_set,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        let subjects: Vec<usize> = tin
            .concepts
            .iter()
            .enumerate()
            .filter(|(_, n)| named_set.contains(*n))
            .map(|(i, _)| i)
            .take(n_probes)
            .collect();
        for &s in &subjects {
            let t0 = std::time::Instant::now();
            let mut algo = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo);
            let mut ctx = CalculationAlgorithmContextBase::new();
            ctx.base.used_concept_priority_strategy =
                Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
            let top = {
                let mut c = Concept::new();
                c.set_concept_tag(1);
                c.set_operator_code(op::CCTOP);
                ctx.ontology_arenas_mut().alloc_concept(c)
            };
            ctx.processing_data_box_mut().ontology_top_concept = top;
            let bridged = bridge_tinput(&mut ctx, &tin);
            let t_bridge = t0.elapsed();
            let t1 = std::time::Instant::now();
            let mut next = 0i64;
            let verdict = bridged_unsat(
                &mut algo,
                &mut ctx,
                &bridged,
                &mut next,
                &[(bridged.named[s], false)],
            );
            eprintln!(
                "BRIDGE-PROBE {}: verdict={:?} bridge={:.0}ms probe={:.0}ms nodes={} backtracks={} absorbed={} top={}",
                tin.concepts[s],
                verdict,
                t_bridge.as_secs_f64() * 1e3,
                t1.elapsed().as_secs_f64() * 1e3,
                ctx.process_context().node_count(),
                algo.or_backtrack_count,
                bridged.absorbed,
                bridged.top_attached,
            );
        }
    }

    /// Verdict CORRECTNESS on a REAL ontology vs a gold classification.
    /// `KM_BRIDGE_ONT` = the .owl; `KM_BRIDGE_GOLD` = the `km classify` JSON
    /// output (`{"consistent":..,"subsumptions":[[sub_iri,sup_iri],..]}`,
    /// the validated production path). Samples the first `KM_BRIDGE_PROBES`
    /// (default 20) named subjects; for each, checks EVERY gold super
    /// (bridge must report subsumption) and an equal number of gold
    /// NON-supers (bridge must NOT). Reports missing (incomplete) / spurious
    /// (unsound) counts. Diagnostic; asserts only that unsound==0 when the
    /// bridge is fully covered (`unsupported==0`), since a clash verdict is
    /// sound even under-approximated.
    #[test]
    #[ignore]
    fn bridge_correctness_sample() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let n_probes: usize = std::env::var("KM_BRIDGE_PROBES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(20);
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        // local name after '#' or last '/'.
        let local =
            |iri: &str| -> String { iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string() };
        // gold super-map: sub_local → set(sup_local); `gold_universe` = every
        // concept gold tracks (as sub or sup). Negatives are drawn ONLY from
        // this universe: cb_to_ht mints internal DEFINER concepts (Q_NNNN) that
        // are NOT named classes, so gold never lists them as supers — a subject
        // legitimately subsumed by an internal definer is correct, not unsound,
        // and must not be sampled as a negative.
        let mut supers: std::collections::HashMap<String, std::collections::HashSet<String>> =
            std::collections::HashMap::new();
        let mut gold_universe: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            supers.entry(sub).or_default().insert(sup);
        }

        let mut env = bridge_ofn_path(&path);
        // owned snapshot of the TInput concept names (avoids holding an
        // immutable borrow of env across the &mut env.subsumes() calls).
        let present: std::collections::HashSet<String> = env.con_id.keys().cloned().collect();
        // subjects: gold subjects that ARE present in the TInput (in-fragment).
        let mut subjects: Vec<String> = supers
            .keys()
            .filter(|s| present.contains(*s))
            .cloned()
            .collect();
        subjects.sort();
        subjects.truncate(n_probes);

        // deterministic "random" negatives: stride through the gold-known,
        // in-fragment concepts (excludes cb_to_ht internal definers).
        let mut all_concepts: Vec<String> = present
            .iter()
            .filter(|c| gold_universe.contains(*c))
            .cloned()
            .collect();
        all_concepts.sort();

        let mut missing = 0usize; // gold super the bridge did NOT derive (incomplete)
        let mut spurious = 0usize; // non-super the bridge DID derive (unsound)
        let mut checked_pos = 0usize;
        let mut checked_neg = 0usize;
        for sub in &subjects {
            let gold_sups = &supers[sub];
            for sup in gold_sups {
                if !present.contains(sup) || sup == sub {
                    continue;
                }
                checked_pos += 1;
                if !env.subsumes(sub, sup) {
                    missing += 1;
                    if missing <= 20 {
                        eprintln!("MISSING (incomplete): {sub} ⊑ {sup}");
                    }
                }
            }
            // negatives: same count of concepts NOT in the gold super-set.
            let want_neg = gold_sups.len().max(1);
            let mut got = 0usize;
            let step = (all_concepts.len() / want_neg.max(1)).max(1);
            let mut i = 0usize;
            while got < want_neg && i < all_concepts.len() {
                let cand = &all_concepts[i];
                i += step;
                if cand == sub || gold_sups.contains(cand) {
                    continue;
                }
                checked_neg += 1;
                got += 1;
                if env.subsumes(sub, cand) {
                    spurious += 1;
                    if spurious <= 20 {
                        eprintln!("SPURIOUS (unsound): {sub} ⊑ {cand}");
                    }
                }
            }
        }
        eprintln!(
            "BRIDGE-CORRECTNESS {path}: subjects={} pos_checked={} missing={} \
             neg_checked={} spurious={} unsupported={}",
            subjects.len(),
            checked_pos,
            missing,
            checked_neg,
            spurious,
            env.unsupported,
        );
        if env.unsupported == 0 {
            assert_eq!(spurious, 0, "clash verdicts must be sound");
        }
    }

    /// Compare the two subsumption oracles on ONE pair (`KM_BRIDGE_PAIR=
    /// "SubLocal,SupLocal"`): the pairwise probe (`subsumes`, seed A+¬B,
    /// re-drive with backtrack) vs the model read-off (`bridged_classify_
    /// subject`, saturate {A} and read the root label). Tells whether a
    /// read-off MISS is a read-off limitation (pairwise=true) or a real
    /// completion-incompleteness (both false). Diagnostic.
    #[test]
    #[ignore]
    fn bridge_probe_pair() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let pair = std::env::var("KM_BRIDGE_PAIR").expect("set KM_BRIDGE_PAIR=Sub,Sup");
        let (sub, sup) = pair.split_once(',').expect("Sub,Sup");
        let mut env = bridge_ofn_path(&path);
        // KM_BRIDGE_DUMP_NAMES: print the concept TAG of each listed name so a
        // numeric KM_BRIDGE_FIND_TAG follow-up can watch the chain.
        // KM_BRIDGE_DUMP_ROLE_SUPERS=<role-name>: print the bridged indirect
        // super-role list (as role TAGS: 100+i forward, 100+n_roles+i inverse)
        // for the named role — verifies the pass-1 hierarchy closure.
        if let Ok(rn) = std::env::var("KM_BRIDGE_DUMP_ROLE_SUPERS") {
            for (i, name) in env.tin.roles.iter().enumerate() {
                if name == &rn {
                    // rebuild a bridged env to inspect the arena role objects
                    let mut ctxr = CalculationAlgorithmContextBase::new();
                    let topr = {
                        let mut c = Concept::new();
                        c.set_concept_tag(1);
                        c.set_operator_code(op::CCTOP);
                        ctxr.ontology_arenas_mut().alloc_concept(c)
                    };
                    ctxr.processing_data_box_mut().ontology_top_concept = topr;
                    let br = bridge_tinput(&mut ctxr, &env.tin);
                    let robj = br.roles[i];
                    let sup_tags: Vec<Cint64> = ctxr
                        .ontology_arenas()
                        .role(robj)
                        .indirect_super_roles
                        .iter()
                        .map(|l| ctxr.ontology_arenas().role(l.target).get_role_tag())
                        .collect();
                    let n = env.tin.roles.len() as Cint64;
                    let named_sups: Vec<String> = sup_tags
                        .iter()
                        .map(|&t| {
                            let fwd = t - 100;
                            if fwd < n {
                                env.tin.roles[fwd as usize].clone()
                            } else {
                                format!("INV({})", env.tin.roles[(fwd - n) as usize])
                            }
                        })
                        .collect();
                    let complex: Vec<(Cint64, bool)> = std::iter::once(robj)
                        .chain(
                            ctxr.ontology_arenas()
                                .role(robj)
                                .indirect_super_roles
                                .iter()
                                .map(|link| link.target),
                        )
                        .map(|role| {
                            let r = ctxr.ontology_arenas().role(role);
                            (r.get_role_tag(), r.is_complex_role())
                        })
                        .collect();
                    eprintln!(
                        "ROLE-SUPERS {rn} (tag {}): {:?} complex={complex:?}",
                        100 + i,
                        named_sups
                    );
                }
            }
        }
        // KM_BRIDGE_TAG_NAMES=<tag>[,<tag>...]: reverse map concept TAGs to
        // TInput names (tag = TAG_BASE + index).
        if let Ok(tags) = std::env::var("KM_BRIDGE_TAG_NAMES") {
            for t in tags.split(',') {
                if let Ok(tag) = t.trim().parse::<i64>() {
                    let i = (tag - TAG_BASE) as usize;
                    if i < env.tin.concepts.len() {
                        eprintln!("TAG-NAME {}={}", tag, env.tin.concepts[i]);
                    }
                }
            }
        }
        // KM_BRIDGE_GREP_CLAUSES=<c:IDX|r:IDX>[,...]: print every TInput
        // clause mentioning any listed concept (c:) or role (r:) index,
        // with concept names resolved — the clause-level entailment-check
        // input (the UNSUP-dumper format).
        if let Ok(spec) = std::env::var("KM_BRIDGE_GREP_CLAUSES") {
            let mut cons: Vec<usize> = Vec::new();
            let mut rols: Vec<usize> = Vec::new();
            for part in spec.split(',') {
                let part = part.trim();
                if let Some(i) = part.strip_prefix("c:").and_then(|s| s.parse().ok()) {
                    cons.push(i);
                } else if let Some(i) = part.strip_prefix("r:").and_then(|s| s.parse().ok()) {
                    rols.push(i);
                }
            }
            let name =
                |c: usize| -> &str { env.tin.concepts.get(c).map(String::as_str).unwrap_or("?") };
            let show = |a: &crate::orchestrate::cb_to_ht::HAtom| -> String {
                use crate::orchestrate::cb_to_ht::HAtom;
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                    HAtom::Role { r, s, t } => format!(
                        "{}({s},{t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?")
                    ),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => format!(
                        "∃{}.{}{}({t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?"),
                        if *neg { "¬" } else { "" },
                        name(*c)
                    ),
                }
            };
            for cl in &env.tin.clauses {
                use crate::orchestrate::cb_to_ht::HAtom;
                let hit = cl.body.iter().chain(cl.head.iter()).any(|a| match a {
                    HAtom::Concept { c, .. } | HAtom::Exist { c, .. } => cons.contains(c),
                    HAtom::Role { r, .. } => rols.contains(r),
                    HAtom::Eq { .. } => false,
                }) || cl.body.iter().chain(cl.head.iter()).any(|a| match a {
                    HAtom::Exist { r, .. } => rols.contains(r),
                    _ => false,
                });
                if hit {
                    let b: Vec<String> = cl.body.iter().map(show).collect();
                    let h: Vec<String> = cl.head.iter().map(show).collect();
                    eprintln!("CLAUSE: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
                }
            }
        }
        // KM_BRIDGE_ROLE_NAMES=<idx>[,<idx>...]: print TInput role names.
        if let Ok(idxs) = std::env::var("KM_BRIDGE_ROLE_NAMES") {
            for i in idxs.split(',') {
                if let Ok(i) = i.trim().parse::<usize>() {
                    if i < env.tin.roles.len() {
                        eprintln!("ROLE-NAME {}={}", i, env.tin.roles[i]);
                    }
                }
            }
        }
        if let Ok(names) = std::env::var("KM_BRIDGE_DUMP_NAMES") {
            for n in names.split(',') {
                if let Some(&idx) = env.con_id.get(n.trim()) {
                    eprintln!("NAME-TAG {}={}", n.trim(), TAG_BASE + idx as Cint64);
                }
            }
        }
        let pairwise = env.subsumes(sub, sup);

        // read-off on the same subject
        let n_named = env.tin.concepts.len();
        let s_idx = *env.con_id.get(sub).expect("sub in TInput");
        let sup_idx = *env.con_id.get(sup).expect("sup in TInput");
        let mut algo = CompletionTaskHandleAlgorithm::new();
        configure_default_blocking(&mut algo);
        if std::env::var_os("KM_HT_BUILD_DEPENDENCIES").is_some() {
            algo.conf_build_dependencies = true;
        }
        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let top = {
            let mut c = Concept::new();
            c.set_concept_tag(1);
            c.set_operator_code(op::CCTOP);
            ctx.ontology_arenas_mut().alloc_concept(c)
        };
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let bridged = bridge_tinput(&mut ctx, &env.tin);
        if let Ok(spec) = std::env::var("KM_BRIDGE_DUMP_CONCEPT_TAGS") {
            let wanted: BTreeSet<Cint64> = spec
                .split(',')
                .filter_map(|s| s.trim().parse().ok())
                .collect();
            for i in 0..ctx.ontology_arenas().concept_count() {
                let concept = ConceptId::new(i);
                let c = ctx.ontology_arenas().concept(concept);
                let tag = c.get_concept_tag();
                if !wanted.contains(&tag) {
                    continue;
                }
                let role = c.get_role();
                let role_tag = role
                    .is_some()
                    .then(|| ctx.ontology_arenas().role(role).get_role_tag());
                let operands: Vec<String> = c
                    .get_operand_list()
                    .iter()
                    .map(|link| {
                        format!(
                            "{}{}",
                            if link.negated { "not " } else { "" },
                            ctx.ontology_arenas().concept(link.target).get_concept_tag()
                        )
                    })
                    .collect();
                eprintln!(
                    "CONCEPT-TAG tag={tag} op={} role={role_tag:?} operands=[{}]",
                    c.get_operator_code(),
                    operands.join(" ")
                );
            }
        }
        let mut next = 0i64;
        let readoff =
            bridged_classify_subject(&mut algo, &mut ctx, &bridged, &mut next, s_idx, n_named);
        let readoff_has = readoff
            .as_ref()
            .map(|(subs, _)| subs.contains(&sup_idx))
            .unwrap_or(false);
        eprintln!(
            "BRIDGE-PAIR {sub} ⊑ {sup}: pairwise={pairwise} readoff_has={readoff_has} \
             readoff_nondet={}",
            !readoff.as_ref().map(|(_, auth)| *auth).unwrap_or(false),
        );
        if std::env::var_os("KM_BRIDGE_PROD_PAIR").is_some() {
            let production = bridged_classify(&env.tin).expect("production classification");
            let production_has = production.subsumptions.contains(&(s_idx, sup_idx));
            eprintln!("BRIDGE-PRODUCTION-PAIR {sub} ⊑ {sup}: production_has={production_has}");
            assert!(
                production_has,
                "Konclude's post-satisfiability possible-subsumption map must be tested"
            );
        }
        // dump every clause referencing sub or sup (to scope the propagation
        // the completion is missing).
        if std::env::var("KM_BRIDGE_DUMP_CLAUSES").is_ok() {
            let name = |i: usize| env.tin.concepts[i].as_str();
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                }
            };
            let mentions = |cl: &HtClause, idx: usize| -> bool {
                cl.body.iter().chain(cl.head.iter()).any(|a| {
                    matches!(a,
                    HAtom::Concept { c, .. } | HAtom::Exist { c, .. } if *c == idx)
                })
            };
            // extra names to trace (KM_BRIDGE_DUMP_NAMES="Q_708,Q_266").
            let extra_idx: Vec<usize> = std::env::var("KM_BRIDGE_DUMP_NAMES")
                .ok()
                .map(|s| {
                    s.split(',')
                        .filter_map(|n| env.con_id.get(n.trim()).copied())
                        .collect()
                })
                .unwrap_or_default();
            for cl in &env.tin.clauses {
                if mentions(cl, s_idx)
                    || mentions(cl, sup_idx)
                    || extra_idx.iter().any(|&i| mentions(cl, i))
                {
                    let b: Vec<String> = cl.body.iter().map(show).collect();
                    let h: Vec<String> = cl.head.iter().map(show).collect();
                    eprintln!("  CLAUSE: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
                }
            }
        }
    }

    /// FULL model-read-off classification vs gold: saturate every named
    /// subject ONCE (`bridged_classify_subject`) and read its subsumers off
    /// the root label — O(concepts) saturations, the feasible classification
    /// path (naive pairwise on 1016 = ~2500² probes). Compares the WHOLE
    /// derived named-subsumption relation to the `km classify` gold
    /// (`KM_BRIDGE_GOLD`), reporting missing (incomplete) / spurious
    /// (unsound) / non-deterministic-subject counts. Diagnostic.
    #[test]
    #[ignore]
    fn bridge_classify_full() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        let local =
            |iri: &str| -> String { iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string() };
        let mut gold_pairs: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut gold_universe: std::collections::HashSet<String> = std::collections::HashSet::new();
        // Names appearing as a SUB in gold: only these become subjects, so a
        // gold file restricted to a subject sample stays self-consistent —
        // every admitted subject carries its COMPLETE supers set, keeping
        // `spurious` meaningful (a supers-only name would otherwise be
        // classified against an empty gold row and misread as unsound).
        let mut gold_subs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            gold_subs.insert(sub.clone());
            gold_pairs.insert((sub, sup));
        }

        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named_set,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        let n_named = tin.concepts.len();

        let mut algo = CompletionTaskHandleAlgorithm::new();
        configure_default_blocking(&mut algo);
        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let top = {
            let mut c = Concept::new();
            c.set_concept_tag(1);
            c.set_operator_code(op::CCTOP);
            ctx.ontology_arenas_mut().alloc_concept(c)
        };
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let bridged = bridge_tinput(&mut ctx, &tin);

        // subjects = gold-classified (sub-side), in-fragment named concepts.
        let mut subjects: Vec<usize> = (0..n_named)
            .filter(|&i| gold_subs.contains(&tin.concepts[i]))
            .collect();
        // KM_BRIDGE_MAX_SUBJECTS=N: validate a bounded prefix of subjects
        // (correctness sample on deep taxonomies where full O(subjects)
        // classification without databox reuse is a separate speed lever).
        // When set, gold is restricted to these subjects so missing/spurious
        // stay meaningful on the sample.
        if let Some(cap) = std::env::var("KM_BRIDGE_MAX_SUBJECTS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
        {
            subjects.truncate(cap);
        }
        // pairwise-fallback COLUMNS: every gold-known named concept (a super
        // like `Path` need not be a classified subject itself).
        let targets: Vec<usize> = (0..n_named)
            .filter(|&i| gold_universe.contains(&tin.concepts[i]))
            .collect();

        let mut derived: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut nondet = 0usize;
        let mut next = 0i64;
        let t0 = std::time::Instant::now();
        for &s in &subjects {
            // fresh ctx per subject (per-probe isolation; the databox-COW
            // reuse is the next wave). Rebuild is O(TBox).
            let mut algo2 = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo2);
            let mut ctx2 = CalculationAlgorithmContextBase::new();
            ctx2.base.used_concept_priority_strategy =
                Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
            let top2 = {
                let mut c = Concept::new();
                c.set_concept_tag(1);
                c.set_operator_code(op::CCTOP);
                ctx2.ontology_arenas_mut().alloc_concept(c)
            };
            ctx2.processing_data_box_mut().ontology_top_concept = top2;
            let bridged2 = bridge_tinput(&mut ctx2, &tin);
            // thread the singleton (value-identity) concepts — WITHOUT them
            // the kernel under-merges value nodes and unsat proofs that need
            // the merges cannot close (measured: PathOfLength3 ⊑ Path
            // converged in the probe harness, which threads them, but burned
            // its whole budget in this loop, which did not).
            algo2.singleton_concepts = bridged2.singleton_concepts.clone();
            let mut n2 = 0i64;
            let t_subj = std::time::Instant::now();
            let verdict =
                bridged_classify_subject(&mut algo2, &mut ctx2, &bridged2, &mut n2, s, n_named);
            eprintln!(
                "SUBJ {} {}: {} in {:.1}s (nodes={} backtracks={})",
                s,
                tin.concepts[s],
                match &verdict {
                    Some((v, true)) => format!("readoff {} supers", v.len()),
                    Some((v, false)) => format!("NONDET {} candidates", v.len()),
                    None => "STOP".into(),
                },
                t_subj.elapsed().as_secs_f64(),
                ctx2.process_context().node_count(),
                algo2.or_backtrack_count,
            );
            match verdict {
                Some((subs, true)) => {
                    for sup in subs {
                        if sup == s {
                            continue;
                        }
                        // only named-vs-named, gold-known targets
                        if gold_universe.contains(&tin.concepts[sup]) {
                            derived.insert((tin.concepts[s].clone(), tin.concepts[sup].clone()));
                        }
                    }
                }
                Some((cands, false)) => {
                    // Non-deterministic saturation: the one-model read-off is
                    // not authoritative — its positives are the CANDIDATE
                    // subsumers (Konclude's possible-subsumer extraction).
                    // Verify each with a pairwise probe: `unsat(s ⊓ ¬sup)`
                    // proves `s ⊑ sup` under ANY branch discipline. On a
                    // small gold universe, probe every target instead (the
                    // candidate label can under-approximate; the pairwise
                    // verdict itself is exact either way).
                    nondet += 1;
                    let cand_list: Vec<usize> = if targets.len() <= 64 {
                        targets.clone()
                    } else {
                        cands
                    };
                    for sup in cand_list {
                        if sup == s || !gold_universe.contains(&tin.concepts[sup]) {
                            continue;
                        }
                        let tp0 = std::time::Instant::now();
                        if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                            eprintln!("PAIR-START {} vs {}", tin.concepts[s], tin.concepts[sup]);
                        }
                        let mut algo3 = CompletionTaskHandleAlgorithm::new();
                        configure_default_blocking(&mut algo3);
                        let mut ctx3 = CalculationAlgorithmContextBase::new();
                        ctx3.base.used_concept_priority_strategy =
                            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
                        let top3 = {
                            let mut c = Concept::new();
                            c.set_concept_tag(1);
                            c.set_operator_code(op::CCTOP);
                            ctx3.ontology_arenas_mut().alloc_concept(c)
                        };
                        ctx3.processing_data_box_mut().ontology_top_concept = top3;
                        let bridged3 = bridge_tinput(&mut ctx3, &tin);
                        // value-identity singletons (see the subject loop).
                        algo3.singleton_concepts = bridged3.singleton_concepts.clone();
                        let mut n3 = 0i64;
                        if bridged_unsat(
                            &mut algo3,
                            &mut ctx3,
                            &bridged3,
                            &mut n3,
                            &[(bridged3.named[s], false), (bridged3.named[sup], true)],
                        ) == Some(true)
                        {
                            derived.insert((tin.concepts[s].clone(), tin.concepts[sup].clone()));
                        }
                        // Surface slow pair probes (the read-offs are ms; a
                        // probe that takes seconds is the scaling story).
                        let dt = tp0.elapsed();
                        if dt.as_millis() > 500 {
                            eprintln!(
                                "SLOW-PAIR {} vs {}: {:.1}s (backtracks={})",
                                tin.concepts[s],
                                tin.concepts[sup],
                                dt.as_secs_f64(),
                                algo3.or_backtrack_count,
                            );
                        }
                    }
                }
                None => nondet += 1, // STOP: no verdict at all
            }
        }
        let elapsed = t0.elapsed();
        let _ = (&algo, &bridged, &mut next);

        // restrict gold to the same subject/target universe we classified.
        let subj_names: std::collections::HashSet<String> =
            subjects.iter().map(|&i| tin.concepts[i].clone()).collect();
        let gold_restricted: std::collections::HashSet<(String, String)> = gold_pairs
            .iter()
            .filter(|(sub, sup)| subj_names.contains(sub) && gold_universe.contains(sup))
            .cloned()
            .collect();
        let missing: Vec<_> = gold_restricted.difference(&derived).take(20).collect();
        let spurious: Vec<_> = derived.difference(&gold_restricted).take(20).collect();
        for m in &missing {
            eprintln!("MISSING (incomplete): {} ⊑ {}", m.0, m.1);
        }
        for sp in &spurious {
            eprintln!("SPURIOUS (unsound): {} ⊑ {}", sp.0, sp.1);
        }
        eprintln!(
            "BRIDGE-CLASSIFY {path}: subjects={} nondet={} derived={} gold={} \
             missing={} spurious={} elapsed={:.1}s unsupported={}",
            subjects.len(),
            nondet,
            derived.len(),
            gold_restricted.len(),
            gold_restricted.difference(&derived).count(),
            derived.difference(&gold_restricted).count(),
            elapsed.as_secs_f64(),
            bridged.unsupported,
        );
    }

    /// PRODUCTION-PATH gold driver: run the shipped entry point
    /// `bridged_classify` (single reused env, production DDB search,
    /// per-subject defer + budget-escalating retry rounds) on
    /// `KM_BRIDGE_ONT` and diff the result against `KM_BRIDGE_GOLD` —
    /// the same gold format as `bridge_classify_full`, which by contrast
    /// drives the subject/probe layers directly with fresh envs. Restrict
    /// subjects via `queries` when `KM_BRIDGE_MAX_SUBJECTS` is set.
    #[test]
    #[ignore]
    fn bridge_classify_prod() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        let local =
            |iri: &str| -> String { iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string() };
        let mut gold_pairs: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut gold_universe: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut gold_subs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            gold_subs.insert(sub.clone());
            gold_pairs.insert((sub, sup));
        }

        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let mut tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named_set,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        // subjects = gold-classified (sub-side) names, optionally capped —
        // expressed through the production `queries` mechanism.
        let mut subjects: Vec<usize> = (0..tin.concepts.len())
            .filter(|&i| gold_subs.contains(&tin.concepts[i]))
            .collect();
        if let Some(cap) = std::env::var("KM_BRIDGE_MAX_SUBJECTS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
        {
            subjects.truncate(cap);
        }
        let subj_names: std::collections::HashSet<String> =
            subjects.iter().map(|&i| tin.concepts[i].clone()).collect();
        tin.queries = subjects.clone();

        let t0 = std::time::Instant::now();
        let res = bridged_classify(&tin);
        let elapsed = t0.elapsed();
        let Some(r) = res else {
            eprintln!(
                "BRIDGE-CLASSIFY-PROD {path}: DEFERRED after {:.1}s",
                elapsed.as_secs_f64()
            );
            return;
        };
        let mut derived: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        for &(a, b) in &r.subsumptions {
            let (sub, sup) = (tin.concepts[a].clone(), tin.concepts[b].clone());
            if gold_universe.contains(&sup) {
                derived.insert((sub, sup));
            }
        }
        // unsat subjects subsume-into everything in gold's universe rows;
        // gold encodes them as pairs already, so expand for the diff.
        for &u in &r.unsatisfiable {
            let sub = tin.concepts[u].clone();
            for sup in &gold_universe {
                if *sup != sub {
                    derived.insert((sub.clone(), sup.clone()));
                }
            }
        }
        let gold_restricted: std::collections::HashSet<(String, String)> = gold_pairs
            .iter()
            .filter(|(sub, sup)| subj_names.contains(sub) && gold_universe.contains(sup))
            .cloned()
            .collect();
        for m in gold_restricted.difference(&derived).take(20) {
            eprintln!("MISSING (incomplete): {} ⊑ {}", m.0, m.1);
        }
        for sp in derived.difference(&gold_restricted).take(20) {
            eprintln!("SPURIOUS (unsound): {} ⊑ {}", sp.0, sp.1);
        }
        eprintln!(
            "BRIDGE-CLASSIFY-PROD {path}: subjects={} derived={} gold={} missing={} \
             spurious={} unsat={} elapsed={:.1}s",
            subjects.len(),
            derived.len(),
            gold_restricted.len(),
            gold_restricted.difference(&derived).count(),
            derived.difference(&gold_restricted).count(),
            r.unsatisfiable.len(),
            elapsed.as_secs_f64(),
        );
    }

    /// Singleton-concept merge (the datatype value-identity clause shape
    /// `V(x) ∧ V(y) → x = y`): X has an r-successor forced into `V ⊓ A` and
    /// an s-successor forced into `V ⊓ ¬A` (via `VA2 ⊓ A ⊑ ⊥`). The two
    /// V-carriers are ONE semantic object, so the deterministic
    /// scan-at-fixpoint merge (u02) must unite them and clash `A ⊓ ¬A` ⇒ X
    /// unsatisfiable. Without the merge the graph is clash-free and the
    /// probe under-detects (the earlier state counted the clause unsupported
    /// and DECLINED). Also asserts the clause is CONSUMED (unsupported == 0,
    /// no defer) and that a singleton-free sibling Y stays satisfiable.
    #[test]
    fn singleton_concept_merge_value_identity_unsat() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, c: usize, t: usize| HAtom::Concept { neg, c, t };
        // concepts: 0=X 1=V 2=A 3=VA1 4=VA2 5=Y
        let tin = TInput {
            concepts: vec![
                "X".into(),
                "V".into(),
                "A".into(),
                "VA1".into(),
                "VA2".into(),
                "Y".into(),
            ],
            roles: vec!["r".into(), "s".into()],
            clauses: vec![
                // V(x) ∧ V(y) → x = y  (the singleton / value-identity shape)
                HtClause {
                    body: vec![c(false, 1, 1), c(false, 1, 2)],
                    head: vec![HAtom::Eq { s: 1, t: 2 }],
                },
                // X ⊑ ∃r.VA1 ; X ⊑ ∃s.VA2
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 3,
                        t: 0,
                    }],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist {
                        r: 1,
                        neg: false,
                        c: 4,
                        t: 0,
                    }],
                },
                // VA1 ⊑ V ; VA1 ⊑ A ; VA2 ⊑ V ; VA2 ⊓ A ⊑ ⊥
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0), c(false, 2, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let r = bridged_classify(&tin).expect("singleton clause must be CONSUMED (no defer)");
        assert!(
            r.unsatisfiable.contains(&0),
            "X must be UNSAT via the value-identity merge (got unsat={:?})",
            r.unsatisfiable
        );
        assert!(
            !r.unsatisfiable.contains(&5),
            "Y (singleton-free) must stay satisfiable"
        );
    }

    /// Fragment-coverage report on a REAL ontology: set `KM_BRIDGE_ONT` to an
    /// .owl/.ofn path and run with `-- --ignored --nocapture`. Reports how
    /// many TInput clauses the v1 bridge encodes vs counts as unsupported —
    /// the data that prioritises the next bridge wave (absorption, inverse,
    /// cardinality). Diagnostic only; asserts nothing about verdicts.
    #[test]
    #[ignore]
    fn bridge_coverage_report() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let top = {
            let mut c = Concept::new();
            c.set_concept_tag(1);
            c.set_operator_code(op::CCTOP);
            ctx.ontology_arenas_mut().alloc_concept(c)
        };
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let bridged = bridge_tinput(&mut ctx, &tin);
        eprintln!(
            "BRIDGE-COVERAGE {path}: concepts={} roles={} clauses={} encoded_impls={} \
             absorbed={} top_attached={} unsupported={} (inverse={} nominals={} card_defs={} chains={})",
            tin.concepts.len(),
            tin.roles.len(),
            tin.clauses.len(),
            bridged.tbox.len(),
            bridged.absorbed,
            bridged.top_attached,
            bridged.unsupported,
            tin.inverse,
            tin.nominals.len(),
            tin.card_defs.len(),
            tin.chains.len(),
        );
    }

    // -----------------------------------------------------------------------
    // Task #23: saturation-first probe answering.
    //
    // These tests drive `bridged_saturate` DIRECTLY (no env flag — env vars
    // are process-global and the suite runs multi-threaded) and cross-check
    // every certain verdict against the completion-probe classification as
    // the oracle.
    // -----------------------------------------------------------------------

    #[test]
    fn saturation_answers_simple_taxonomy() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B, B ⊑ C — the pure-Horn case saturation must fully answer.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 1, 0)],
                    head: vec![c(false, 2, 0)],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict,
            vec![Some(false); 3],
            "all three classes are satisfiable and must be SAT-certain"
        );
        assert_eq!(out.certain_subsumers[0].as_deref(), Some(&[1usize, 2][..]));
        assert_eq!(out.certain_subsumers[1].as_deref(), Some(&[2usize][..]));
        assert_eq!(out.certain_subsumers[2].as_deref(), Some(&[][..]));
        // Oracle: the probe path derives the same taxonomy.
        let r = bridged_classify(&tin).expect("classify");
        let mut probe_subs = r.subsumptions.clone();
        probe_subs.sort_unstable();
        assert_eq!(probe_subs, vec![(0, 1), (0, 2), (1, 2)]);
        assert!(r.unsatisfiable.is_empty());
    }

    #[test]
    fn saturation_existential_applies_role_domain_before_certifying() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |cc: usize, t: usize| HAtom::Concept {
            neg: false,
            c: cc,
            t,
        };
        // A ⊆ ∃r.T and Domain(r, D) entail A ⊆ D. This is the
        // dominant ore_ont_9663 shape: a saturation row is complete only if
        // the domain consequence is present, otherwise it must remain unknown
        // for the completion probe.
        let tin = TInput {
            concepts: vec!["A".into(), "D".into(), "T".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 2,
                        t: 0,
                    }],
                },
                HtClause {
                    body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
                    head: vec![c(1, 0)],
                },
            ],
            ..Default::default()
        };

        let oracle = bridged_classify_opts(&tin, false, false).expect("completion oracle");
        assert!(oracle.subsumptions.contains(&(0, 1)));

        let out = bridged_saturate(&tin).expect("in fragment");
        if out.sat_verdict[0] == Some(false) {
            assert!(
                out.certain_subsumers[0]
                    .as_ref()
                    .is_some_and(|subsumers| subsumers.contains(&1)),
                "a SAT-certain A row must include the role-domain subsumer D"
            );
        }
    }

    #[test]
    fn saturation_detects_unsat_concept() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B and A ⊓ B ⊑ ⊥ — the deterministic clash must surface as
        // UNSAT-certain on A while B stays SAT-certain.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 0, 0), c(false, 1, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(out.sat_verdict[0], Some(true), "A is unsatisfiable");
        assert_eq!(out.sat_verdict[1], Some(false), "B is satisfiable");
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
        assert!(!r.unsatisfiable.contains(&1));
    }

    #[test]
    fn probe_oracle_alone_detects_unsat_concept() {
        // DIAGNOSTIC twin of `saturation_detects_unsat_concept` WITHOUT the
        // saturation pre-pass: isolates whether the probe path alone answers
        // the tiny A ⊑ B, A ⊓ B ⊑ ⊥ input (checks the oracle, not saturation).
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 0, 0), c(false, 1, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let r = bridged_classify(&tin).expect("classify");
        assert!(
            r.unsatisfiable.contains(&0),
            "probe path must detect A unsat (got unsat={:?} subs={:?})",
            r.unsatisfiable,
            r.subsumptions
        );
    }

    #[test]
    fn saturation_defers_disjunction_subjects() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B ⊔ C — branching: the non-branching saturation must NOT claim
        // a certain verdict built on one disjunct (the OR rule goes critical;
        // with no disjunct entailed the node is insufficient ⇒ unknown).
        // B and C stay plain satisfiable classes.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            clauses: vec![HtClause {
                body: vec![c(false, 0, 0)],
                head: vec![c(false, 1, 0), c(false, 2, 0)],
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        // Soundness bar: whatever A gets, it must not be a WRONG certainty.
        // A is satisfiable with no named subsumers; SAT-certain is acceptable
        // ONLY with an empty subsumer set; unknown (defer) is acceptable.
        match out.sat_verdict[0] {
            Some(true) => panic!("A is satisfiable — UNSAT-certain is unsound"),
            Some(false) => {
                assert_eq!(
                    out.certain_subsumers[0].as_deref(),
                    Some(&[][..]),
                    "a certain subsumer from ONE disjunct branch would be unsound"
                );
            }
            None => {}
        }
        assert_eq!(out.sat_verdict[1], Some(false));
        assert_eq!(out.sat_verdict[2], Some(false));
    }

    #[test]
    fn saturation_never_sat_certain_on_forall_exists_clash() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ ∃r.B and A ⊑ ∀r.¬B ⇒ A unsatisfiable. The cheap saturation
        // shares successor nodes, so it may not DETECT the clash — but it must
        // never claim SAT-certain (the ∀-into-creation-direction escape hatch:
        // criticality/insufficiency must fire).
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 1,
                        t: 0,
                    }],
                },
                // A(x) ∧ r(x,y) ∧ B(y) → ⊥  (A ⊑ ∀r.¬B)
                HtClause {
                    body: vec![
                        c(false, 0, 0),
                        HAtom::Role { r: 0, s: 0, t: 1 },
                        c(false, 1, 1),
                    ],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT — SAT-certain would be a soundness bug \
             (the ∀-into-creation-direction hatch must defer or clash)"
        );
        assert_eq!(out.sat_verdict[1], Some(false), "B alone is satisfiable");
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
    }

    // -----------------------------------------------------------------------
    // Task #24: precise ATMOST criticality test (isCriticalATMOSTConcept-
    // DescriptorInsufficient + collect + simple/detailed mergeability).
    // -----------------------------------------------------------------------

    /// `A ⊑ ∃r.B, A ⊑ ≤2 r.B`: one successor against a bound of two — the
    /// precise test must answer SAT-certain (the old conservative stub
    /// deferred EVERY critical ≤n).
    #[test]
    fn saturation_answers_atmost_within_bound() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![HtClause {
                body: vec![c(false, 0, 0)],
                head: vec![HAtom::Exist {
                    r: 0,
                    neg: false,
                    c: 1,
                    t: 0,
                }],
            }],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "A has 1 r.B successor against ≤2 r.B — must be SAT-certain"
        );
        assert_eq!(out.sat_verdict[1], Some(false));
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// `A ⊑ ∃r.B, A ⊑ ∃r.C, A ⊑ ≤1 r.B`: the C-successor does not count
    /// toward the qualified bound (its label cannot positively satisfy B) —
    /// SAT-certain with the precise qualified counting.
    #[test]
    fn saturation_atmost_qualified_counting_sat() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 1)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
            ],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "only the B-successor counts toward ≤1 r.B — A is SAT-certain"
        );
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// `A ⊑ ∃r.B1, A ⊑ ∃r.B2, B1 ⊑ B, B2 ⊑ B, A ⊑ ≤1 r.B`: both successors
    /// count, but their labels are compatible — the mergeability discount
    /// brings the residual cardinality back to the bound ⇒ SAT-certain.
    #[test]
    fn saturation_atmost_merging_discount_sat() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "B1".into(), "B2".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 3)],
                },
                HtClause {
                    body: vec![c(false, 2, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
            ],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "the two r-successors are label-mergeable — ≤1 r.B holds, A SAT-certain"
        );
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// The disjoint twin of the merging-discount case: `B1 ⊓ B2 ⊑ ⊥` makes
    /// the merge clash, so A is UNSATISFIABLE — the saturation must NOT
    /// claim SAT-certain (label-merging-problematic must veto the discount).
    #[test]
    fn saturation_atmost_disjoint_successors_not_sat_certain() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "B1".into(), "B2".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 3)],
                },
                HtClause {
                    body: vec![c(false, 2, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
                // B1 ⊓ B2 ⊑ ⊥
                HtClause {
                    body: vec![c(false, 2, 0), c(false, 3, 0)],
                    head: vec![],
                },
            ],
            number: true,
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT (disjoint successors under ≤1 r.B) — SAT-certain would \
             mean the mergeability discount ignored the disjointness"
        );
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
    }

    /// `A ⊑ ≥3 r.B, A ⊑ ≤2 r.B`: the pairwise-distinct ≥3 successors exceed
    /// the bound — the saturation must not read SAT-certain (Konclude clashes
    /// the node in collectATMOSTConceptRelevantSuccessors when a single
    /// distinct-successor block already exceeds the allowance).
    #[test]
    fn saturation_atleast_over_atmost_not_sat_certain() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![],
            number: true,
            card_defs: vec![
                CardDefJson {
                    marker: 0,
                    min: true,
                    n: 3,
                    role: 0,
                    filler: 1,
                },
                CardDefJson {
                    marker: 0,
                    min: false,
                    n: 2,
                    role: 0,
                    filler: 1,
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT (≥3 r.B vs ≤2 r.B) — SAT-certain is unsound"
        );
        assert_eq!(out.sat_verdict[1], Some(false), "B alone is satisfiable");
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(
            r.unsatisfiable.contains(&0),
            "probe oracle must prove A unsat (got {:?})",
            r.unsatisfiable
        );
    }

    // -----------------------------------------------------------------------
    // Saturation-node coupling into the completion probes (task #24 wave 2):
    // expand-from-saturation (u17) + caching-blocking (u22) armed inside the
    // probe env after a same-env saturation pass. Driven programmatically
    // (env-var-independent).
    // -----------------------------------------------------------------------

    /// The ∃-rule must replay the filler's saturated label onto the fresh
    /// successor (expansion) and establish saturation blocking on it — and
    /// both must KEEP firing after a `reset_probe_env` carry (the arenas +
    /// reference linkings survive the reset).
    #[test]
    fn satcache_expansion_and_blocking_fire_in_probe() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        assert_eq!(bridged.unsupported, 0, "fully bridged");
        assert!(
            run_bridged_saturation(&mut ctx, &bridged),
            "saturation within budget"
        );
        let arm = |algo: &mut CompletionTaskHandleAlgorithm| {
            configure_production_completion_saturation_coupling(algo);
        };
        arm(&mut algo);
        assert!(
            !algo.conf_successor_saturation_expansion_restrictions_resolving,
            "production completion must match Konclude's disabled restriction resolver"
        );
        assert!(
            algo.conf_saturation_expansion_cache_reading,
            "production coupling must retain cached successors after modification"
        );
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        let (a, d) = (bridged.named[idx("A")], bridged.named[idx("D")]);
        let mut id = 0i64;
        // A ⊓ ¬D is satisfiable (A ⋢ D); the drive expands A's ∃r.B.
        let verdict = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id,
            &[(a, false), (d, true)],
        );
        assert_eq!(verdict, Some(false), "A ⊑ D must NOT hold");
        assert!(
            algo.saturation_expansion_concept_count > 0,
            "the saturated filler label must be replayed onto the ∃-successor"
        );
        assert!(
            algo.saturation_cache_establish_count > 0,
            "the ∃-successor must be established saturation-blocked"
        );
        // The classify-style reset must CARRY the saturation state: the
        // coupling keeps firing on the warm env.
        reset_probe_env(&mut algo, &mut ctx, &bridged, true);
        arm(&mut algo);
        let mut id2 = 0i64;
        let warm = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id2,
            &[(a, false), (d, true)],
        );
        assert_eq!(warm, Some(false), "verdict stable across the carry");
        assert!(
            algo.saturation_expansion_concept_count > 0
                && algo.saturation_cache_establish_count > 0,
            "the coupling must survive reset_probe_env (saturation arenas carried)"
        );
    }

    #[test]
    fn satcache_successful_root_writes_and_preserves_associated_expansion() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        install_bridge_saturation_node_expansion_cache(&mut ctx);
        configure_production_search(&mut algo);
        algo.conf_expand_created_successors_from_saturation = true;
        algo.conf_caching_blocking_from_saturation = true;
        algo.conf_saturation_satisfiabilitiy_expansion_cache_writing = true;
        let a = env
            .tin
            .concepts
            .iter()
            .position(|name| name == "A")
            .expect("A in classification input");
        // Production probes reserve low IDs for ontology individuals.
        let mut next_id = 1_000;
        assert!(bridged_classify_subject(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut next_id,
            a,
            bridged.named.len(),
        )
        .is_some());
        let state = ctx
            .take_used_saturation_node_expansion_cache_handler()
            .expect("associated-expansion cache remains installed");
        assert!(
            state.cache_context.sat_expansion_cache_entries.len() > 0,
            "successful root must write an associated-expansion cache entry"
        );
        ctx.restore_used_saturation_node_expansion_cache_handler(state);

        reset_probe_env(&mut algo, &mut ctx, &bridged, true);
        assert!(
            ctx.take_used_saturation_node_expansion_cache_handler()
                .is_some(),
            "classification reset must preserve the ontology-wide cache"
        );
    }

    /// A clashed saturation node must replay as a CLASH in the probe: with
    /// B deterministically unsatisfiable (B ⊑ C ⊓ ¬C), probing A (⊑ ∃r.B)
    /// must answer UNSAT through `try_expansion_from_saturated_data`'s
    /// clash arm — and agree with the plain (uncoupled) probe.
    #[test]
    fn satcache_clash_replay_probe_unsat() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n\
             SubClassOf(:B ObjectComplementOf(:C))\n)"
        );
        let env = bridge_ofn(&ofn);
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        // Plain probe (no saturation, no coupling): A unsat.
        {
            let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
            assert_eq!(bridged.unsupported, 0);
            let a = bridged.named[idx("A")];
            let mut id = 0i64;
            let plain = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(a, false)]);
            assert_eq!(plain, Some(true), "A is unsatisfiable (plain probe)");
        }
        // Coupled probe: the ∃-rule must clash from B's CLASHED saturation node.
        {
            let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
            assert!(run_bridged_saturation(&mut ctx, &bridged));
            algo.conf_expand_created_successors_from_saturation = true;
            algo.conf_caching_blocking_from_saturation = true;
            let a = bridged.named[idx("A")];
            let mut id = 0i64;
            let coupled = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(a, false)]);
            assert_eq!(coupled, Some(true), "A is unsatisfiable (coupled probe)");
        }
    }

    /// Public-API A/B/C: plain probes vs saturation-only vs saturation +
    /// coupling must classify identically on a mixed ontology whose
    /// disjunction forces a probe residue (the coupling actually runs).
    #[test]
    fn satcache_classification_matches_plain() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:X)) Declaration(Class(:Y)) Declaration(Class(:Z))\n\
             Declaration(Class(:A1)) Declaration(Class(:A2))\n\
             Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:X ObjectUnionOf(:A1 :A2))\n\
             SubClassOf(:A1 :Y)\n\
             SubClassOf(:A2 :Y)\n\
             SubClassOf(:Y ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n\
             SubClassOf(:Z ObjectAllValuesFrom(:r ObjectComplementOf(:B)))\n)"
        );
        let env = bridge_ofn(&ofn);
        let norm = |r: BridgedClassification| {
            let mut u = r.unsatisfiable;
            let mut s = r.subsumptions;
            u.sort_unstable();
            s.sort_unstable();
            (u, s)
        };
        let plain = norm(bridged_classify_opts(&env.tin, false, false).expect("plain arm"));
        let sat_only = norm(bridged_classify_opts(&env.tin, true, false).expect("sat-only arm"));
        let coupled = norm(bridged_classify_opts(&env.tin, true, true).expect("coupled arm"));
        assert_eq!(plain, sat_only, "saturation-only must not change verdicts");
        assert_eq!(
            plain, coupled,
            "the saturation-node coupling must not change verdicts"
        );
    }

    /// Horn ∃-cycle equality: `B ⊑ ∃r.B` grows an unbounded chain that the
    /// coupled arm must terminate via successor absorption (the cached
    /// successor's generating ∃ is absorbed instead of expanded) with the
    /// SAME classification as the plain arm (which terminates via blocking).
    /// Horn-only so every read-off is authoritative — no branch probes, no
    /// poison-defer noise in either arm.
    #[test]
    fn satcache_absorption_terminates_exists_cycle() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:X)) Declaration(Class(:Y))\n\
             Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:X :Y)\n\
             SubClassOf(:Y ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n\
             SubClassOf(:B ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:C :D)\n)"
        );
        let env = bridge_ofn(&ofn);
        let norm = |r: BridgedClassification| {
            let mut u = r.unsatisfiable;
            let mut s = r.subsumptions;
            u.sort_unstable();
            s.sort_unstable();
            (u, s)
        };
        let plain = norm(bridged_classify_opts(&env.tin, false, false).expect("plain arm"));
        let coupled = norm(bridged_classify_opts(&env.tin, true, true).expect("coupled arm"));
        assert_eq!(
            plain, coupled,
            "absorption must preserve the classification"
        );
        assert!(
            plain.1.len() >= 4,
            "sanity: the taxonomy has X⊑Y, B⊑C, B⊑D, C⊑D (got {:?})",
            plain.1
        );
    }

    /// Full-agreement harness: saturation certainties vs the probe-path
    /// classification on a small mixed ontology (Horn taxonomy + one
    /// disjunction + one ∃/∀ interaction). Every CERTAIN saturation answer
    /// must match the oracle exactly; unknowns are free.
    #[test]
    fn saturation_certainties_agree_with_probe_classification() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // 0=A 1=B 2=C 3=D 4=E; r
        // A ⊑ B, B ⊑ C, D ⊑ B ⊔ C, E ⊑ ∃r.A, E ⊑ ∀r.B (entailed anyway), C ⊓ A ⊑ D? no — keep simple.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into(), "D".into(), "E".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 1, 0)],
                    head: vec![c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0), c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 0,
                        t: 0,
                    }],
                },
            ],
            ..Default::default()
        };
        let oracle = bridged_classify(&tin).expect("classify");
        let oracle_subs: std::collections::HashSet<(usize, usize)> =
            oracle.subsumptions.iter().copied().collect();
        let out = bridged_saturate(&tin).expect("in fragment");
        for i in 0..tin.concepts.len() {
            match out.sat_verdict[i] {
                Some(true) => assert!(
                    oracle.unsatisfiable.contains(&i),
                    "saturation UNSAT-certain on {} disagrees with oracle",
                    tin.concepts[i]
                ),
                Some(false) => {
                    assert!(
                        !oracle.unsatisfiable.contains(&i),
                        "saturation SAT-certain on {} but oracle says unsat",
                        tin.concepts[i]
                    );
                    if let Some(subs) = &out.certain_subsumers[i] {
                        let sat_set: std::collections::HashSet<(usize, usize)> =
                            subs.iter().map(|&cc| (i, cc)).collect();
                        let oracle_row: std::collections::HashSet<(usize, usize)> = oracle_subs
                            .iter()
                            .filter(|&&(s, _)| s == i)
                            .copied()
                            .collect();
                        assert_eq!(
                            sat_set, oracle_row,
                            "certain-subsumer row for {} diverges from oracle",
                            tin.concepts[i]
                        );
                    }
                }
                None => {}
            }
        }
    }
}
