//! Sound, one-shot propagation of named classes known to be empty.
//!
//! Konclude does not repeat a complete satisfiability test for every descendant
//! of an unsatisfiable class. Once a root is known empty, its classifier
//! propagates that verdict through the told dependency order. This module
//! materializes a cheap, deterministic subset of the same consequences before
//! KM starts classification:
//!
//! * conflicting inherited values on a functional data/object property;
//! * `A <= B` and `B <= bottom` imply `A <= bottom`;
//! * `A <= exists R.B` and `B <= bottom` imply `A <= bottom`; and
//! * a required successor is impossible when every alternative allowed by the
//!   role range, inverse-role domain, and inherited universal restrictions has
//!   one of the certified clashes above.
//!
//! The contextual check is bounded and fail-closed. Unsupported expressions or
//! a search-cap hit are treated as `top`, so they can only lose a certificate.
//! Every emitted bottom constraint is therefore an entailed OWL consequence.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use super::clauses::{Atom, DLClause};
use super::iri::IriRegistry;
use super::sexpr::Node;
use super::syntax::{Axiom, Concept, Ontology, Role};

const MAX_EXPRESSION_ALTERNATIVES: usize = 256;
const MAX_CONTEXT_BRANCHES: usize = 4_096;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BottomPrepassResult {
    /// Internal class names certified equivalent to the empty class.
    pub classes: Vec<String>,
    /// Classes directly clashing on a functional property (plus explicit
    /// source-bottom classes), before dependency propagation.
    pub seeds: usize,
    /// New bottom classes reached through an atomic subclass edge.
    pub via_subclass: usize,
    /// New bottom classes reached through a named existential filler.
    pub via_existential: usize,
    /// Independently impossible existential owners found by the contextual
    /// successor check. Their descendants are counted in the two fields above.
    pub contextual_roots: usize,
    /// Named-class subsumptions forced by role domain/range alternatives at a
    /// required edge's owner. Every emitted parent occurs in every branch that
    /// survives the bounded clash check.
    pub forced_subclasses: Vec<(String, String)>,
    /// Owner/alternative pairs proved incompatible while checking those role
    /// constraints. Materialising these entailed constraints lets downstream
    /// model builders avoid choices that this prepass has already refuted.
    pub incompatible_pairs: Vec<(String, String)>,
    /// Source classes linked to fresh internal markers for their required
    /// value on a functional property. Distinct-value marker pairs occur in
    /// `incompatible_pairs`, exposing concrete-domain clashes compactly.
    pub value_markers: Vec<(String, String)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DependencyKind {
    Subclass,
    Existential,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum RequiredValue {
    Data(String),
    Object(String),
}

/// Exact DNF over named classes. `[]` is bottom; `[[]]` is top. Expressions
/// outside the supported positive named fragment are deliberately mapped to
/// top, a sound over-approximation for an emptiness proof.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ClassConstraint {
    alternatives: Vec<Vec<String>>,
}

impl ClassConstraint {
    fn top() -> Self {
        Self {
            alternatives: vec![Vec::new()],
        }
    }

    fn bottom() -> Self {
        Self {
            alternatives: Vec::new(),
        }
    }

    fn named(name: String) -> Self {
        Self {
            alternatives: vec![vec![name]],
        }
    }

    fn is_top(&self) -> bool {
        self.alternatives.len() == 1 && self.alternatives[0].is_empty()
    }

    fn disjunction(parts: impl IntoIterator<Item = Self>) -> Self {
        let mut alternatives = Vec::new();
        for part in parts {
            if part.is_top() {
                return Self::top();
            }
            alternatives.extend(part.alternatives);
            if alternatives.len() > MAX_EXPRESSION_ALTERNATIVES {
                return Self::top();
            }
        }
        canonical_constraint(alternatives)
    }

    fn conjunction(parts: impl IntoIterator<Item = Self>) -> Self {
        let mut product = vec![Vec::new()];
        for part in parts {
            if part.alternatives.is_empty() {
                return Self::bottom();
            }
            if part.is_top() {
                continue;
            }
            let mut next = Vec::new();
            for left in &product {
                for right in &part.alternatives {
                    let mut alternative = left.clone();
                    alternative.extend(right.iter().cloned());
                    next.push(alternative);
                    if next.len() > MAX_EXPRESSION_ALTERNATIVES {
                        // Replacing an over-large conjunction by top weakens it;
                        // this can only suppress an emptiness certificate.
                        return Self::top();
                    }
                }
            }
            product = next;
        }
        canonical_constraint(product)
    }

    fn from_concept(concept: &Concept) -> Self {
        match concept {
            Concept::Name(name) => Self::named(name.clone()),
            Concept::Top => Self::top(),
            Concept::Bottom => Self::bottom(),
            Concept::And(parts) => Self::conjunction(parts.iter().map(Self::from_concept)),
            Concept::Or(parts) => Self::disjunction(parts.iter().map(Self::from_concept)),
            // Nominals, complements, and restrictions need equality/modal state
            // not represented by this prepass. Treat them as unconstrained.
            _ => Self::top(),
        }
    }

    fn names(&self) -> impl Iterator<Item = &str> {
        self.alternatives
            .iter()
            .flat_map(|alternative| alternative.iter().map(String::as_str))
    }
}

fn canonical_constraint(mut alternatives: Vec<Vec<String>>) -> ClassConstraint {
    for alternative in &mut alternatives {
        alternative.sort();
        alternative.dedup();
    }
    alternatives.sort();
    alternatives.dedup();
    ClassConstraint { alternatives }
}

#[derive(Clone, Debug)]
enum RawClassConstraint {
    Name(String),
    Top,
    Bottom,
    And(Vec<RawClassConstraint>),
    Or(Vec<RawClassConstraint>),
    Unknown,
}

impl RawClassConstraint {
    fn from_node(node: &Node<'_>) -> Self {
        match node {
            Node::Atom(name) => Self::Name((*name).to_string()),
            Node::List("ObjectIntersectionOf", parts) => {
                Self::And(parts.iter().map(Self::from_node).collect())
            }
            Node::List("ObjectUnionOf", parts) => {
                Self::Or(parts.iter().map(Self::from_node).collect())
            }
            _ => Self::Unknown,
        }
    }

    fn resolve(self, registry: &mut IriRegistry) -> ClassConstraint {
        match self {
            Self::Name(raw) => match registry.short(&raw).as_str() {
                "owl:Thing" => ClassConstraint::top(),
                "owl:Nothing" => ClassConstraint::bottom(),
                name => ClassConstraint::named(name.to_string()),
            },
            Self::Top => ClassConstraint::top(),
            Self::Bottom => ClassConstraint::bottom(),
            Self::And(parts) => {
                ClassConstraint::conjunction(parts.into_iter().map(|part| part.resolve(registry)))
            }
            Self::Or(parts) => {
                ClassConstraint::disjunction(parts.into_iter().map(|part| part.resolve(registry)))
            }
            Self::Unknown => ClassConstraint::top(),
        }
    }
}

/// Zero-copy pass-2 observer for role domains/ranges. Raw names are retained
/// without touching the IRI registry, then resolved only after declarations,
/// preserving the frontend's established collision-assignment order.
#[derive(Clone, Debug, Default)]
pub struct RawRoleConstraints {
    domains: Vec<(String, RawClassConstraint)>,
    ranges: Vec<(String, RawClassConstraint)>,
}

impl RawRoleConstraints {
    pub fn observe(&mut self, node: &Node<'_>) {
        let Node::List(head, raw_args) = node else {
            return;
        };
        if !matches!(*head, "ObjectPropertyDomain" | "ObjectPropertyRange") {
            return;
        }
        let args: Vec<&Node<'_>> = raw_args
            .iter()
            .filter(|arg| arg.head() != Some("Annotation"))
            .collect();
        if args.len() < 2 {
            return;
        }
        let class = RawClassConstraint::from_node(args[1]);
        let (role, inverse) = match args[0] {
            Node::Atom(role) => ((*role).to_string(), false),
            Node::List("ObjectInverseOf", members) => {
                let Some(Node::Atom(role)) = members.first() else {
                    return;
                };
                ((*role).to_string(), true)
            }
            _ => return,
        };
        // domain(inv(r)) = range(r), range(inv(r)) = domain(r)
        let is_domain = *head == "ObjectPropertyDomain";
        if is_domain ^ inverse {
            self.domains.push((role, class));
        } else {
            self.ranges.push((role, class));
        }
    }

    pub fn resolve(self, registry: &mut IriRegistry) -> RoleConstraints {
        let mut out = RoleConstraints::default();
        for (role, class) in self.domains {
            let role = registry.short(&role);
            let class = class.resolve(registry);
            out.domains.entry(role).or_default().push(class);
        }
        for (role, class) in self.ranges {
            let role = registry.short(&role);
            let class = class.resolve(registry);
            out.ranges.entry(role).or_default().push(class);
        }
        for constraints in out.domains.values_mut().chain(out.ranges.values_mut()) {
            constraints.sort();
            constraints.dedup();
        }
        out
    }
}

#[derive(Clone, Debug, Default)]
pub struct RoleConstraints {
    domains: BTreeMap<String, Vec<ClassConstraint>>,
    ranges: BTreeMap<String, Vec<ClassConstraint>>,
}

#[derive(Default)]
pub struct BottomPrepass {
    names: Vec<String>,
    ids: HashMap<String, usize>,
    /// child -> parent
    supers: Vec<Vec<usize>>,
    /// owner -> (required role, named filler)
    existentials: Vec<Vec<(String, usize)>>,
    /// owner -> (role, required successor formula)
    universals: Vec<Vec<(String, ClassConstraint)>>,
    /// Direct data/object has-value restrictions before inheritance.
    direct_values: Vec<Vec<(String, RequiredValue)>>,
    explicit_bottom: Vec<usize>,
    functional: HashSet<String>,
    different: HashSet<(String, String)>,
    disjoint: HashSet<(usize, usize)>,
    role_supers: HashMap<String, Vec<String>>,
    inverse_roles: HashMap<String, Vec<String>>,
}

impl BottomPrepass {
    fn id(&mut self, name: &str) -> usize {
        if let Some(&id) = self.ids.get(name) {
            return id;
        }
        let id = self.names.len();
        self.names.push(name.to_string());
        self.ids.insert(name.to_string(), id);
        self.supers.push(Vec::new());
        self.existentials.push(Vec::new());
        self.universals.push(Vec::new());
        self.direct_values.push(Vec::new());
        id
    }

    fn atomic_subclass(&mut self, child: &str, parent: &str) {
        let child = self.id(child);
        let parent = self.id(parent);
        self.supers[child].push(parent);
    }

    fn requirement(&mut self, owner: &str, expression: &Concept) {
        match expression {
            Concept::Name(parent) => self.atomic_subclass(owner, parent),
            Concept::Bottom => {
                let owner = self.id(owner);
                self.explicit_bottom.push(owner);
            }
            Concept::And(conjuncts) => {
                for conjunct in conjuncts {
                    self.requirement(owner, conjunct);
                }
            }
            Concept::Exists(Role::Name(role), filler)
            | Concept::AtLeast(1.., Role::Name(role), filler) => {
                let owner_id = self.id(owner);
                match filler.as_ref() {
                    Concept::Name(filler) if filler.starts_with("__dt__val__") => self
                        .direct_values[owner_id]
                        .push((role.clone(), RequiredValue::Data(filler.clone()))),
                    Concept::Name(filler) if !filler.starts_with("__dt__") => {
                        let filler_id = self.id(filler);
                        self.existentials[owner_id].push((role.clone(), filler_id));
                    }
                    Concept::Nominal(individual) => self.direct_values[owner_id]
                        .push((role.clone(), RequiredValue::Object(individual.clone()))),
                    _ => {}
                }
            }
            Concept::Forall(Role::Name(role), filler) => {
                let owner = self.id(owner);
                let constraint = ClassConstraint::from_concept(filler);
                let names: Vec<String> = constraint.names().map(str::to_string).collect();
                for name in names {
                    self.id(&name);
                }
                self.universals[owner].push((role.clone(), constraint));
            }
            _ => {}
        }
    }

    pub fn from_ontology(ontology: &Ontology) -> Self {
        let mut out = BottomPrepass::default();
        for axiom in ontology.rbox() {
            match axiom {
                Axiom::FunctionalRole(role) => {
                    out.functional.insert(role.clone());
                }
                Axiom::RoleInclusion(sub, sup) => {
                    out.role_supers
                        .entry(sub.clone())
                        .or_default()
                        .push(sup.clone());
                }
                Axiom::InverseRoles(left, right) => {
                    out.inverse_roles
                        .entry(left.clone())
                        .or_default()
                        .push(right.clone());
                    out.inverse_roles
                        .entry(right.clone())
                        .or_default()
                        .push(left.clone());
                }
                _ => {}
            }
        }
        for axiom in ontology.tbox() {
            match axiom {
                Axiom::SubClassOf(Concept::Name(owner), expression) => {
                    out.requirement(owner, expression);
                }
                Axiom::EquivalentClasses(left, right) => {
                    if let Concept::Name(owner) = left {
                        out.requirement(owner, right);
                    }
                    if let Concept::Name(owner) = right {
                        out.requirement(owner, left);
                    }
                }
                Axiom::DisjointClasses(Concept::Name(left), Concept::Name(right)) => {
                    let left = out.id(left);
                    let right = out.id(right);
                    out.disjoint.insert(ordered_usize_pair(left, right));
                }
                _ => {}
            }
        }
        for axiom in ontology.abox() {
            if let Axiom::DifferentIndividuals(left, right) = axiom {
                out.different
                    .insert(ordered_string_pair(left.clone(), right.clone()));
            }
        }
        for edges in &mut out.supers {
            edges.sort_unstable();
            edges.dedup();
        }
        for edges in &mut out.existentials {
            edges.sort();
            edges.dedup();
        }
        for constraints in &mut out.universals {
            constraints.sort();
            constraints.dedup();
        }
        for values in &mut out.direct_values {
            values.sort();
            values.dedup();
        }
        for roles in out
            .role_supers
            .values_mut()
            .chain(out.inverse_roles.values_mut())
        {
            roles.sort();
            roles.dedup();
        }
        out.explicit_bottom.sort_unstable();
        out.explicit_bottom.dedup();
        out
    }

    pub fn certify(mut self, role_constraints: &RoleConstraints) -> BottomPrepassResult {
        for constraint in role_constraints
            .domains
            .values()
            .chain(role_constraints.ranges.values())
            .flatten()
        {
            for name in constraint.names() {
                self.id(name);
            }
        }
        if self.names.is_empty() {
            return BottomPrepassResult::default();
        }

        let children = class_children(&self.supers);
        let role_closure = role_super_closure(&self, role_constraints);
        let values = inherited_values(&self, &children, &role_closure);
        let universals = inherited_universals(&self, &children);
        let distinct_data = distinct_data_pairs(&values);
        let (value_markers, marker_incompatibilities) =
            functional_value_markers(&self, &role_closure, &distinct_data);

        let mut bottom = vec![false; self.names.len()];
        let mut queue = VecDeque::new();
        for &class in &self.explicit_bottom {
            if !bottom[class] {
                bottom[class] = true;
                queue.push_back(class);
            }
        }
        for class in 0..self.names.len() {
            if value_maps_clash(
                std::iter::once(&values[class]),
                &self.functional,
                &distinct_data,
                &self.different,
            ) && !bottom[class]
            {
                bottom[class] = true;
                queue.push_back(class);
            }
        }
        let seed_count = queue.len();

        let mut dependents = vec![Vec::new(); self.names.len()];
        for (parent, subclasses) in children.iter().enumerate() {
            for &child in subclasses {
                dependents[parent].push((child, DependencyKind::Subclass));
            }
        }
        for (owner, fillers) in self.existentials.iter().enumerate() {
            for (_, filler) in fillers {
                dependents[*filler].push((owner, DependencyKind::Existential));
            }
        }

        let mut via_subclass = 0;
        let mut via_existential = 0;
        propagate_bottom(
            &mut bottom,
            &mut queue,
            &dependents,
            &mut via_subclass,
            &mut via_existential,
        );

        let mut contextual_roots = 0;
        loop {
            let mut newly_empty = Vec::new();
            for owner in 0..self.names.len() {
                if bottom[owner] {
                    continue;
                }
                let impossible = self.existentials[owner].iter().any(|(role, filler)| {
                    context_impossible(
                        owner,
                        role,
                        *filler,
                        &self,
                        role_constraints,
                        &role_closure,
                        &universals,
                        &values,
                        &bottom,
                        &distinct_data,
                    )
                });
                if impossible {
                    newly_empty.push(owner);
                }
            }
            if newly_empty.is_empty() {
                break;
            }
            for owner in newly_empty {
                if !bottom[owner] {
                    bottom[owner] = true;
                    contextual_roots += 1;
                    queue.push_back(owner);
                }
            }
            propagate_bottom(
                &mut bottom,
                &mut queue,
                &dependents,
                &mut via_subclass,
                &mut via_existential,
            );
        }

        // A required r-successor also constrains its OWNER through Domain(r)
        // and, for every inverse s of r, Range(s).  Enumerate the positive
        // named alternatives of those constraints.  The enumeration is an
        // over-approximation: unsupported expressions become top and our
        // clash test recognizes only already certified bottom, named
        // disjointness, and distinct values of functional properties.  A type
        // common to every surviving over-approximated branch is consequently
        // an entailed superclass of the owner.  Hitting a cap returns no
        // consequence.
        let mut forced_ids: BTreeSet<(usize, usize)> = BTreeSet::new();
        let mut incompatible_ids: BTreeSet<(usize, usize)> = BTreeSet::new();
        for owner in 0..self.names.len() {
            if bottom[owner] {
                continue;
            }
            let owner_closure = type_closure(&[owner], &self);
            for (role, _) in &self.existentials[owner] {
                let factors = owner_context_factors(role, &self, role_constraints, &role_closure);
                if factors.is_empty() {
                    continue;
                }

                // Record only unary alternatives here.  For such an
                // alternative, owner ⊓ choice ⊑ ⊥ follows directly from
                // the same sound clash check, independent of the other role
                // factors.  Multi-name alternatives remain represented by the
                // full bounded search below and are not weakened into pairwise
                // constraints.
                for factor in &factors {
                    for alternative in &factor.alternatives {
                        if alternative.len() != 1 {
                            continue;
                        }
                        let Some(&choice) = self.ids.get(&alternative[0]) else {
                            continue;
                        };
                        if selected_types_clash(
                            &[owner, choice],
                            &self,
                            &values,
                            &bottom,
                            &distinct_data,
                        ) {
                            incompatible_ids.insert(ordered_usize_pair(owner, choice));
                        }
                    }
                }

                let Some(Some(common)) = viable_context_common_types(
                    owner,
                    &factors,
                    &self,
                    &values,
                    &bottom,
                    &distinct_data,
                ) else {
                    // Unknown (cap) or no viable branch.  The latter can prove
                    // the owner empty, but bottom propagation above deliberately
                    // owns that verdict; declining here stays sound and keeps
                    // this pass one-shot.
                    continue;
                };
                for parent in common {
                    if parent != owner && !owner_closure.contains(&parent) {
                        forced_ids.insert((owner, parent));
                    }
                }
            }
        }

        let mut classes: Vec<String> = bottom
            .iter()
            .enumerate()
            .filter_map(|(id, &empty)| empty.then(|| self.names[id].clone()))
            .collect();
        classes.sort();
        let forced_subclasses = forced_ids
            .into_iter()
            .map(|(child, parent)| (self.names[child].clone(), self.names[parent].clone()))
            .collect();
        let mut incompatible_pairs: Vec<(String, String)> = incompatible_ids
            .into_iter()
            .map(|(left, right)| (self.names[left].clone(), self.names[right].clone()))
            .collect();
        incompatible_pairs.extend(marker_incompatibilities);
        incompatible_pairs.sort();
        incompatible_pairs.dedup();
        BottomPrepassResult {
            classes,
            seeds: seed_count,
            via_subclass,
            via_existential,
            contextual_roots,
            forced_subclasses,
            incompatible_pairs,
            value_markers,
        }
    }
}

fn class_children(supers: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut children = vec![Vec::new(); supers.len()];
    for (child, parents) in supers.iter().enumerate() {
        for &parent in parents {
            children[parent].push(child);
        }
    }
    children
}

fn role_super_closure(
    prepass: &BottomPrepass,
    constraints: &RoleConstraints,
) -> HashMap<String, Vec<String>> {
    let mut roles = BTreeSet::new();
    roles.extend(prepass.functional.iter().cloned());
    roles.extend(prepass.role_supers.keys().cloned());
    roles.extend(prepass.role_supers.values().flatten().cloned());
    roles.extend(prepass.inverse_roles.keys().cloned());
    roles.extend(prepass.inverse_roles.values().flatten().cloned());
    roles.extend(constraints.domains.keys().cloned());
    roles.extend(constraints.ranges.keys().cloned());
    for restrictions in &prepass.existentials {
        roles.extend(restrictions.iter().map(|(role, _)| role.clone()));
    }
    for restrictions in &prepass.universals {
        roles.extend(restrictions.iter().map(|(role, _)| role.clone()));
    }
    for restrictions in &prepass.direct_values {
        roles.extend(restrictions.iter().map(|(role, _)| role.clone()));
    }

    let mut out = HashMap::new();
    for role in roles {
        let mut seen = BTreeSet::from([role.clone()]);
        let mut queue = VecDeque::from([role.clone()]);
        while let Some(current) = queue.pop_front() {
            for next in prepass.role_supers.get(&current).into_iter().flatten() {
                if seen.insert(next.clone()) {
                    queue.push_back(next.clone());
                }
            }
        }
        out.insert(role, seen.into_iter().collect());
    }
    out
}

fn inherited_values(
    prepass: &BottomPrepass,
    children: &[Vec<usize>],
    role_closure: &HashMap<String, Vec<String>>,
) -> Vec<BTreeMap<String, BTreeSet<RequiredValue>>> {
    let mut values: Vec<BTreeMap<String, BTreeSet<RequiredValue>>> =
        vec![BTreeMap::new(); prepass.names.len()];
    let mut queue = VecDeque::new();
    for (owner, direct) in prepass.direct_values.iter().enumerate() {
        for (role, value) in direct {
            for effective_role in role_closure
                .get(role)
                .map(Vec::as_slice)
                .unwrap_or(std::slice::from_ref(role))
            {
                queue.push_back((owner, effective_role.clone(), value.clone()));
            }
        }
    }
    while let Some((owner, role, value)) = queue.pop_front() {
        if !values[owner]
            .entry(role.clone())
            .or_default()
            .insert(value.clone())
        {
            continue;
        }
        for &child in &children[owner] {
            queue.push_back((child, role.clone(), value.clone()));
        }
    }
    values
}

fn inherited_universals(
    prepass: &BottomPrepass,
    children: &[Vec<usize>],
) -> Vec<Vec<(String, ClassConstraint)>> {
    let mut inherited = vec![Vec::new(); prepass.names.len()];
    let mut queue = VecDeque::new();
    for (owner, direct) in prepass.universals.iter().enumerate() {
        for restriction in direct {
            queue.push_back((owner, restriction.clone()));
        }
    }
    while let Some((owner, restriction)) = queue.pop_front() {
        if inherited[owner].contains(&restriction) {
            continue;
        }
        inherited[owner].push(restriction.clone());
        for &child in &children[owner] {
            queue.push_back((child, restriction.clone()));
        }
    }
    inherited
}

fn distinct_data_pairs(
    values: &[BTreeMap<String, BTreeSet<RequiredValue>>],
) -> HashSet<(String, String)> {
    let names: Vec<String> = values
        .iter()
        .flat_map(BTreeMap::values)
        .flat_map(BTreeSet::iter)
        .filter_map(|value| match value {
            RequiredValue::Data(name) => Some(name.clone()),
            RequiredValue::Object(_) => None,
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let mut pairs = HashSet::new();
    for (index, left) in names.iter().enumerate() {
        for right in names.iter().skip(index + 1) {
            // The prepass may turn this verdict into a named-class bottom
            // certificate, so use only the deliberately narrow exact oracle.
            // It admits boolean, mathematical integer, and xsd:string values;
            // whitespace-normalised strings and IEEE float/double values stay
            // unknown rather than inheriting a lexical-inequality guess from
            // the general relation-clause generator.
            if super::datatypes::bridge_exact_value_equal(left, right) == Some(false) {
                pairs.insert(ordered_string_pair(left.clone(), right.clone()));
            }
        }
    }
    pairs
}

/// Compactly expose distinct required values to the Horn layer.  A fresh
/// marker denotes the preimage of one value on one functional role.  Every
/// source class with that has-value restriction is a marker subclass, and
/// markers for known-distinct values on the same role are disjoint.  Any model
/// of the source ontology extends to these fresh symbols, so the extension is
/// conservative over all source class names.
fn functional_value_markers(
    prepass: &BottomPrepass,
    role_closure: &HashMap<String, Vec<String>>,
    distinct_data: &HashSet<(String, String)>,
) -> (Vec<(String, String)>, Vec<(String, String)>) {
    let mut links = BTreeSet::new();
    let mut by_role: BTreeMap<String, BTreeMap<RequiredValue, String>> = BTreeMap::new();
    for (owner, requirements) in prepass.direct_values.iter().enumerate() {
        for (role, value) in requirements {
            for effective_role in role_closure
                .get(role)
                .map(Vec::as_slice)
                .unwrap_or(std::slice::from_ref(role))
            {
                if !prepass.functional.contains(effective_role) {
                    continue;
                }
                let marker = value_marker(effective_role, value);
                links.insert((prepass.names[owner].clone(), marker.clone()));
                by_role
                    .entry(effective_role.clone())
                    .or_default()
                    .entry(value.clone())
                    .or_insert(marker);
            }
        }
    }

    let mut incompatible = BTreeSet::new();
    for values in by_role.values() {
        let entries: Vec<_> = values.iter().collect();
        for (index, (left_value, left_marker)) in entries.iter().enumerate() {
            for (right_value, right_marker) in entries.iter().skip(index + 1) {
                if required_values_distinct(
                    left_value,
                    right_value,
                    distinct_data,
                    &prepass.different,
                ) {
                    incompatible.insert(ordered_string_pair(
                        (*left_marker).clone(),
                        (*right_marker).clone(),
                    ));
                }
            }
        }
    }
    (
        links.into_iter().collect(),
        incompatible.into_iter().collect(),
    )
}

fn value_marker(role: &str, value: &RequiredValue) -> String {
    let (kind, name) = match value {
        RequiredValue::Data(name) => ('d', name.as_str()),
        RequiredValue::Object(name) => ('o', name.as_str()),
    };
    format!(
        "__km_bpval__r{}:{}k{}v{}:{}",
        role.len(),
        role,
        kind,
        name.len(),
        name,
    )
}

fn required_values_distinct(
    left: &RequiredValue,
    right: &RequiredValue,
    distinct_data: &HashSet<(String, String)>,
    different: &HashSet<(String, String)>,
) -> bool {
    match (left, right) {
        (RequiredValue::Data(left), RequiredValue::Data(right)) => {
            distinct_data.contains(&ordered_string_pair(left.clone(), right.clone()))
        }
        (RequiredValue::Object(left), RequiredValue::Object(right)) => {
            different.contains(&ordered_string_pair(left.clone(), right.clone()))
        }
        _ => false,
    }
}

fn value_maps_clash<'a>(
    maps: impl IntoIterator<Item = &'a BTreeMap<String, BTreeSet<RequiredValue>>>,
    functional: &HashSet<String>,
    distinct_data: &HashSet<(String, String)>,
    different: &HashSet<(String, String)>,
) -> bool {
    let mut combined: BTreeMap<&str, BTreeSet<&RequiredValue>> = BTreeMap::new();
    for map in maps {
        for (role, values) in map {
            if functional.contains(role) {
                combined.entry(role).or_default().extend(values);
            }
        }
    }
    combined.values().any(|required| {
        required.iter().enumerate().any(|(index, left)| {
            required
                .iter()
                .skip(index + 1)
                .any(|right| required_values_distinct(left, right, distinct_data, different))
        })
    })
}

fn propagate_bottom(
    bottom: &mut [bool],
    queue: &mut VecDeque<usize>,
    dependents: &[Vec<(usize, DependencyKind)>],
    via_subclass: &mut usize,
    via_existential: &mut usize,
) {
    while let Some(empty) = queue.pop_front() {
        for &(owner, kind) in &dependents[empty] {
            if bottom[owner] {
                continue;
            }
            bottom[owner] = true;
            match kind {
                DependencyKind::Subclass => *via_subclass += 1,
                DependencyKind::Existential => *via_existential += 1,
            }
            queue.push_back(owner);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn context_impossible(
    owner: usize,
    role: &str,
    filler: usize,
    prepass: &BottomPrepass,
    constraints: &RoleConstraints,
    role_closure: &HashMap<String, Vec<String>>,
    universals: &[Vec<(String, ClassConstraint)>],
    values: &[BTreeMap<String, BTreeSet<RequiredValue>>],
    bottom: &[bool],
    distinct_data: &HashSet<(String, String)>,
) -> bool {
    let supers: Vec<String> = role_closure
        .get(role)
        .cloned()
        .unwrap_or_else(|| vec![role.to_string()]);
    let mut successor_factors: Vec<&ClassConstraint> = Vec::new();
    for super_role in &supers {
        successor_factors.extend(constraints.ranges.get(super_role).into_iter().flatten());
        for inverse in prepass.inverse_roles.get(super_role).into_iter().flatten() {
            for inverse_super in role_closure
                .get(inverse)
                .map(Vec::as_slice)
                .unwrap_or(std::slice::from_ref(inverse))
            {
                successor_factors
                    .extend(constraints.domains.get(inverse_super).into_iter().flatten());
            }
        }
    }
    for (universal_role, constraint) in &universals[owner] {
        if supers.iter().any(|candidate| candidate == universal_role) {
            successor_factors.push(constraint);
        }
    }

    all_context_branches_impossible(
        &[filler],
        &successor_factors,
        prepass,
        values,
        bottom,
        distinct_data,
    ) == Some(true)
}

/// Positive named constraints that a required edge imposes on its source.
fn owner_context_factors<'a>(
    role: &str,
    prepass: &'a BottomPrepass,
    constraints: &'a RoleConstraints,
    role_closure: &HashMap<String, Vec<String>>,
) -> Vec<&'a ClassConstraint> {
    let supers: Vec<String> = role_closure
        .get(role)
        .cloned()
        .unwrap_or_else(|| vec![role.to_string()]);
    let mut factors = Vec::new();
    for super_role in &supers {
        factors.extend(constraints.domains.get(super_role).into_iter().flatten());
        for inverse in prepass.inverse_roles.get(super_role).into_iter().flatten() {
            for inverse_super in role_closure
                .get(inverse)
                .map(Vec::as_slice)
                .unwrap_or(std::slice::from_ref(inverse))
            {
                factors.extend(constraints.ranges.get(inverse_super).into_iter().flatten());
            }
        }
    }
    factors.retain(|factor| !factor.is_top());
    factors.sort();
    factors.dedup();
    factors
}

/// `None` means the search cap was hit; `Some(None)` means every branch
/// clashed; `Some(Some(types))` is the intersection of the named-type closure
/// across every viable branch.
fn viable_context_common_types(
    owner: usize,
    factors: &[&ClassConstraint],
    prepass: &BottomPrepass,
    values: &[BTreeMap<String, BTreeSet<RequiredValue>>],
    bottom: &[bool],
    distinct_data: &HashSet<(String, String)>,
) -> Option<Option<BTreeSet<usize>>> {
    #[allow(clippy::too_many_arguments)]
    fn dfs(
        index: usize,
        factors: &[&ClassConstraint],
        selected: &mut Vec<usize>,
        visited: &mut usize,
        common: &mut Option<BTreeSet<usize>>,
        prepass: &BottomPrepass,
        values: &[BTreeMap<String, BTreeSet<RequiredValue>>],
        bottom: &[bool],
        distinct_data: &HashSet<(String, String)>,
    ) -> bool {
        *visited += 1;
        if *visited > MAX_CONTEXT_BRANCHES {
            return false;
        }
        if selected_types_clash(selected, prepass, values, bottom, distinct_data) {
            return true;
        }
        if index == factors.len() {
            let closure = type_closure(selected, prepass);
            *common = Some(match common.take() {
                None => closure,
                Some(previous) => previous.intersection(&closure).copied().collect(),
            });
            return true;
        }
        let factor = factors[index];
        for alternative in &factor.alternatives {
            let old_len = selected.len();
            for name in alternative {
                let Some(&class) = prepass.ids.get(name) else {
                    selected.truncate(old_len);
                    return false;
                };
                selected.push(class);
            }
            if !dfs(
                index + 1,
                factors,
                selected,
                visited,
                common,
                prepass,
                values,
                bottom,
                distinct_data,
            ) {
                selected.truncate(old_len);
                return false;
            }
            selected.truncate(old_len);
        }
        true
    }

    let mut selected = vec![owner];
    let mut common = None;
    let complete = dfs(
        0,
        factors,
        &mut selected,
        &mut 0,
        &mut common,
        prepass,
        values,
        bottom,
        distinct_data,
    );
    complete.then_some(common)
}

fn type_closure(initial: &[usize], prepass: &BottomPrepass) -> BTreeSet<usize> {
    let mut closure = BTreeSet::new();
    let mut queue: VecDeque<usize> = initial.iter().copied().collect();
    while let Some(class) = queue.pop_front() {
        if closure.insert(class) {
            queue.extend(prepass.supers[class].iter().copied());
        }
    }
    closure
}

fn all_context_branches_impossible(
    initial: &[usize],
    factors: &[&ClassConstraint],
    prepass: &BottomPrepass,
    values: &[BTreeMap<String, BTreeSet<RequiredValue>>],
    bottom: &[bool],
    distinct_data: &HashSet<(String, String)>,
) -> Option<bool> {
    fn dfs(
        index: usize,
        factors: &[&ClassConstraint],
        selected: &mut Vec<usize>,
        visited: &mut usize,
        prepass: &BottomPrepass,
        values: &[BTreeMap<String, BTreeSet<RequiredValue>>],
        bottom: &[bool],
        distinct_data: &HashSet<(String, String)>,
    ) -> Option<bool> {
        *visited += 1;
        if *visited > MAX_CONTEXT_BRANCHES {
            return None;
        }
        if selected_types_clash(selected, prepass, values, bottom, distinct_data) {
            return Some(true);
        }
        if index == factors.len() {
            return Some(false);
        }
        let factor = factors[index];
        if factor.alternatives.is_empty() {
            return Some(true);
        }
        for alternative in &factor.alternatives {
            let old_len = selected.len();
            for name in alternative {
                let Some(&class) = prepass.ids.get(name) else {
                    // The caller pre-registers every constraint name. Unknown is
                    // still fail-closed if malformed metadata reaches here.
                    selected.truncate(old_len);
                    return None;
                };
                selected.push(class);
            }
            match dfs(
                index + 1,
                factors,
                selected,
                visited,
                prepass,
                values,
                bottom,
                distinct_data,
            ) {
                Some(true) => {}
                Some(false) => {
                    selected.truncate(old_len);
                    return Some(false);
                }
                None => {
                    selected.truncate(old_len);
                    return None;
                }
            }
            selected.truncate(old_len);
        }
        Some(true)
    }

    let mut selected = initial.to_vec();
    dfs(
        0,
        factors,
        &mut selected,
        &mut 0,
        prepass,
        values,
        bottom,
        distinct_data,
    )
}

fn selected_types_clash(
    selected: &[usize],
    prepass: &BottomPrepass,
    values: &[BTreeMap<String, BTreeSet<RequiredValue>>],
    bottom: &[bool],
    distinct_data: &HashSet<(String, String)>,
) -> bool {
    let mut closure = BTreeSet::new();
    let mut queue: VecDeque<usize> = selected.iter().copied().collect();
    while let Some(class) = queue.pop_front() {
        if !closure.insert(class) {
            continue;
        }
        if bottom[class] {
            return true;
        }
        queue.extend(prepass.supers[class].iter().copied());
    }
    let types: Vec<usize> = closure.into_iter().collect();
    if types.iter().enumerate().any(|(index, left)| {
        types.iter().skip(index + 1).any(|right| {
            prepass
                .disjoint
                .contains(&ordered_usize_pair(*left, *right))
        })
    }) {
        return true;
    }
    value_maps_clash(
        types.iter().map(|&class| &values[class]),
        &prepass.functional,
        distinct_data,
        &prepass.different,
    )
}

fn ordered_usize_pair(left: usize, right: usize) -> (usize, usize) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

fn ordered_string_pair(left: String, right: String) -> (String, String) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

/// Compatibility helper for callers/tests that need only the source-AST part.
pub fn certified_bottom(ontology: &Ontology) -> BottomPrepassResult {
    BottomPrepass::from_ontology(ontology).certify(&RoleConstraints::default())
}

/// Convert a certified closure to ordinary DL constraints. This does not add a
/// reasoner rule; it only materializes consequences proved by this prepass.
pub(crate) fn constraints(result: &BottomPrepassResult) -> Vec<DLClause> {
    let mut out = Vec::with_capacity(
        result.classes.len()
            + result.forced_subclasses.len()
            + result.value_markers.len()
            + result.incompatible_pairs.len(),
    );
    out.extend(result.classes.iter().map(|name| {
        super::clauses::constraint([Atom::Concept(name.clone(), super::clauses::var_x())])
    }));
    out.extend(result.forced_subclasses.iter().map(|(child, parent)| {
        super::clauses::clause(
            [Atom::Concept(child.clone(), super::clauses::var_x())],
            [Atom::Concept(parent.clone(), super::clauses::var_x())],
        )
    }));
    out.extend(result.value_markers.iter().map(|(child, marker)| {
        super::clauses::clause(
            [Atom::Concept(child.clone(), super::clauses::var_x())],
            [Atom::Concept(marker.clone(), super::clauses::var_x())],
        )
    }));
    out.extend(result.incompatible_pairs.iter().map(|(left, right)| {
        super::clauses::constraint([
            Atom::Concept(left.clone(), super::clauses::var_x()),
            Atom::Concept(right.clone(), super::clauses::var_x()),
        ])
    }));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{iri::IriRegistry, parse, sexpr};

    fn parse_prepass(body: &str) -> (BottomPrepass, IriRegistry) {
        let text = format!("Ontology({body})");
        let mut registry = IriRegistry::new();
        let ontology = parse::parse_axioms(&mut registry, &text).unwrap();
        (BottomPrepass::from_ontology(&ontology), registry)
    }

    fn run(body: &str) -> BottomPrepassResult {
        let (prepass, _) = parse_prepass(body);
        prepass.certify(&RoleConstraints::default())
    }

    fn role_constraints(texts: &[&str], registry: &mut IriRegistry) -> RoleConstraints {
        let mut raw = RawRoleConstraints::default();
        for text in texts {
            raw.observe(&sexpr::Parser::new(text).parse().unwrap());
        }
        raw.resolve(registry)
    }

    #[test]
    fn functional_boolean_clash_propagates_through_subclass_and_exists() {
        let result = run(r#"
            FunctionalDataProperty(<http://x/p>)
            SubClassOf(<http://x/True> DataHasValue(<http://x/p> "true"^^xsd:boolean))
            SubClassOf(<http://x/False> DataHasValue(<http://x/p> "false"^^xsd:boolean))
            SubClassOf(<http://x/Bad> <http://x/True>)
            SubClassOf(<http://x/Bad> <http://x/False>)
            SubClassOf(<http://x/Owner> ObjectSomeValuesFrom(<http://x/r> <http://x/Bad>))
            SubClassOf(<http://x/OwnerChild> <http://x/Owner>)
            EquivalentClasses(<http://x/EqOwner> ObjectIntersectionOf(
                <http://x/Anchor>
                ObjectSomeValuesFrom(<http://x/r> <http://x/Bad>)))
            "#);
        let names: BTreeSet<_> = result.classes.iter().map(String::as_str).collect();
        assert_eq!(result.seeds, 1);
        assert!(names.contains("Bad"));
        assert!(names.contains("Owner"));
        assert!(names.contains("OwnerChild"));
        assert!(names.contains("EqOwner"));
        assert_eq!(result.via_subclass, 1);
        assert_eq!(result.via_existential, 2);
    }

    #[test]
    fn equal_boolean_lexical_forms_and_nonfunctional_values_do_not_clash() {
        let equal = run(r#"
            FunctionalDataProperty(<http://x/p>)
            SubClassOf(<http://x/A> DataHasValue(<http://x/p> "true"^^xsd:boolean))
            SubClassOf(<http://x/A> DataHasValue(<http://x/p> "1"^^xsd:boolean))
            "#);
        assert!(equal.classes.is_empty());

        let nonfunctional = run(r#"
            SubClassOf(<http://x/A> DataHasValue(<http://x/p> "true"^^xsd:boolean))
            SubClassOf(<http://x/A> DataHasValue(<http://x/p> "false"^^xsd:boolean))
            "#);
        assert!(nonfunctional.classes.is_empty());
    }

    #[test]
    fn lossy_datatype_lexicals_do_not_create_bottom_certificates() {
        let token = run(r#"
            FunctionalDataProperty(<http://x/p>)
            SubClassOf(<http://x/A> DataHasValue(<http://x/p> "a  b"^^xsd:token))
            SubClassOf(<http://x/A> DataHasValue(<http://x/p> "a b"^^xsd:string))
            "#);
        assert!(
            token.classes.is_empty(),
            "xsd:token whitespace collapse makes the values equal: {token:#?}"
        );

        let float = run(r#"
            FunctionalDataProperty(<http://x/p>)
            SubClassOf(<http://x/A> DataHasValue(<http://x/p> "16777216"^^xsd:float))
            SubClassOf(<http://x/A> DataHasValue(<http://x/p> "16777217"^^xsd:float))
            "#);
        assert!(
            float.classes.is_empty(),
            "both values round to 2^24 in IEEE binary32: {float:#?}"
        );
    }

    #[test]
    fn exact_integer_and_string_values_still_seed_bottom() {
        let result = run(r#"
            FunctionalDataProperty(<http://x/integerProperty>)
            FunctionalDataProperty(<http://x/stringProperty>)
            SubClassOf(<http://x/BadInteger> DataHasValue(<http://x/integerProperty> "1"^^xsd:integer))
            SubClassOf(<http://x/BadInteger> DataHasValue(<http://x/integerProperty> "2"^^xsd:integer))
            SubClassOf(<http://x/BadString> DataHasValue(<http://x/stringProperty> "alpha"^^xsd:string))
            SubClassOf(<http://x/BadString> DataHasValue(<http://x/stringProperty> "beta"^^xsd:string))
            "#);
        let classes: BTreeSet<_> = result.classes.iter().map(String::as_str).collect();
        assert!(classes.contains("BadInteger"), "{result:#?}");
        assert!(classes.contains("BadString"), "{result:#?}");
        assert_eq!(result.seeds, 2);
    }

    #[test]
    fn inverse_domain_can_make_a_required_successor_impossible() {
        let (prepass, mut registry) = parse_prepass(
            r#"
            FunctionalObjectProperty(<http://x/dimension>)
            DifferentIndividuals(<http://x/d2> <http://x/d3>)
            SubClassOf(<http://x/Space> ObjectHasValue(<http://x/dimension> <http://x/d3>))
            SubClassOf(<http://x/Surface> ObjectHasValue(<http://x/dimension> <http://x/d2>))
            InverseObjectProperties(<http://x/part> <http://x/partOf>)
            SubClassOf(<http://x/Root> ObjectSomeValuesFrom(<http://x/part> <http://x/Space>))
            "#,
        );
        let constraints = role_constraints(
            &["ObjectPropertyDomain(<http://x/partOf> <http://x/Surface>)"],
            &mut registry,
        );
        let result = prepass.certify(&constraints);
        assert!(result.classes.iter().any(|name| name == "Root"));
        assert!(!result.classes.iter().any(|name| name == "Space"));
        assert!(!result.classes.iter().any(|name| name == "Surface"));
        assert_eq!(result.contextual_roots, 1);
    }

    #[test]
    fn union_range_requires_every_alternative_to_clash() {
        let ontology = |include_point: bool| {
            let (prepass, mut registry) = parse_prepass(
                r#"
                FunctionalDataProperty(<http://x/mass>)
                SubClassOf(<http://x/Point> DataHasValue(<http://x/mass> "false"^^xsd:boolean))
                SubClassOf(<http://x/Mat1> DataHasValue(<http://x/mass> "true"^^xsd:boolean))
                SubClassOf(<http://x/Mat2> DataHasValue(<http://x/mass> "1"^^xsd:boolean))
                SubClassOf(<http://x/Root> ObjectSomeValuesFrom(<http://x/related> <http://x/Point>))
                "#,
            );
            let range = if include_point {
                "ObjectPropertyRange(<http://x/related> ObjectUnionOf(<http://x/Mat1> <http://x/Mat2> <http://x/Point>))"
            } else {
                "ObjectPropertyRange(<http://x/related> ObjectUnionOf(<http://x/Mat1> <http://x/Mat2>))"
            };
            let constraints = role_constraints(&[range], &mut registry);
            prepass.certify(&constraints)
        };
        assert!(ontology(false).classes.iter().any(|name| name == "Root"));
        assert!(!ontology(true).classes.iter().any(|name| name == "Root"));
    }

    #[test]
    fn inherited_universal_participates_in_successor_clash() {
        let (prepass, mut registry) = parse_prepass(
            r#"
            FunctionalDataProperty(<http://x/mass>)
            SubClassOf(<http://x/Material> DataHasValue(<http://x/mass> "true"^^xsd:boolean))
            SubClassOf(<http://x/NonMaterial> DataHasValue(<http://x/mass> "false"^^xsd:boolean))
            SubClassOf(<http://x/Bad> DataHasValue(<http://x/mass> "true"^^xsd:boolean))
            SubClassOf(<http://x/Bad> DataHasValue(<http://x/mass> "false"^^xsd:boolean))
            SubClassOf(<http://x/Parent> ObjectAllValuesFrom(<http://x/r> ObjectUnionOf(<http://x/NonMaterial> <http://x/Bad>)))
            SubClassOf(<http://x/Root> <http://x/Parent>)
            SubClassOf(<http://x/Root> ObjectSomeValuesFrom(<http://x/r> <http://x/Filler>))
            "#,
        );
        let constraints = role_constraints(
            &["ObjectPropertyRange(<http://x/r> <http://x/Material>)"],
            &mut registry,
        );
        let result = prepass.certify(&constraints);
        assert!(result.classes.iter().any(|name| name == "Root"));
    }

    #[test]
    fn inverse_range_alternatives_force_the_only_viable_owner_type() {
        let (prepass, mut registry) = parse_prepass(
            r#"
            FunctionalDataProperty(<http://x/has_mass>)
            SubClassOf(<http://x/Material> DataHasValue(<http://x/has_mass> "true"^^xsd:boolean))
            SubClassOf(<http://x/Cavity> DataHasValue(<http://x/has_mass> "false"^^xsd:boolean))
            SubClassOf(<http://x/DeadOrgan> DataHasValue(<http://x/has_mass> "true"^^xsd:boolean))
            SubClassOf(<http://x/DeadOrgan> DataHasValue(<http://x/has_mass> "false"^^xsd:boolean))
            SubClassOf(<http://x/Owner> <http://x/Material>)
            InverseObjectProperties(<http://x/part> <http://x/partOf>)
            SubClassOf(<http://x/Owner> ObjectSomeValuesFrom(<http://x/part> <http://x/Filler>))
            "#,
        );
        let constraints = role_constraints(
            &["ObjectPropertyRange(<http://x/partOf> ObjectUnionOf(<http://x/Cavity> <http://x/DeadOrgan> <http://x/Forced>))"],
            &mut registry,
        );
        let result = prepass.certify(&constraints);
        assert!(result.classes.iter().any(|name| name == "DeadOrgan"));
        assert!(result
            .forced_subclasses
            .iter()
            .any(|(child, parent)| child == "Owner" && parent == "Forced"));
        assert!(result.incompatible_pairs.iter().any(|(left, right)| {
            (left == "Cavity" && right == "Owner") || (left == "Owner" && right == "Cavity")
        }));
        assert!(!result.classes.iter().any(|name| name == "Owner"));
    }

    #[test]
    fn functional_values_are_materialized_as_disjoint_horn_markers() {
        let result = run(r#"
            FunctionalDataProperty(<http://x/mass>)
            SubClassOf(<http://x/TrueCarrier> DataHasValue(<http://x/mass> "true"^^xsd:boolean))
            SubClassOf(<http://x/FalseCarrier> DataHasValue(<http://x/mass> "false"^^xsd:boolean))
            "#);
        assert_eq!(result.value_markers.len(), 2);
        assert_eq!(result.incompatible_pairs.len(), 1);

        let materialized = constraints(&result);
        for (owner, marker) in &result.value_markers {
            let expected = super::super::clauses::clause(
                [Atom::Concept(owner.clone(), super::super::clauses::var_x())],
                [Atom::Concept(
                    marker.clone(),
                    super::super::clauses::var_x(),
                )],
            );
            assert!(materialized.contains(&expected));
        }
    }
}
