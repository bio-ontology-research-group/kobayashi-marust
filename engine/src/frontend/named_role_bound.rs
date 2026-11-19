//! Sound upper bound on named-individual object-property pairs in forest models.
//!
//! For an ontology `O` without `SameIndividual`, `HasKey`, non-tautological uses
//! of `owl:topObjectProperty`, positive nominals (outside closed value-partition
//! definitions whose defined class never occurs positively elsewhere, and query
//! probe definitions in `http://km.invalid/`), or positive `ObjectMaxCardinality`
//! / `ObjectExactCardinality` with bound >= 1, every consistent model can be
//! forest-unravelled from the named individuals `N` so that anonymous existential
//! witnesses never merge with named individuals or connect two distinct named
//! individuals. The object-property pairs `(r, a, b)` over `a, b in N` are then
//! bounded above by the least fixpoint `E+` of:
//! - explicit `ObjectPropertyAssertion(r, a, b)` facts;
//! - universal diagonal self-loops `(r, a, a)` (`a in N`) from `ReflexiveRole(r)`,
//!   positive `ObjectHasSelf(r)`, and tree-folding `RoleChain`s whose steps can
//!   traverse an anonymous tree edge and its inverse back to the same root `a`;
//! - closure under `RoleInclusion`, `InverseRoles`, `SymmetricRole`,
//!   `TransitiveRole`, `RoleChain`, and the `ObjectPropertyAtom` projection of
//!   `DLSafeRule`s.
//! If any `FunctionalRole` or `InverseFunctionalRole` would equate two distinct
//! named individuals in `E+`, the bound declines (`None`).

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::{Arc, Mutex};

use super::iri::IriRegistry;
use super::rbox::{RawRbox, RboxRecord};
use super::sexpr::Node;
use super::syntax::{ mk_and, Axiom, Concept, Role, RuleAtom, RuleTerm };

#[derive(Clone, Debug)]
pub struct NamedRoleBound {
    /// Named individuals (short names in the parser's `IriRegistry`).
    pub named: BTreeSet<String>,
    /// Map from short name to full IRI (without angle brackets).
    pub full_iris: BTreeMap<String, String>,
    /// Map from full IRI (without angle brackets) to short name.
    pub short_of_full: BTreeMap<String, String>,
    /// Off-diagonal or explicit pairs `(a, b)` per short role name `r`.
    pub edges: BTreeMap<String, BTreeSet<(String, String)>>,
    /// Reverse pairs `(b, a)` per short role name `r`.
    pub rev_edges: BTreeMap<String, BTreeSet<(String, String)>>,
    /// Wildcard-source targets `b` (`(*, b) in r`) per short role name `r`.
    pub w_src: BTreeMap<String, BTreeSet<String>>,
    /// Wildcard-target sources `a` (`(a, *) in r`) per short role name `r`.
    pub w_dst: BTreeMap<String, BTreeSet<String>>,
    /// Short role names `r` with universal target reachability `(*, *)`.
    pub universal_roles: BTreeSet<String>,
    /// Short role names `r` that hold on the diagonal `(a, a)` for all `a in N`.
    pub self_roles: BTreeSet<String>,
    /// Whether the strict forest precondition for DL-safe rule grounding holds
    /// (no `SameIndividual`, `ObjectHasValue`, `AtMost >= 1`, or role merges).
    pub forest_exact_for_rules: bool,
    /// Whether `ObjectHasSelf` already occurs in the source ontology.
    pub has_self_in_source: bool,
    /// Closed value-partition classes `v -> {a_1, ..., a_k}` (short names).
    pub vp_classes: BTreeMap<String, BTreeSet<String>>,
    /// Exact data property assertions `(short_prop, identity_key) -> {short_ind}`
    /// when the ontology has no existential data value generators.
    pub exact_data_values: Option<BTreeMap<(String, String), BTreeSet<String>>>,
    /// Entailed positive role assertions `(r, a, b)` that hold in every model.
    pub entailed_roles: BTreeSet<(String, String, String)>,
    /// Entailed positive atomic class assertions `(c, a)` that hold in every model.
    pub entailed_classes: BTreeSet<(String, String)>,
}

struct Equiv {
    parent: BTreeMap<String, String>,
    num_merges: usize,
}

impl Equiv {
    fn new() -> Self {
        Self {
            parent: BTreeMap::new(),
            num_merges: 0,
        }
    }

    fn find(&mut self, x: &str) -> String {
        let Some(p) = self.parent.get(x).cloned() else {
            self.parent.insert(x.to_owned(), x.to_owned());
            return x.to_owned();
        };
        if p == x {
            return p;
        }
        let root = self.find(&p);
        self.parent.insert(x.to_owned(), root.clone());
        root
    }

    fn union(&mut self, a: &str, b: &str) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        if ra < rb {
            self.parent.insert(rb, ra);
        } else {
            self.parent.insert(ra, rb);
        }
        self.num_merges += 1;
        true
    }

    fn multi_member_map(&mut self) -> Option<BTreeMap<String, Vec<String>>> {
        let keys: Vec<String> = self.parent.keys().cloned().collect();
        let mut groups: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for k in keys {
            let r = self.find(&k);
            groups.entry(r).or_default().push(k);
        }
        let mut out = BTreeMap::new();
        for (_, members) in groups {
            if members.len() > 256 {
                return None;
            }
            if members.len() >= 2 {
                for m in &members {
                    out.insert(m.clone(), members.clone());
                }
            }
        }
        Some(out)
    }
}

fn is_universal_role_token(token: &str) -> bool {
    matches!(
        token,
        "owl:topObjectProperty" | "<http://www.w3.org/2002/07/owl#topObjectProperty>"
    )
}

fn mentions_universal_role(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(token) => is_universal_role_token(token),
        Node::List("Annotation", _) => false,
        Node::List(_, args) => args.iter().any(mentions_universal_role),
    }
}

fn mentions_disqualifying_construct(node: &Node<'_>, data_gen: &mut bool) -> bool {
    let Node::List(head, args) = node else {
        return matches!(node, Node::Atom(token) if is_universal_role_token(token));
    };
    match *head {
        "Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
        | "AnnotationPropertyDomain" | "AnnotationPropertyRange" | "Declaration" => return false,
        "HasKey" => return true,
        "SubDataPropertyOf" | "EquivalentDataProperties" => {
            *data_gen = true;
            return false;
        }
        "EquivalentClasses" => {
            let plain: Vec<&Node<'_>> =
                args.iter().filter(|arg| arg.head() != Some("Annotation")).collect();
            if let Some(Node::Atom(first)) = plain.first() {
                if first.starts_with("<http://km.invalid/") {
                    return false;
                }
            }
        }
        "DataSomeValuesFrom" | "DataMinCardinality" | "DataExactCardinality" => {
            *data_gen = true;
        }
        "SubObjectPropertyOf" => {
            let plain: Vec<&Node<'_>> =
                args.iter().filter(|arg| arg.head() != Some("Annotation")).collect();
            if let [sub, Node::Atom(sup)] = plain.as_slice() {
                if is_universal_role_token(sup) && !mentions_universal_role(sub) {
                    return false;
                }
            }
            return args.iter().any(|a| mentions_disqualifying_construct(a, data_gen));
        }
        _ => {}
    }
    args.iter().any(|a| mentions_disqualifying_construct(a, data_gen))
}

fn extract_nominal_union(concept: &Concept, named: &BTreeSet<String>) -> Option<BTreeSet<String>> {
    match concept {
        Concept::Nominal(a) if named.contains(a) => Some(BTreeSet::from([a.clone()])),
        Concept::Or(cs) if !cs.is_empty() => {
            let mut out = BTreeSet::new();
            for c in cs {
                let Concept::Nominal(a) = c else { return None };
                if !named.contains(a) {
                    return None;
                }
                out.insert(a.clone());
            }
            Some(out)
        }
        _ => None,
    }
}

fn literal_identity_key(literal: &str) -> Option<String> {
    super::datatypes::bridge_value_identity_key(&format!("__dt__val__{literal}"))
        .or_else(|| super::data_rules::exact_rule_literal(literal).then(|| literal.to_owned()))
}

static CACHED_ROLE_BOUND: Mutex<Option<(Arc<str>, Option<NamedRoleBound>)>> = Mutex::new(None);

impl NamedRoleBound {
    pub fn bound_disabled() -> bool {
        std::env::var("KM_DISABLE_NAMED_ROLE_BOUND")
            .ok()
            .is_some_and(|v| matches!(v.trim(), "1" | "true" | "TRUE" | "yes" | "YES"))
            || std::env::var("KM_NAMED_ROLE_BOUND")
                .ok()
                .is_some_and(|v| matches!(v.trim(), "0" | "false" | "FALSE" | "no" | "NO" | "off" | "OFF"))
    }

    pub fn compute(text: &str) -> Option<Self> {
        if Self::bound_disabled() {
            return None;
        }
        if text.len() <= 16 * 1024 * 1024 {
            if let Some((_, cached)) = CACHED_ROLE_BOUND
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .as_ref()
                .filter(|(src, _)| &**src == text)
            {
                return cached.clone();
            }
        }
        let result = Self::compute_uncached(text);
        if text.len() <= 16 * 1024 * 1024 {
            *CACHED_ROLE_BOUND.lock().unwrap_or_else(|e| e.into_inner()) =
                Some((Arc::from(text), result.clone()));
        }
        result
    }

    fn compute_uncached(text: &str) -> Option<Self> {
        let mut has_disqualifying = false;
        let mut data_gen = false;
        let mut raw_rbox = RawRbox::default();
        let mut profile = super::profile::SourceProfileBuilder::new();
        let mut raw_data_assertions: Vec<(String, String, String)> = Vec::new();
        let mut registry = IriRegistry::new();
        let mut ontology = super::parse::parse_axioms_observed(&mut registry, text, |node| {
            if mentions_disqualifying_construct(node, &mut data_gen) {
                has_disqualifying = true;
            }
            raw_rbox.observe(node);
            profile.observe(node);
            if let Node::List("DataPropertyAssertion", args) = node {
                let plain = super::parse::strip_annotations(args);
                if let (Some(prop), Some(ind), Some((lit, used))) = (
                    plain.first().and_then(|n| n.as_atom()),
                    plain.get(1).and_then(|n| n.as_atom()),
                    super::parse::glue_literal(&plain, 2),
                ) {
                    if plain.len() == 2 + used && !ind.starts_with("_:") {
                        raw_data_assertions.push((prop.to_owned(), ind.to_owned(), lit));
                    } else {
                        data_gen = true;
                    }
                } else {
                    data_gen = true;
                }
            } else if matches!(node.head(), Some("NegativeDataPropertyAssertion")) {
                data_gen = true;
            }
        }).ok()?;
        if has_disqualifying || !ontology.dropped_source_axioms().is_empty() {
            return None;
        }
        let rbox = raw_rbox.resolve(&mut registry);
        let mut named: BTreeSet<String> = profile
            .rule_individual_names()
            .into_iter()
            .map(|n| registry.short(n))
            .collect();
        if named.is_empty() {
            if let Ok(inds) = crate::orchestrate::realize::source_individuals(text) {
                for raw in inds {
                    if !raw.starts_with("_:") {
                        named.insert(registry.short(&raw));
                    }
                }
            }
        }
        for op in profile.object_property_names() {
            registry.short(op);
        }
        let mut full_iris = BTreeMap::new();
        let mut short_of_full = BTreeMap::new();
        for short in registry.owned_names() {
            let full = registry.full_iri(&short).to_owned();
            short_of_full.insert(full.clone(), short.clone());
            full_iris.insert(short, full);
        }

        let is_probe_class = |name: &str| -> bool {
            full_iris
                .get(name)
                .is_some_and(|iri| iri.starts_with("http://km.invalid/"))
        };

        // Pass 1: identify probe axioms and value-partition candidate classes.
        let all_axioms: Vec<&Axiom> = ontology.axioms_iter().collect();
        let mut skip_axiom = vec![false; all_axioms.len()];
        let mut vp_classes: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut probe_occurrences: BTreeMap<String, usize> = BTreeMap::new();

        fn count_probes(c: &Concept, is_probe: &impl Fn(&str) -> bool, out: &mut BTreeMap<String, usize>) {
            match c {
                Concept::Name(n) if is_probe(n) => *out.entry(n.clone()).or_default() += 1,
                Concept::Not(inner)
                | Concept::Exists(_, inner)
                | Concept::Forall(_, inner)
                | Concept::AtLeast(_, _, inner)
                | Concept::AtMost(_, _, inner) => count_probes(inner, is_probe, out),
                Concept::And(cs) | Concept::Or(cs) => {
                    for d in cs {
                        count_probes(d, is_probe, out);
                    }
                }
                _ => {}
            }
        }
        for ax in &all_axioms {
            match ax {
                Axiom::SubClassOf(a, b) | Axiom::EquivalentClasses(a, b) | Axiom::DisjointClasses(a, b) => {
                    count_probes(a, &is_probe_class, &mut probe_occurrences);
                    count_probes(b, &is_probe_class, &mut probe_occurrences);
                }
                Axiom::ConceptAssertion(c, _) => count_probes(c, &is_probe_class, &mut probe_occurrences),
                Axiom::Rule(body, head) | Axiom::DataRule(body, head) => {
                    for atom in body.iter().chain(head) {
                        if let RuleAtom::Class(c, _) = atom {
                            count_probes(c, &is_probe_class, &mut probe_occurrences);
                        }
                    }
                }
                _ => {}
            }
        }

        for (idx, ax) in all_axioms.iter().enumerate() {
            match ax {
                Axiom::EquivalentClasses(Concept::Name(c), rhs)
                    if is_probe_class(c) && probe_occurrences.get(c).copied() == Some(1) =>
                {
                    let mut rhs_probes = BTreeMap::new();
                    count_probes(rhs, &is_probe_class, &mut rhs_probes);
                    if rhs_probes
                        .keys()
                        .all(|p| full_iris.get(p).is_some_and(|iri| iri.ends_with("#filler")))
                    {
                        skip_axiom[idx] = true;
                        continue;
                    }
                }
                Axiom::EquivalentClasses(Concept::Name(c), rhs)
                | Axiom::EquivalentClasses(rhs, Concept::Name(c))
                    if !is_probe_class(c) =>
                {
                    if let Some(members) = extract_nominal_union(rhs, &named) {
                        vp_classes.entry(c.clone()).or_default().extend(members);
                        skip_axiom[idx] = true;
                    }
                }
                Axiom::SubClassOf(Concept::Name(c), rhs) if !is_probe_class(c) => {
                    if let Some(members) = extract_nominal_union(rhs, &named) {
                        vp_classes.entry(c.clone()).or_default().extend(members);
                        skip_axiom[idx] = true;
                    }
                }
                _ => {}
            }
        }

        let data_prop_shorts: BTreeSet<String> = profile
            .data_property_names()
            .into_iter()
            .map(|n| registry.short(n))
            .collect();

        // Pass 2: walk concept polarities across all remaining axioms.
        let mut pos_classes: BTreeSet<String> = BTreeSet::new();
        let mut has_self_roles: BTreeSet<String> = BTreeSet::new();
        let mut has_self_in_source = false;
        let mut forest_exact_for_rules = true;
        let mut w_src: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut w_dst: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut card_functional: BTreeSet<String> = BTreeSet::new();
        let mut card_inv_functional: BTreeSet<String> = BTreeSet::new();
        let mut pos_existential_roles: BTreeSet<String> = BTreeSet::new();
        let mut inv_existential_roles: BTreeSet<String> = BTreeSet::new();
        let mut same_pairs: Vec<(String, String)> = Vec::new();

        #[allow(clippy::too_many_arguments)]
        fn walk_concept(
            c: &Concept,
            pos: bool,
            neg: bool,
            data_props: &BTreeSet<String>,
            pos_classes: &mut BTreeSet<String>,
            has_self_roles: &mut BTreeSet<String>,
            has_self_in_source: &mut bool,
            data_gen: &mut bool,
            forest_exact_for_rules: &mut bool,
            w_src: &mut BTreeMap<String, BTreeSet<String>>,
            w_dst: &mut BTreeMap<String, BTreeSet<String>>,
            card_functional: &mut BTreeSet<String>,
            card_inv_functional: &mut BTreeSet<String>,
            pos_existential_roles: &mut BTreeSet<String>,
            inv_existential_roles: &mut BTreeSet<String>,
        ) -> Result<(), ()> {
            match c {
                Concept::Name(n) => {
                    if pos {
                        pos_classes.insert(n.clone());
                    }
                    Ok(())
                }
                Concept::Top | Concept::Bottom => Ok(()),
                Concept::Nominal(a) => {
                    if a.starts_with("_:") || pos {
                        Err(())
                    } else {
                        Ok(())
                    }
                }
                Concept::Not(inner) => walk_concept(
                    inner,
                    neg,
                    pos,
                    data_props,
                    pos_classes,
                    has_self_roles,
                    has_self_in_source,
                    data_gen,
                    forest_exact_for_rules,
                    w_src,
                    w_dst,
                    card_functional,
                    card_inv_functional,
                    pos_existential_roles,
                    inv_existential_roles,
                ),
                Concept::And(cs) | Concept::Or(cs) => {
                    for d in cs {
                        walk_concept(
                            d,
                            pos,
                            neg,
                            data_props,
                            pos_classes,
                            has_self_roles,
                            has_self_in_source,
                            data_gen,
                            forest_exact_for_rules,
                            w_src,
                            w_dst,
                            card_functional,
                            card_inv_functional,
                            pos_existential_roles,
                            inv_existential_roles,
                        )?;
                    }
                    Ok(())
                }
                Concept::Exists(r, filler) => {
                    match r {
                        Role::Universal => return Err(()),
                        Role::Name(rn) if data_props.contains(rn) => {
                            if pos {
                                *data_gen = true;
                            }
                            return walk_concept(
                                filler,
                                pos,
                                neg,
                                data_props,
                                pos_classes,
                                has_self_roles,
                                has_self_in_source,
                                data_gen,
                                forest_exact_for_rules,
                                w_src,
                                w_dst,
                                card_functional,
                                card_inv_functional,
                                pos_existential_roles,
                                inv_existential_roles,
                            );
                        }
                        _ => {}
                    }
                    if let Concept::Nominal(b) = filler.as_ref() {
                        if b.starts_with("_:") {
                            return Err(());
                        }
                        *forest_exact_for_rules = false;
                        if pos {
                            match r {
                                Role::Name(rn) => {
                                    w_src.entry(rn.clone()).or_default().insert(b.clone());
                                }
                                Role::Inverse(rn) => {
                                    w_dst.entry(rn.clone()).or_default().insert(b.clone());
                                }
                                Role::Universal => return Err(()),
                            }
                        }
                        return Ok(());
                    }
                    if pos {
                        match r {
                            Role::Name(rn) => {
                                pos_existential_roles.insert(rn.clone());
                            }
                            Role::Inverse(rn) => {
                                inv_existential_roles.insert(rn.clone());
                            }
                            Role::Universal => return Err(()),
                        }
                    }
                    walk_concept(
                        filler,
                        pos,
                        neg,
                        data_props,
                        pos_classes,
                        has_self_roles,
                        has_self_in_source,
                        data_gen,
                        forest_exact_for_rules,
                        w_src,
                        w_dst,
                        card_functional,
                        card_inv_functional,
                        pos_existential_roles,
                        inv_existential_roles,
                    )
                }
                Concept::Forall(r, filler) => {
                    match r {
                        Role::Universal => return Err(()),
                        Role::Name(rn) if data_props.contains(rn) => {
                            if neg {
                                *data_gen = true;
                            }
                        }
                        Role::Name(rn) if neg => {
                            pos_existential_roles.insert(rn.clone());
                        }
                        Role::Inverse(rn) if neg => {
                            inv_existential_roles.insert(rn.clone());
                        }
                        _ => {}
                    }
                    walk_concept(
                        filler,
                        pos,
                        neg,
                        data_props,
                        pos_classes,
                        has_self_roles,
                        has_self_in_source,
                        data_gen,
                        forest_exact_for_rules,
                        w_src,
                        w_dst,
                        card_functional,
                        card_inv_functional,
                        pos_existential_roles,
                        inv_existential_roles,
                    )
                }
                Concept::AtLeast(n, r, filler) => {
                    let is_data = match r {
                        Role::Universal => return Err(()),
                        Role::Name(rn) => data_props.contains(rn),
                        Role::Inverse(_) => false,
                    };
                    if is_data && pos && *n >= 1 {
                        *data_gen = true;
                    }
                    if !is_data && pos && *n >= 1 {
                        match r {
                            Role::Name(rn) => {
                                pos_existential_roles.insert(rn.clone());
                            }
                            Role::Inverse(rn) => {
                                inv_existential_roles.insert(rn.clone());
                            }
                            Role::Universal => return Err(()),
                        }
                    }
                    if !is_data && neg && *n >= 2 {
                        if *n >= 3 {
                            *forest_exact_for_rules = false;
                        }
                        match r {
                            Role::Name(rn) => {
                                card_functional.insert(rn.clone());
                            }
                            Role::Inverse(rn) => {
                                card_inv_functional.insert(rn.clone());
                            }
                            Role::Universal => return Err(()),
                        }
                    }
                    if *n > 0 {
                        walk_concept(
                            filler,
                            pos,
                            neg,
                            data_props,
                            pos_classes,
                            has_self_roles,
                            has_self_in_source,
                            data_gen,
                            forest_exact_for_rules,
                            w_src,
                            w_dst,
                            card_functional,
                            card_inv_functional,
                            pos_existential_roles,
                            inv_existential_roles,
                        )
                    } else {
                        Ok(())
                    }
                }
                Concept::AtMost(n, r, filler) => {
                    let is_data = match r {
                        Role::Universal => return Err(()),
                        Role::Name(rn) => data_props.contains(rn),
                        Role::Inverse(_) => false,
                    };
                    if is_data && neg {
                        *data_gen = true;
                    }
                    if !is_data && pos && *n >= 1 {
                        if *n >= 2 {
                            *forest_exact_for_rules = false;
                        }
                        match r {
                            Role::Name(rn) => {
                                card_functional.insert(rn.clone());
                            }
                            Role::Inverse(rn) => {
                                card_inv_functional.insert(rn.clone());
                            }
                            Role::Universal => return Err(()),
                        }
                    }
                    if !is_data && neg && *n >= 0 {
                        match r {
                            Role::Name(rn) => {
                                pos_existential_roles.insert(rn.clone());
                            }
                            Role::Inverse(rn) => {
                                inv_existential_roles.insert(rn.clone());
                            }
                            Role::Universal => return Err(()),
                        }
                    }
                    walk_concept(
                        filler,
                        neg,
                        pos,
                        data_props,
                        pos_classes,
                        has_self_roles,
                        has_self_in_source,
                        data_gen,
                        forest_exact_for_rules,
                        w_src,
                        w_dst,
                        card_functional,
                        card_inv_functional,
                        pos_existential_roles,
                        inv_existential_roles,
                    )
                }
                Concept::HasSelf(r) => match r {
                    Role::Name(n) | Role::Inverse(n) => {
                        *has_self_in_source = true;
                        if pos {
                            has_self_roles.insert(n.clone());
                        }
                        Ok(())
                    }
                    Role::Universal => Err(()),
                },
            }
        }

        fn concept_mentions_class(c: &Concept, target: &str) -> bool {
            match c {
                Concept::Name(n) => n == target,
                Concept::Not(inner)
                | Concept::Exists(_, inner)
                | Concept::Forall(_, inner)
                | Concept::AtLeast(_, _, inner)
                | Concept::AtMost(_, _, inner) => concept_mentions_class(inner, target),
                Concept::And(cs) | Concept::Or(cs) => cs.iter().any(|d| concept_mentions_class(d, target)),
                _ => false,
            }
        }

        let mut equiv_def_count: BTreeMap<String, usize> = BTreeMap::new();
        for (idx, ax) in all_axioms.iter().enumerate() {
            if skip_axiom[idx] {
                continue;
            }
            if let Axiom::EquivalentClasses(a, b) = ax {
                if let Concept::Name(c) = a {
                    *equiv_def_count.entry(c.clone()).or_default() += 1;
                }
                if let Concept::Name(c) = b {
                    *equiv_def_count.entry(c.clone()).or_default() += 1;
                }
            }
        }

        let mut deferred_equiv_defs: Vec<(String, &Concept)> = Vec::new();
        for (idx, ax) in all_axioms.iter().enumerate() {
            if skip_axiom[idx] {
                continue;
            }
            match ax {
                Axiom::SubClassOf(a, b) => {
                    walk_concept(a, false, true, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                    walk_concept(b, true, false, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                }
                Axiom::EquivalentClasses(a, b) => {
                    let candidate = match (a, b) {
                        (Concept::Name(c), rhs) if !matches!(rhs, Concept::Name(_)) => Some((c, rhs)),
                        (rhs, Concept::Name(c)) if !matches!(rhs, Concept::Name(_)) => Some((c, rhs)),
                        _ => None,
                    };
                    if let Some((c, rhs)) = candidate.filter(|(c, rhs)| {
                        !is_probe_class(c)
                            && !vp_classes.contains_key(*c)
                            && full_iris.get(*c).map(String::as_str) != Some("http://www.w3.org/2002/07/owl#Thing")
                            && equiv_def_count.get(*c).copied() == Some(1)
                            && !concept_mentions_class(rhs, c)
                    }) {
                        walk_concept(rhs, false, true, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                        deferred_equiv_defs.push((c.clone(), rhs));
                    } else {
                        walk_concept(a, true, true, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                        walk_concept(b, true, true, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                    }
                }
                Axiom::DisjointClasses(a, b) => {
                    walk_concept(a, false, true, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                    walk_concept(b, false, true, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                }
                Axiom::ConceptAssertion(c, ind) => {
                    if let Concept::Name(v) = c {
                        if vp_classes.get(v).is_some_and(|members| members.contains(ind)) {
                            continue;
                        }
                    }
                    walk_concept(c, true, false, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                }
                Axiom::Rule(body, head) | Axiom::DataRule(body, head) => {
                    if head.is_empty() {
                        return None;
                    }
                    for atom in body {
                        if let RuleAtom::Class(c, _) = atom {
                            walk_concept(c, false, true, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                        }
                    }
                    for atom in head {
                        match atom {
                            RuleAtom::Class(c, term) => {
                                if matches!(term, RuleTerm::Ind(_)) {
                                    return None;
                                }
                                walk_concept(c, true, false, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                            }
                            RuleAtom::Role(_, _, _) => {}
                            RuleAtom::Data(..) | RuleAtom::DataRange(..) => {
                                data_gen = true;
                            }
                            RuleAtom::Same(..) | RuleAtom::Diff(..) | RuleAtom::Builtin(..) => {
                                return None;
                            }
                        }
                    }
                }
                Axiom::SameIndividual(a, b) => {
                    if a.starts_with("_:") || b.starts_with("_:") {
                        return None;
                    }
                    forest_exact_for_rules = false;
                    same_pairs.push((a.clone(), b.clone()));
                }
                _ => {}
            }
        }
        for record in &rbox {
            match record {
                RboxRecord::Domain(_, c) | RboxRecord::Range(_, c) if !c.is_empty() => {
                    pos_classes.insert(c.clone());
                }
                _ => {}
            }
        }
        if !deferred_equiv_defs.is_empty() {
            let mut activated = vec![false; deferred_equiv_defs.len()];
            loop {
                let mut progress = false;
                for (i, (c, rhs)) in deferred_equiv_defs.iter().enumerate() {
                    if !activated[i] && pos_classes.contains(c) {
                        activated[i] = true;
                        progress = true;
                        walk_concept(rhs, true, false, &data_prop_shorts, &mut pos_classes, &mut has_self_roles, &mut has_self_in_source, &mut data_gen, &mut forest_exact_for_rules, &mut w_src, &mut w_dst, &mut card_functional, &mut card_inv_functional, &mut pos_existential_roles, &mut inv_existential_roles).ok()?;
                    }
                }
                if !progress {
                    break;
                }
            }
        }
        if !forest_exact_for_rules && !vp_classes.is_empty() {
            return None;
        }
        for v in vp_classes.keys() {
            if pos_classes.contains(v) {
                return None;
            }
        }

        let exact_data_values = (!data_gen).then(|| {
            let mut map: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
            for (raw_prop, raw_ind, lit) in &raw_data_assertions {
                if let Some(key) = literal_identity_key(lit) {
                    let prop = registry.short(raw_prop);
                    let ind = registry.short(raw_ind);
                    map.entry((prop, key)).or_default().insert(ind);
                }
            }
            map
        });

        // Collect RBox structure.
        let mut subroles: Vec<(String, String)> = Vec::new();
        let mut inverses: Vec<(String, String)> = Vec::new();
        let mut symmetric: BTreeSet<String> = BTreeSet::new();
        let mut transitive: BTreeSet<String> = BTreeSet::new();
        let mut chains: Vec<(Vec<String>, String)> = Vec::new();
        let mut functional: BTreeSet<String> = card_functional;
        let mut inv_functional: BTreeSet<String> = card_inv_functional;
        let mut self_roles: BTreeSet<String> = has_self_roles;
        let mut universal_roles: BTreeSet<String> = BTreeSet::new();
        let mut edges: BTreeMap<String, BTreeSet<(String, String)>> = BTreeMap::new();

        for ax in &all_axioms {
            match ax {
                Axiom::RoleAssertion(r, a, b) if !a.starts_with("_:") && !b.starts_with("_:") => {
                    edges.entry(r.clone()).or_default().insert((a.clone(), b.clone()));
                }
                Axiom::RoleInclusion(a, b) => subroles.push((a.clone(), b.clone())),
                Axiom::InverseRoles(a, b) => inverses.push((a.clone(), b.clone())),
                Axiom::SymmetricRole(r) => {
                    symmetric.insert(r.clone());
                    inverses.push((r.clone(), r.clone()));
                }
                Axiom::TransitiveRole(r) => {
                    transitive.insert(r.clone());
                }
                Axiom::ReflexiveRole(r) => {
                    self_roles.insert(r.clone());
                }
                Axiom::RoleChain(ch, sup) => chains.push((ch.clone(), sup.clone())),
                Axiom::FunctionalRole(r) if !data_prop_shorts.contains(r) => {
                    functional.insert(r.clone());
                }
                Axiom::InverseFunctionalRole(r) if !data_prop_shorts.contains(r) => {
                    inv_functional.insert(r.clone());
                }
                _ => {}
            }
        }
        for record in &rbox {
            match record {
                RboxRecord::Subrole(a, b) => subroles.push((a.clone(), b.clone())),
                RboxRecord::Inverse(a, b) => inverses.push((a.clone(), b.clone())),
                RboxRecord::Transitive(r) => {
                    transitive.insert(r.clone());
                }
                RboxRecord::Chain(r1, r2, sup) => {
                    chains.push((vec![r1.clone(), r2.clone()], sup.clone()));
                }
                RboxRecord::ChainN(ch, sup) => chains.push((ch.clone(), sup.clone())),
                _ => {}
            }
        }

        // Compute role hierarchy closure on signed roles `(role, is_inv)` to detect
        // tree-folding role chains `r_1 o ... o r_k <= sup` where some `r_i, r_j`
        // share a sub-role `t <= r_i` and `t^- <= r_j`.
        let mut all_roles: BTreeSet<String> = BTreeSet::new();
        for (a, b) in &subroles {
            all_roles.insert(a.clone());
            all_roles.insert(b.clone());
        }
        for (a, b) in &inverses {
            all_roles.insert(a.clone());
            all_roles.insert(b.clone());
        }
        for (ch, sup) in &chains {
            for r in ch {
                all_roles.insert(r.clone());
            }
            all_roles.insert(sup.clone());
        }
        let mut super_roles: BTreeMap<(String, bool), BTreeSet<(String, bool)>> = BTreeMap::new();
        for r in &all_roles {
            super_roles.entry((r.clone(), false)).or_default().insert((r.clone(), false));
            super_roles.entry((r.clone(), true)).or_default().insert((r.clone(), true));
        }
        loop {
            let mut changed = false;
            for (a, b) in &subroles {
                for inv in [false, true] {
                    let supers: Vec<_> = super_roles.get(&(b.clone(), inv)).into_iter().flatten().cloned().collect();
                    let entry = super_roles.entry((a.clone(), inv)).or_default();
                    for s in supers {
                        changed |= entry.insert(s);
                    }
                }
            }
            for (a, b) in &inverses {
                for inv in [false, true] {
                    let sb: Vec<_> = super_roles.get(&(b.clone(), !inv)).into_iter().flatten().cloned().collect();
                    let sa: Vec<_> = super_roles.get(&(a.clone(), !inv)).into_iter().flatten().cloned().collect();
                    let ea = super_roles.entry((a.clone(), inv)).or_default();
                    for s in sb {
                        changed |= ea.insert(s);
                    }
                    let eb = super_roles.entry((b.clone(), !inv)).or_default();
                    for s in sa {
                        changed |= eb.insert(s);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (ch, sup) in &chains {
            let mut can_fold = false;
            for i in 0..ch.len() {
                for j in (i + 1)..ch.len() {
                    let ri = &ch[i];
                    let rj = &ch[j];
                    if all_roles.iter().any(|t| {
                        (super_roles.get(&(t.clone(), false)).is_some_and(|s| s.contains(&(ri.clone(), false)))
                            && super_roles.get(&(t.clone(), true)).is_some_and(|s| s.contains(&(rj.clone(), false))))
                            || (super_roles.get(&(t.clone(), true)).is_some_and(|s| s.contains(&(ri.clone(), false)))
                                && super_roles.get(&(t.clone(), false)).is_some_and(|s| s.contains(&(rj.clone(), false))))
                    }) || functional.iter().chain(inv_functional.iter()).any(|f| {
                        (super_roles
                            .get(&(ri.clone(), false))
                            .is_some_and(|s| s.contains(&(f.clone(), false)))
                            && super_roles
                                .get(&(rj.clone(), true))
                                .is_some_and(|s| s.contains(&(f.clone(), false))))
                            || (super_roles
                                .get(&(ri.clone(), false))
                                .is_some_and(|s| s.contains(&(f.clone(), true)))
                                && super_roles
                                    .get(&(rj.clone(), true))
                                    .is_some_and(|s| s.contains(&(f.clone(), true))))
                    }) {
                        can_fold = true;
                        break;
                    }
                }
            }
            if can_fold {
                self_roles.insert(sup.clone());
            }
        }

        // Collect lowered rules for fixpoint evaluation.
        let mut all_rules: Vec<(Vec<RuleAtom>, Vec<RuleAtom>)> = Vec::new();
        for ax in ontology.rules() {
            if let Axiom::Rule(b, h) = ax {
                all_rules.push((b.clone(), h.clone()));
            }
        }
        let mut finite_values: Vec<String> = raw_data_assertions.iter().map(|(_, _, l)| l.clone()).collect();
        finite_values.sort();
        finite_values.dedup();
        for ax in ontology.datatype_rules() {
            if let Some(Axiom::Rule(b, h)) = super::data_rules::constant_data_rule_plan(ax) {
                all_rules.push((b, h));
            } else if !data_gen {
                if let Some(lowered) = super::data_rules::finite_data_rule_plan(ax, &finite_values, 100_000) {
                    for l in lowered {
                        if let Axiom::Rule(b, h) = l {
                            all_rules.push((b, h));
                        }
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }

        if !forest_exact_for_rules && !all_rules.is_empty() {
            return None;
        }

        // Separate rules whose head roles feed back into rule bodies or RBox axioms
        // from pure sink-head rules that only need to be evaluated once after the
        // recursive role fixpoint converges.
        let mut active_source_roles: BTreeSet<String> = BTreeSet::new();
        for r in &symmetric {
            active_source_roles.insert(r.clone());
        }
        for (a, b) in &inverses {
            active_source_roles.insert(a.clone());
            active_source_roles.insert(b.clone());
        }
        for (sub, _) in &subroles {
            active_source_roles.insert(sub.clone());
        }
        for r in &transitive {
            active_source_roles.insert(r.clone());
        }
        for (ch, _) in &chains {
            for r in ch {
                active_source_roles.insert(r.clone());
            }
        }
        for (body, _) in &all_rules {
            for atom in body {
                if let RuleAtom::Role(r, _, _) = atom {
                    active_source_roles.insert(r.clone());
                }
            }
        }
        let mut recursive_rules = Vec::new();
        let mut sink_rules = Vec::new();
        for (body, head) in &all_rules {
            let role_heads: Vec<_> = head
                .iter()
                .filter_map(|a| match a {
                    RuleAtom::Role(r, u, v) => Some((r, u, v)),
                    _ => None,
                })
                .collect();
            if role_heads.is_empty() {
                continue;
            }
            if role_heads.iter().any(|(r, _, _)| active_source_roles.contains(*r)) {
                recursive_rules.push((body, role_heads));
            } else {
                sink_rules.push((body, role_heads));
            }
        }

        let mut equiv = Equiv::new();
        for (a, b) in &same_pairs {
            equiv.union(a, b);
        }
        let mut all_named_merged = false;

        // Datalog fixpoint of `(edges, self_roles, w_src, w_dst, universal_roles, equiv)`.
        loop {
            let mut changed = false;
            if !forest_exact_for_rules {
                for r in &inv_existential_roles {
                    changed |= universal_roles.insert(r.clone());
                }
            }
            for r in &symmetric {
                if let Some(es) = edges.get(r).cloned() {
                    let entry = edges.entry(r.clone()).or_default();
                    for (a, b) in es {
                        changed |= entry.insert((b, a));
                    }
                }
                if !forest_exact_for_rules {
                    let ws = w_src.get(r).cloned().unwrap_or_default();
                    let wd = w_dst.get(r).cloned().unwrap_or_default();
                    if !ws.is_empty() {
                        let ed = w_dst.entry(r.clone()).or_default();
                        for v in ws {
                            changed |= ed.insert(v);
                        }
                    }
                    if !wd.is_empty() {
                        let es = w_src.entry(r.clone()).or_default();
                        for v in wd {
                            changed |= es.insert(v);
                        }
                    }
                    if functional.contains(r) {
                        changed |= inv_functional.insert(r.clone());
                    }
                    if inv_functional.contains(r) {
                        changed |= functional.insert(r.clone());
                    }
                }
            }
            for (a, b) in &inverses {
                if self_roles.contains(a) {
                    changed |= self_roles.insert(b.clone());
                }
                if self_roles.contains(b) {
                    changed |= self_roles.insert(a.clone());
                }
                if universal_roles.contains(a) {
                    changed |= universal_roles.insert(b.clone());
                }
                if universal_roles.contains(b) {
                    changed |= universal_roles.insert(a.clone());
                }
                if functional.contains(a) {
                    changed |= inv_functional.insert(b.clone());
                }
                if inv_functional.contains(a) {
                    changed |= functional.insert(b.clone());
                }
                if functional.contains(b) {
                    changed |= inv_functional.insert(a.clone());
                }
                if inv_functional.contains(b) {
                    changed |= functional.insert(a.clone());
                }
                if pos_existential_roles.contains(a) {
                    changed |= inv_existential_roles.insert(b.clone());
                }
                if inv_existential_roles.contains(a) {
                    changed |= pos_existential_roles.insert(b.clone());
                }
                if pos_existential_roles.contains(b) {
                    changed |= inv_existential_roles.insert(a.clone());
                }
                if inv_existential_roles.contains(b) {
                    changed |= pos_existential_roles.insert(a.clone());
                }
                if let Some(ea) = edges.get(a).cloned() {
                    let eb = edges.entry(b.clone()).or_default();
                    for (x, y) in ea {
                        changed |= eb.insert((y, x));
                    }
                }
                if let Some(eb) = edges.get(b).cloned() {
                    let ea = edges.entry(a.clone()).or_default();
                    for (x, y) in eb {
                        changed |= ea.insert((y, x));
                    }
                }
                if !forest_exact_for_rules {
                    if let Some(wsa) = w_src.get(a).cloned() {
                        let wdb = w_dst.entry(b.clone()).or_default();
                        for v in wsa {
                            changed |= wdb.insert(v);
                        }
                    }
                    if let Some(wda) = w_dst.get(a).cloned() {
                        let wsb = w_src.entry(b.clone()).or_default();
                        for v in wda {
                            changed |= wsb.insert(v);
                        }
                    }
                    if let Some(wsb) = w_src.get(b).cloned() {
                        let wda = w_dst.entry(a.clone()).or_default();
                        for v in wsb {
                            changed |= wda.insert(v);
                        }
                    }
                    if let Some(wdb) = w_dst.get(b).cloned() {
                        let wsa = w_src.entry(a.clone()).or_default();
                        for v in wdb {
                            changed |= wsa.insert(v);
                        }
                    }
                }
            }
            for (sub, sup) in &subroles {
                if self_roles.contains(sub) {
                    changed |= self_roles.insert(sup.clone());
                }
                if universal_roles.contains(sub) {
                    changed |= universal_roles.insert(sup.clone());
                }
                if functional.contains(sup) {
                    changed |= functional.insert(sub.clone());
                }
                if inv_functional.contains(sup) {
                    changed |= inv_functional.insert(sub.clone());
                }
                if pos_existential_roles.contains(sub) {
                    changed |= pos_existential_roles.insert(sup.clone());
                }
                if inv_existential_roles.contains(sub) {
                    changed |= inv_existential_roles.insert(sup.clone());
                }
                if let Some(es) = edges.get(sub).cloned() {
                    let entry = edges.entry(sup.clone()).or_default();
                    for e in es {
                        changed |= entry.insert(e);
                    }
                }
                if !forest_exact_for_rules {
                    if let Some(ws) = w_src.get(sub).cloned() {
                        let entry = w_src.entry(sup.clone()).or_default();
                        for v in ws {
                            changed |= entry.insert(v);
                        }
                    }
                    if let Some(wd) = w_dst.get(sub).cloned() {
                        let entry = w_dst.entry(sup.clone()).or_default();
                        for v in wd {
                            changed |= entry.insert(v);
                        }
                    }
                }
            }
            for r in &transitive {
                if let Some(es) = edges.get(r).cloned() {
                    let mut adj: BTreeMap<String, Vec<String>> = BTreeMap::new();
                    for (a, b) in &es {
                        adj.entry(a.clone()).or_default().push(b.clone());
                    }
                    let entry = edges.entry(r.clone()).or_default();
                    for (a, bs) in &adj {
                        for b in bs {
                            if let Some(cs) = adj.get(b) {
                                for c in cs {
                                    changed |= entry.insert((a.clone(), c.clone()));
                                }
                            }
                        }
                    }
                    if !forest_exact_for_rules {
                        if let Some(ws) = w_src.get(r).cloned() {
                            let ws_entry = w_src.entry(r.clone()).or_default();
                            for b in &ws {
                                if let Some(cs) = adj.get(b) {
                                    for c in cs {
                                        changed |= ws_entry.insert(c.clone());
                                    }
                                }
                            }
                        }
                        if let Some(wd) = w_dst.get(r).cloned() {
                            let wd_entry = w_dst.entry(r.clone()).or_default();
                            for (a, bs) in &adj {
                                if bs.iter().any(|b| wd.contains(b)) {
                                    changed |= wd_entry.insert(a.clone());
                                }
                            }
                        }
                    }
                }
                if !forest_exact_for_rules {
                    if let (Some(ws), Some(wd)) = (w_src.get(r), w_dst.get(r)) {
                        if ws.iter().any(|b| wd.contains(b)) {
                            changed |= universal_roles.insert(r.clone());
                        }
                    }
                }
            }
            for (ch, sup) in &chains {
                if ch.is_empty() {
                    continue;
                }
                if ch.iter().all(|r| self_roles.contains(r)) {
                    changed |= self_roles.insert(sup.clone());
                }
                if ch.iter().any(|r| pos_existential_roles.contains(r)) {
                    changed |= pos_existential_roles.insert(sup.clone());
                }
                if ch.iter().any(|r| inv_existential_roles.contains(r)) {
                    changed |= inv_existential_roles.insert(sup.clone());
                }
                // Relational composition along `ch`, allowing identity step on `self_roles`.
                let mut current: BTreeSet<(String, String)> = BTreeSet::new();
                let mut cur_w_src: BTreeSet<String> = BTreeSet::new();
                let mut cur_w_dst: BTreeSet<String> = BTreeSet::new();
                let mut cur_univ = false;
                let mut prefix_all_self = true;
                for step in ch {
                    let step_edges = edges.get(step);
                    let step_self = self_roles.contains(step);
                    let mut next: BTreeSet<(String, String)> = BTreeSet::new();
                    if prefix_all_self {
                        if let Some(se) = step_edges {
                            next.extend(se.iter().cloned());
                        }
                    }
                    if step_self {
                        next.extend(current.iter().cloned());
                    }
                    if !current.is_empty() {
                        if let Some(se) = step_edges {
                            let mut adj: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
                            for (u, v) in se {
                                adj.entry(u.as_str()).or_default().push(v.as_str());
                            }
                            for (a, b) in &current {
                                if let Some(cs) = adj.get(b.as_str()) {
                                    for &c in cs {
                                        next.insert((a.clone(), c.to_owned()));
                                    }
                                }
                            }
                        }
                    }
                    if !forest_exact_for_rules {
                        let step_w_src = w_src.get(step);
                        let step_w_dst = w_dst.get(step);
                        let step_univ = universal_roles.contains(step);
                        let mut next_w_src: BTreeSet<String> = BTreeSet::new();
                        let mut next_w_dst: BTreeSet<String> = cur_w_dst.clone();
                        let mut next_univ = cur_univ;

                        if let Some(sws) = step_w_src {
                            next_w_src.extend(sws.iter().cloned());
                        }
                        if let Some(swd) = step_w_dst {
                            if prefix_all_self {
                                next_w_dst.extend(swd.iter().cloned());
                            }
                            for (a, b) in &current {
                                if swd.contains(b) {
                                    next_w_dst.insert(a.clone());
                                }
                            }
                            if cur_w_src.iter().any(|b| swd.contains(b)) {
                                next_univ = true;
                            }
                        }
                        if step_self {
                            next_w_src.extend(cur_w_src.iter().cloned());
                        }
                        if prefix_all_self && step_univ {
                            next_univ = true;
                        }
                        if step_univ {
                            next_univ = true;
                            for (a, _) in &current {
                                next_w_dst.insert(a.clone());
                            }
                        }
                        if let Some(se) = step_edges {
                            if cur_univ || !cur_w_dst.is_empty() {
                                for (_, c) in se {
                                    next_w_src.insert(c.clone());
                                }
                            }
                            if !cur_w_src.is_empty() {
                                for (u, v) in se {
                                    if cur_w_src.contains(u) {
                                        next_w_src.insert(v.clone());
                                    }
                                }
                            }
                        }
                        cur_w_src = next_w_src;
                        cur_w_dst = next_w_dst;
                        cur_univ = next_univ;
                    }
                    current = next;
                    prefix_all_self &= step_self;
                }
                if !current.is_empty() {
                    let entry = edges.entry(sup.clone()).or_default();
                    for pair in current {
                        changed |= entry.insert(pair);
                    }
                }
                if !forest_exact_for_rules {
                    if !cur_w_src.is_empty() {
                        let entry = w_src.entry(sup.clone()).or_default();
                        for v in cur_w_src {
                            changed |= entry.insert(v);
                        }
                    }
                    if !cur_w_dst.is_empty() {
                        let entry = w_dst.entry(sup.clone()).or_default();
                        for v in cur_w_dst {
                            changed |= entry.insert(v);
                        }
                    }
                    if cur_univ {
                        changed |= universal_roles.insert(sup.clone());
                    }
                }
            }
            // Evaluate recursive rules with Role atoms in head.
            let rev_edges: BTreeMap<String, BTreeSet<(String, String)>> = if recursive_rules.is_empty() {
                BTreeMap::new()
            } else {
                edges
                    .iter()
                    .map(|(r, es)| (r.clone(), es.iter().map(|(a, b)| (b.clone(), a.clone())).collect()))
                    .collect()
            };
            for (body, role_heads) in &recursive_rules {
                let Some(bindings) = Self::eval_rule_bindings_raw(
                    body,
                    &named,
                    &edges,
                    &rev_edges,
                    &self_roles,
                    &vp_classes,
                    exact_data_values.as_ref(),
                    None,
                    100_000,
                ) else {
                    return None;
                };
                for (r, u, v) in role_heads {
                    let resolve = |t: &RuleTerm, b: &BTreeMap<String, String>| -> String {
                        match t {
                            RuleTerm::Ind(i) => i.clone(),
                            RuleTerm::Var(var) => b[var].clone(),
                        }
                    };
                    let entry = edges.entry((*r).clone()).or_default();
                    for b in &bindings {
                        changed |= entry.insert((resolve(u, b), resolve(v, b)));
                    }
                }
            }

            // Propagate equalities from functional, inverse-functional, and max-cardinality roles.
            for f in &functional {
                if universal_roles.contains(f)
                    || w_dst.get(f).is_some_and(|s| !s.is_empty())
                    || (pos_existential_roles.contains(f)
                        && (w_src.get(f).is_some_and(|s| !s.is_empty())
                            || edges.get(f).is_some_and(|s| !s.is_empty())))
                    || (inv_existential_roles.contains(f)
                        && w_src.get(f).is_some_and(|s| !s.is_empty()))
                {
                    if !all_named_merged {
                        all_named_merged = true;
                        forest_exact_for_rules = false;
                        changed = true;
                    }
                }
                if self_roles.contains(f) {
                    if w_src.get(f).is_some_and(|s| !s.is_empty()) && !all_named_merged {
                        all_named_merged = true;
                        forest_exact_for_rules = false;
                        changed = true;
                    }
                    if let Some(es) = edges.get(f) {
                        for (a, b) in es {
                            if a != b {
                                forest_exact_for_rules = false;
                                changed |= equiv.union(a, b);
                            }
                        }
                    }
                }
                if let Some(es) = edges.get(f) {
                    let mut seen: BTreeMap<&str, &str> = BTreeMap::new();
                    for (a, b) in es {
                        if let Some(&prev) = seen.get(a.as_str()) {
                            if prev != b.as_str() {
                                forest_exact_for_rules = false;
                                changed |= equiv.union(prev, b);
                            }
                        } else {
                            seen.insert(a.as_str(), b.as_str());
                        }
                    }
                }
                if let Some(ws) = w_src.get(f) {
                    if let Some(first_ws) = ws.iter().next() {
                        for other in ws.iter().skip(1) {
                            forest_exact_for_rules = false;
                            changed |= equiv.union(first_ws, other);
                        }
                        if let Some(es) = edges.get(f) {
                            for (_, b) in es {
                                forest_exact_for_rules = false;
                                changed |= equiv.union(first_ws, b);
                            }
                        }
                    }
                }
            }
            for f in &inv_functional {
                if universal_roles.contains(f)
                    || w_src.get(f).is_some_and(|s| !s.is_empty())
                    || (inv_existential_roles.contains(f)
                        && (w_dst.get(f).is_some_and(|s| !s.is_empty())
                            || edges.get(f).is_some_and(|s| !s.is_empty())))
                    || (pos_existential_roles.contains(f)
                        && w_dst.get(f).is_some_and(|s| !s.is_empty()))
                {
                    if !all_named_merged {
                        all_named_merged = true;
                        forest_exact_for_rules = false;
                        changed = true;
                    }
                }
                if self_roles.contains(f) {
                    if w_dst.get(f).is_some_and(|s| !s.is_empty()) && !all_named_merged {
                        all_named_merged = true;
                        forest_exact_for_rules = false;
                        changed = true;
                    }
                    if let Some(es) = edges.get(f) {
                        for (a, b) in es {
                            if a != b {
                                forest_exact_for_rules = false;
                                changed |= equiv.union(a, b);
                            }
                        }
                    }
                }
                if let Some(es) = edges.get(f) {
                    let mut seen: BTreeMap<&str, &str> = BTreeMap::new();
                    for (a, b) in es {
                        if let Some(&prev) = seen.get(b.as_str()) {
                            if prev != a.as_str() {
                                forest_exact_for_rules = false;
                                changed |= equiv.union(prev, a);
                            }
                        } else {
                            seen.insert(b.as_str(), a.as_str());
                        }
                    }
                }
                if let Some(wd) = w_dst.get(f) {
                    if let Some(first_wd) = wd.iter().next() {
                        for other in wd.iter().skip(1) {
                            forest_exact_for_rules = false;
                            changed |= equiv.union(first_wd, other);
                        }
                        if let Some(es) = edges.get(f) {
                            for (a, _) in es {
                                forest_exact_for_rules = false;
                                changed |= equiv.union(first_wd, a);
                            }
                        }
                    }
                }
            }

            if !forest_exact_for_rules && (!all_rules.is_empty() || !vp_classes.is_empty()) {
                return None;
            }

            if all_named_merged {
                for r in pos_existential_roles.iter().chain(inv_existential_roles.iter()) {
                    changed |= universal_roles.insert(r.clone());
                }
                let active: Vec<String> = edges
                    .iter()
                    .filter(|(_, s)| !s.is_empty())
                    .map(|(r, _)| r.clone())
                    .chain(w_src.iter().filter(|(_, s)| !s.is_empty()).map(|(r, _)| r.clone()))
                    .chain(w_dst.iter().filter(|(_, s)| !s.is_empty()).map(|(r, _)| r.clone()))
                    .chain(self_roles.iter().cloned())
                    .collect();
                for r in active {
                    changed |= universal_roles.insert(r);
                }
            } else if equiv.num_merges > 0 {
                let members_of = equiv.multi_member_map()?;
                if !members_of.is_empty() {
                    for es in edges.values_mut() {
                        let mut extra_a = Vec::new();
                        for (a, b) in es.iter() {
                            if let Some(ma) = members_of.get(a) {
                                for a2 in ma {
                                    if a2 != a {
                                        extra_a.push((a2.clone(), b.clone()));
                                    }
                                }
                            }
                        }
                        for pair in extra_a {
                            changed |= es.insert(pair);
                        }
                        let mut extra_b = Vec::new();
                        for (a, b) in es.iter() {
                            if let Some(mb) = members_of.get(b) {
                                for b2 in mb {
                                    if b2 != b {
                                        extra_b.push((a.clone(), b2.clone()));
                                    }
                                }
                            }
                        }
                        for pair in extra_b {
                            changed |= es.insert(pair);
                        }
                        if es.len() > 200_000 {
                            return None;
                        }
                    }
                    for ws in w_src.values_mut() {
                        let mut extra = Vec::new();
                        for b in ws.iter() {
                            if let Some(mb) = members_of.get(b) {
                                for b2 in mb {
                                    if b2 != b {
                                        extra.push(b2.clone());
                                    }
                                }
                            }
                        }
                        for b2 in extra {
                            changed |= ws.insert(b2);
                        }
                    }
                    for wd in w_dst.values_mut() {
                        let mut extra = Vec::new();
                        for a in wd.iter() {
                            if let Some(ma) = members_of.get(a) {
                                for a2 in ma {
                                    if a2 != a {
                                        extra.push(a2.clone());
                                    }
                                }
                            }
                        }
                        for a2 in extra {
                            changed |= wd.insert(a2);
                        }
                    }
                }
            }

            if !changed {
                break;
            }
        }
        let rev_edges_for_sinks: BTreeMap<String, BTreeSet<(String, String)>> = edges
            .iter()
            .map(|(r, es)| (r.clone(), es.iter().map(|(a, b)| (b.clone(), a.clone())).collect()))
            .collect();
        // Evaluate pure sink-head rules once after the recursive fixpoint converges.
        for (body, role_heads) in &sink_rules {
            let Some(bindings) = Self::eval_rule_bindings_raw(
                body,
                &named,
                &edges,
                &rev_edges_for_sinks,
                &self_roles,
                &vp_classes,
                exact_data_values.as_ref(),
                None,
                100_000,
            ) else {
                return None;
            };
            for (r, u, v) in role_heads {
                let resolve = |t: &RuleTerm, b: &BTreeMap<String, String>| -> String {
                    match t {
                        RuleTerm::Ind(i) => i.clone(),
                        RuleTerm::Var(var) => b[var].clone(),
                    }
                };
                let entry = edges.entry((*r).clone()).or_default();
                for b in &bindings {
                    entry.insert((resolve(u, b), resolve(v, b)));
                }
            }
        }
        // Re-check that sink-head rules did not introduce a functional or inverse-functional merge.
        if !sink_rules.is_empty() {
            for f in &functional {
                if let Some(es) = edges.get(f) {
                    let mut seen: BTreeMap<&str, &str> = BTreeMap::new();
                    for (a, b) in es {
                        if self_roles.contains(f) && a != b {
                            return None;
                        }
                        if let Some(&prev) = seen.get(a.as_str()) {
                            if prev != b.as_str() {
                                return None;
                            }
                        } else {
                            seen.insert(a.as_str(), b.as_str());
                        }
                    }
                }
            }
            for f in &inv_functional {
                if let Some(es) = edges.get(f) {
                    let mut seen: BTreeMap<&str, &str> = BTreeMap::new();
                    for (a, b) in es {
                        if self_roles.contains(f) && a != b {
                            return None;
                        }
                        if let Some(&prev) = seen.get(b.as_str()) {
                            if prev != a.as_str() {
                                return None;
                            }
                        } else {
                            seen.insert(b.as_str(), a.as_str());
                        }
                    }
                }
            }
        }
        let rev_edges: BTreeMap<String, BTreeSet<(String, String)>> = edges
            .iter()
            .map(|(r, es)| (r.clone(), es.iter().map(|(a, b)| (b.clone(), a.clone())).collect()))
            .collect();

        // Also compute positive entailed facts via `rule_assertions` for redundancy pruning.
        drop(all_axioms);
        let mut entailed_roles = BTreeSet::new();
        let mut entailed_classes = BTreeSet::new();
        if forest_exact_for_rules {
            super::rule_assertions::materialize(&mut ontology);
            for ax in ontology.abox() {
                match ax {
                    Axiom::RoleAssertion(r, a, b) => {
                        entailed_roles.insert((r.clone(), a.clone(), b.clone()));
                    }
                    Axiom::ConceptAssertion(Concept::Name(c), a) => {
                        entailed_classes.insert((c.clone(), a.clone()));
                    }
                    _ => {}
                }
            }
            if let Some(exact_dv) = &exact_data_values {
                for ((prop, key), inds) in exact_dv {
                    for ind in inds {
                        entailed_classes.insert((format!("__exact_dv__{prop}__{key}"), ind.clone()));
                    }
                }
            }
        }

        Some(NamedRoleBound {
            named,
            full_iris,
            short_of_full,
            edges,
            rev_edges,
            w_src,
            w_dst,
            universal_roles,
            self_roles,
            forest_exact_for_rules,
            has_self_in_source,
            vp_classes,
            exact_data_values,
            entailed_roles,
            entailed_classes,
        })
    }

    pub fn role_has_self_by_full_iri(&self, full_role: &str) -> bool {
        self.short_of_full.get(full_role).is_some_and(|short| {
            self.self_roles.contains(short)
                || self.universal_roles.contains(short)
                || self.w_dst.get(short).is_some_and(|s| !s.is_empty())
        })
    }

    pub fn reachable_targets_by_full_iri(&self, full_role: &str) -> BTreeSet<String> {
        let Some(short) = self.short_of_full.get(full_role) else {
            return BTreeSet::new();
        };
        if self.role_has_self_by_full_iri(full_role) {
            return self
                .named
                .iter()
                .filter_map(|s| self.full_iris.get(s))
                .filter(|iri| !iri.starts_with("_:") && !super::lenient::is_skolem_anon_iri(iri))
                .cloned()
                .collect();
        }
        let mut targets = BTreeSet::new();
        if let Some(es) = self.edges.get(short) {
            for (_, b) in es {
                if let Some(full_b) = self.full_iris.get(b) {
                    if !full_b.starts_with("_:") && !super::lenient::is_skolem_anon_iri(full_b) {
                        targets.insert(full_b.clone());
                    }
                }
            }
        }
        if let Some(ws) = self.w_src.get(short) {
            for b in ws {
                if let Some(full_b) = self.full_iris.get(b) {
                    if !full_b.starts_with("_:") && !super::lenient::is_skolem_anon_iri(full_b) {
                        targets.insert(full_b.clone());
                    }
                }
            }
        }
        targets
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_rule_bindings_raw(
        body: &[RuleAtom],
        named: &BTreeSet<String>,
        edges: &BTreeMap<String, BTreeSet<(String, String)>>,
        rev_edges: &BTreeMap<String, BTreeSet<(String, String)>>,
        self_roles: &BTreeSet<String>,
        vp_classes: &BTreeMap<String, BTreeSet<String>>,
        exact_data_values: Option<&BTreeMap<(String, String), BTreeSet<String>>>,
        alias_definitions: Option<&BTreeMap<String, Concept>>,
        max_bindings: usize,
    ) -> Option<Vec<BTreeMap<String, String>>> {
        let mut vars = BTreeSet::new();
        for atom in body {
            match atom {
                RuleAtom::Class(_, RuleTerm::Var(v)) => {
                    vars.insert(v.clone());
                }
                RuleAtom::Role(_, a, b) | RuleAtom::Same(a, b) | RuleAtom::Diff(a, b) => {
                    if let RuleTerm::Var(v) = a {
                        vars.insert(v.clone());
                    }
                    if let RuleTerm::Var(v) = b {
                        vars.insert(v.clone());
                    }
                }
                _ => {}
            }
        }
        // Check unary constraints on variables/constants first.
        let mut unary_restricted: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for atom in body {
            if let RuleAtom::Class(c, term) = atom {
                let resolved_c = match c {
                    Concept::Name(n) => alias_definitions.and_then(|m| m.get(n)).unwrap_or(c),
                    _ => c,
                };
                let allowed: Option<&BTreeSet<String>> = match resolved_c {
                    Concept::Name(n) => vp_classes.get(n),
                    Concept::Exists(Role::Name(p), filler) => {
                        if let Concept::Name(vn) = filler.as_ref() {
                            if let Some(lit) = vn.strip_prefix("__dt__val__") {
                                if let Some(key) = literal_identity_key(lit) {
                                    if let Some(edv) = exact_data_values {
                                        Some(edv.get(&(p.clone(), key)).map_or_else(
                                            || {
                                                static EMPTY: BTreeSet<String> = BTreeSet::new();
                                                &EMPTY
                                            },
                                            |s| s,
                                        ))
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(allowed_set) = allowed {
                    match term {
                        RuleTerm::Ind(i) => {
                            if !allowed_set.contains(i) {
                                return Some(Vec::new());
                            }
                        }
                        RuleTerm::Var(v) => {
                            unary_restricted
                                .entry(v.clone())
                                .and_modify(|s| s.retain(|x| allowed_set.contains(x)))
                                .or_insert_with(|| allowed_set.clone());
                        }
                    }
                }
            }
        }
        for set in unary_restricted.values() {
            if set.is_empty() {
                return Some(Vec::new());
            }
        }

        // Order body Role atoms and Same atoms to join efficiently.
        let role_atoms: Vec<_> = body
            .iter()
            .filter(|a| matches!(a, RuleAtom::Role(..) | RuleAtom::Same(..)))
            .collect();
        let diff_atoms: Vec<_> = body
            .iter()
            .filter_map(|a| match a {
                RuleAtom::Diff(x, y) => Some((x, y)),
                _ => None,
            })
            .collect();

        // Check ground Role/Same atoms and verify whether any Role atom has an empty relation.
        for atom in &role_atoms {
            if let RuleAtom::Role(r, a, b) = atom {
                let has_edges = edges.get(r).is_some_and(|s| !s.is_empty());
                let has_self = self_roles.contains(r);
                if !has_edges && !has_self {
                    return Some(Vec::new());
                }
                if let (RuleTerm::Ind(ia), RuleTerm::Ind(ib)) = (a, b) {
                    let ok = (has_self && ia == ib)
                        || edges.get(r).is_some_and(|s| s.contains(&(ia.clone(), ib.clone())));
                    if !ok {
                        return Some(Vec::new());
                    }
                }
            } else if let RuleAtom::Same(RuleTerm::Ind(ia), RuleTerm::Ind(ib)) = atom {
                if ia != ib {
                    return Some(Vec::new());
                }
            }
        }

        let mut bindings: Vec<BTreeMap<String, String>> = vec![BTreeMap::new()];
        let mut bound_vars: BTreeSet<String> = BTreeSet::new();
        let mut unary_order: Vec<(&String, &BTreeSet<String>)> = unary_restricted.iter().collect();
        unary_order.sort_by_key(|(_, set)| set.len());
        for (v, set) in unary_order {
            if set.len() <= 8 && bindings.len().saturating_mul(set.len()) <= 64 {
                let mut next = Vec::with_capacity(bindings.len() * set.len());
                for b in &bindings {
                    for val in set {
                        let mut nb = b.clone();
                        nb.insert(v.clone(), val.clone());
                        next.push(nb);
                    }
                }
                bindings = next;
                bound_vars.insert(v.clone());
            }
        }
        let mut remaining = role_atoms;

        while !remaining.is_empty() {
            let check_unary = |var: &str, val: &str| -> bool {
                unary_restricted.get(var).is_none_or(|s| s.contains(val))
            };
            // Pick an atom that touches an already-bound variable, ordered by actual
            // candidate fan-out over `bindings`, then a unary-restricted variable,
            // or has the fewest edges and does not use a `self_roles` role with both ends unbound.
            let best_idx = remaining
                .iter()
                .enumerate()
                .min_by_key(|(_, atom)| match atom {
                    RuleAtom::Same(a, b) => {
                        let ba_bound = matches!(a, RuleTerm::Ind(_))
                            || matches!(a, RuleTerm::Var(v) if bound_vars.contains(v));
                        let bb_bound = matches!(b, RuleTerm::Ind(_))
                            || matches!(b, RuleTerm::Var(v) if bound_vars.contains(v));
                        let ba_unary = matches!(a, RuleTerm::Var(v) if unary_restricted.contains_key(v));
                        let bb_unary = matches!(b, RuleTerm::Var(v) if unary_restricted.contains_key(v));
                        if ba_bound || bb_bound {
                            0usize
                        } else if ba_unary || bb_unary {
                            50_000
                        } else {
                            1_000_000 + named.len()
                        }
                    }
                    RuleAtom::Role(r, a, b) => {
                        let ba_bound = matches!(a, RuleTerm::Ind(_))
                            || matches!(a, RuleTerm::Var(v) if bound_vars.contains(v));
                        let bb_bound = matches!(b, RuleTerm::Ind(_))
                            || matches!(b, RuleTerm::Var(v) if bound_vars.contains(v));
                        let ba_unary = matches!(a, RuleTerm::Var(v) if unary_restricted.contains_key(v));
                        let bb_unary = matches!(b, RuleTerm::Var(v) if unary_restricted.contains_key(v));
                        let edge_cnt = edges.get(r).map_or(0, BTreeSet::len)
                            + if self_roles.contains(r) { named.len() } else { 0 };
                        match (ba_bound, bb_bound, ba_unary, bb_unary) {
                            (true, true, _, _) => 0,
                            (true, false, _, _) => {
                                let is_self = self_roles.contains(r);
                                let es = edges.get(r);
                                let RuleTerm::Var(var_b) = b else { unreachable!() };
                                let mut fanout = 0usize;
                                for bm in bindings.iter().take(64) {
                                    let xa = match a {
                                        RuleTerm::Ind(i) => i.as_str(),
                                        RuleTerm::Var(v) => bm[v].as_str(),
                                    };
                                    if is_self && check_unary(var_b, xa) {
                                        fanout += 1;
                                    }
                                    if let Some(s) = es {
                                        for (u, v) in s.range((xa.to_owned(), String::new())..) {
                                            if u != xa {
                                                break;
                                            }
                                            if check_unary(var_b, v) {
                                                fanout += 1;
                                            }
                                        }
                                    }
                                }
                                1 + fanout
                            }
                            (false, true, _, _) => {
                                let is_self = self_roles.contains(r);
                                let rev_es = rev_edges.get(r);
                                let RuleTerm::Var(var_a) = a else { unreachable!() };
                                let mut fanout = 0usize;
                                for bm in bindings.iter().take(64) {
                                    let xb = match b {
                                        RuleTerm::Ind(i) => i.as_str(),
                                        RuleTerm::Var(v) => bm[v].as_str(),
                                    };
                                    if is_self && check_unary(var_a, xb) {
                                        fanout += 1;
                                    }
                                    if let Some(s) = rev_es {
                                        for (v, u) in s.range((xb.to_owned(), String::new())..) {
                                            if v != xb {
                                                break;
                                            }
                                            if check_unary(var_a, u) {
                                                fanout += 1;
                                            }
                                        }
                                    }
                                }
                                1 + fanout
                            }
                            (false, false, true, true) => 50_000 + edge_cnt,
                            (false, false, true, false) | (false, false, false, true) => 100_000 + edge_cnt,
                            (false, false, false, false) => 1_000_000 + edge_cnt,
                        }
                    }
                    _ => usize::MAX,
                })?
                .0;
            let atom = remaining.remove(best_idx);
            let atom_terms = match atom {
                RuleAtom::Role(_, a, b) | RuleAtom::Same(a, b) => [a, b],
                _ => unreachable!(),
            };
            let any_bound = atom_terms.iter().any(|t| {
                matches!(t, RuleTerm::Ind(_))
                    || matches!(t, RuleTerm::Var(v) if bound_vars.contains(v))
            });
            // Only pre-expand `unary_restricted` when neither side of `atom` is already bound;
            // when one side is bound, the join below filters the other side via `check_unary`.
            if !any_bound {
                for t in atom_terms {
                    if let RuleTerm::Var(v) = t {
                        if !bound_vars.contains(v) {
                            if let Some(allowed) = unary_restricted.get(v) {
                                let mut next = Vec::new();
                                for b in &bindings {
                                    for val in allowed {
                                        let mut nb = b.clone();
                                        nb.insert(v.clone(), val.clone());
                                        next.push(nb);
                                        if next.len() > max_bindings {
                                            return None;
                                        }
                                    }
                                }
                                bindings = next;
                                bound_vars.insert(v.clone());
                                break;
                            }
                        }
                    }
                }
            }
            let mut next = Vec::new();
            match atom {
                RuleAtom::Same(a, b) => {
                    for binding in &bindings {
                        let va = match a {
                            RuleTerm::Ind(i) => Some(i.as_str()),
                            RuleTerm::Var(v) => binding.get(v).map(String::as_str),
                        };
                        let vb = match b {
                            RuleTerm::Ind(i) => Some(i.as_str()),
                            RuleTerm::Var(v) => binding.get(v).map(String::as_str),
                        };
                        match (va, vb, a, b) {
                            (Some(xa), Some(xb), _, _) => {
                                if xa == xb {
                                    next.push(binding.clone());
                                }
                            }
                            (Some(xa), None, _, RuleTerm::Var(var_b)) => {
                                if check_unary(var_b, xa) {
                                    let mut nb = binding.clone();
                                    nb.insert(var_b.clone(), xa.to_owned());
                                    next.push(nb);
                                }
                            }
                            (None, Some(xb), RuleTerm::Var(var_a), _) => {
                                if check_unary(var_a, xb) {
                                    let mut nb = binding.clone();
                                    nb.insert(var_a.clone(), xb.to_owned());
                                    next.push(nb);
                                }
                            }
                            (None, None, RuleTerm::Var(var_a), RuleTerm::Var(var_b)) => {
                                for x in named {
                                    if check_unary(var_a, x) && check_unary(var_b, x) {
                                        let mut nb = binding.clone();
                                        nb.insert(var_a.clone(), x.clone());
                                        nb.insert(var_b.clone(), x.clone());
                                        next.push(nb);
                                        if next.len() > max_bindings {
                                            return None;
                                        }
                                    }
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    if let RuleTerm::Var(v) = a {
                        bound_vars.insert(v.clone());
                    }
                    if let RuleTerm::Var(v) = b {
                        bound_vars.insert(v.clone());
                    }
                }
                RuleAtom::Role(r, a, b) => {
                    let es = edges.get(r);
                    let is_self = self_roles.contains(r);
                    for binding in &bindings {
                        let va = match a {
                            RuleTerm::Ind(i) => Some(i.as_str()),
                            RuleTerm::Var(v) => binding.get(v).map(String::as_str),
                        };
                        let vb = match b {
                            RuleTerm::Ind(i) => Some(i.as_str()),
                            RuleTerm::Var(v) => binding.get(v).map(String::as_str),
                        };
                        match (va, vb, a, b) {
                            (Some(xa), Some(xb), _, _) => {
                                let ok = (is_self && xa == xb)
                                    || es.is_some_and(|s| s.contains(&(xa.to_owned(), xb.to_owned())));
                                if ok {
                                    next.push(binding.clone());
                                }
                            }
                            (Some(xa), None, _, RuleTerm::Var(var_b)) => {
                                let mut targets = BTreeSet::new();
                                if is_self && check_unary(var_b, xa) {
                                    targets.insert(xa);
                                }
                                if let Some(s) = es {
                                    for (u, v) in s.range((xa.to_owned(), String::new())..) {
                                        if u != xa {
                                            break;
                                        }
                                        if check_unary(var_b, v) {
                                            targets.insert(v.as_str());
                                        }
                                    }
                                }
                                for xb in targets {
                                    let mut nb = binding.clone();
                                    nb.insert(var_b.clone(), xb.to_owned());
                                    next.push(nb);
                                    if next.len() > max_bindings {
                                        return None;
                                    }
                                }
                            }
                            (None, Some(xb), RuleTerm::Var(var_a), _) => {
                                let mut sources = BTreeSet::new();
                                if is_self && check_unary(var_a, xb) {
                                    sources.insert(xb);
                                }
                                if let Some(s) = rev_edges.get(r) {
                                    for (v, u) in s.range((xb.to_owned(), String::new())..) {
                                        if v != xb {
                                            break;
                                        }
                                        if check_unary(var_a, u) {
                                            sources.insert(u.as_str());
                                        }
                                    }
                                }
                                for xa in sources {
                                    let mut nb = binding.clone();
                                    nb.insert(var_a.clone(), xa.to_owned());
                                    next.push(nb);
                                    if next.len() > max_bindings {
                                        return None;
                                    }
                                }
                            }
                            (None, None, RuleTerm::Var(var_a), RuleTerm::Var(var_b)) => {
                                let mut pairs = BTreeSet::new();
                                if is_self {
                                    for x in named {
                                        if check_unary(var_a, x) && check_unary(var_b, x) {
                                            pairs.insert((x.as_str(), x.as_str()));
                                        }
                                    }
                                }
                                if let Some(s) = es {
                                    for (u, v) in s {
                                        if var_a == var_b && u != v {
                                            continue;
                                        }
                                        if check_unary(var_a, u) && check_unary(var_b, v) {
                                            pairs.insert((u.as_str(), v.as_str()));
                                        }
                                    }
                                }
                                for (xa, xb) in pairs {
                                    let mut nb = binding.clone();
                                    nb.insert(var_a.clone(), xa.to_owned());
                                    nb.insert(var_b.clone(), xb.to_owned());
                                    next.push(nb);
                                    if next.len() > max_bindings {
                                        return None;
                                    }
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    if let RuleTerm::Var(v) = a {
                        bound_vars.insert(v.clone());
                    }
                    if let RuleTerm::Var(v) = b {
                        bound_vars.insert(v.clone());
                    }
                }
                _ => unreachable!(),
            }
            bindings = next;
            if bindings.is_empty() {
                return Some(Vec::new());
            }
        }

        // Bind any remaining variables that did not appear in Role/Same atoms.
        for v in &vars {
            if !bound_vars.contains(v) {
                let pool = unary_restricted.get(v).unwrap_or(named);
                let mut next = Vec::new();
                for b in &bindings {
                    for val in pool {
                        let mut nb = b.clone();
                        nb.insert(v.clone(), val.clone());
                        next.push(nb);
                        if next.len() > max_bindings {
                            return None;
                        }
                    }
                }
                bindings = next;
                bound_vars.insert(v.clone());
            }
        }

        // Filter by Diff atoms.
        if !diff_atoms.is_empty() {
            bindings.retain(|b| {
                diff_atoms.iter().all(|(x, y)| {
                    let vx = match x {
                        RuleTerm::Ind(i) => i.as_str(),
                        RuleTerm::Var(v) => b[v].as_str(),
                    };
                    let vy = match y {
                        RuleTerm::Ind(i) => i.as_str(),
                        RuleTerm::Var(v) => b[v].as_str(),
                    };
                    vx != vy
                })
            });
        }

        Some(bindings)
    }

    pub fn has_reachable_binding(&self, rule: &Axiom) -> bool {
        let Axiom::Rule(body, _) = rule else {
            return true;
        };
        Self::eval_rule_bindings_raw(
            body,
            &self.named,
            &self.edges,
            &self.rev_edges,
            &self.self_roles,
            &self.vp_classes,
            self.exact_data_values.as_ref(),
            None,
            100_000,
        )
        .map_or(true, |b| !b.is_empty())
    }

    /// Ground a list of rules into exact `SubClassOf` axioms without an anchor
    /// individual or covering domain disjunction whenever every rule has a
    /// connected body-role spanning tree over its reachable bindings in `E+`.
    pub fn compile_rules(
        &self,
        rules: &[Axiom],
        alias_definitions: &BTreeMap<String, Concept>,
        max_instances: usize,
    ) -> Option<(Vec<Axiom>, usize)> {
        let mut axioms = Vec::new();
        let mut total_instances = 0usize;
        for rule in rules {
            let Axiom::Rule(body, head) = rule else {
                return None;
            };
            let bindings = Self::eval_rule_bindings_raw(
                body,
                &self.named,
                &self.edges,
                &self.rev_edges,
                &self.self_roles,
                &self.vp_classes,
                self.exact_data_values.as_ref(),
                Some(alias_definitions),
                max_instances.saturating_sub(total_instances),
            )?;
            if bindings.is_empty() {
                continue;
            }
            // If a binding's body atoms are already unconditionally entailed by the
            // positive ABox closure (`self.entailed_roles` / `self.entailed_classes`),
            // then one such binding per distinct head ground conclusion already forces
            // that head conclusion in every model, rendering duplicate head-conclusion
            // bindings redundant.
            let mut unconditionally_covered_heads: BTreeSet<Vec<(String, String, String)>> =
                BTreeSet::new();
            let mut kept_bindings = Vec::new();
            let mut non_asserted_bindings = Vec::new();
            for b in bindings {
                let head_key = Self::ground_head_key(head, &b);
                if self.body_unconditionally_entailed(body, &b, alias_definitions) {
                    if unconditionally_covered_heads.insert(head_key) {
                        kept_bindings.push(b);
                    }
                } else {
                    non_asserted_bindings.push((head_key, b));
                }
            }
            for (head_key, b) in non_asserted_bindings {
                if !unconditionally_covered_heads.contains(&head_key) {
                    kept_bindings.push(b);
                }
            }
            total_instances = total_instances.checked_add(kept_bindings.len())?;
            if total_instances > max_instances {
                return None;
            }
            for b in &kept_bindings {
                let ax = Self::spanning_tree_ground_axiom(body, head, b)?;
                axioms.push(ax);
            }
        }
        Some((axioms, total_instances))
    }

    fn ground_head_key(head: &[RuleAtom], binding: &BTreeMap<String, String>) -> Vec<(String, String, String)> {
        let resolve = |t: &RuleTerm| -> String {
            match t {
                RuleTerm::Ind(i) => i.clone(),
                RuleTerm::Var(v) => binding[v].clone(),
            }
        };
        let mut key: Vec<_> = head
            .iter()
            .map(|atom| match atom {
                RuleAtom::Class(Concept::Name(c), t) => ("C".to_owned(), c.clone(), resolve(t)),
                RuleAtom::Class(c, t) => ("CX".to_owned(), format!("{c:?}"), resolve(t)),
                RuleAtom::Role(r, a, b) => (format!("R:{r}"), resolve(a), resolve(b)),
                RuleAtom::Same(a, b) => ("=".to_owned(), resolve(a), resolve(b)),
                RuleAtom::Diff(a, b) => ("!=".to_owned(), resolve(a), resolve(b)),
                _ => ("?".to_owned(), String::new(), String::new()),
            })
            .collect();
        key.sort();
        key.dedup();
        key
    }

    fn body_unconditionally_entailed(
        &self,
        body: &[RuleAtom],
        binding: &BTreeMap<String, String>,
        alias_definitions: &BTreeMap<String, Concept>,
    ) -> bool {
        let resolve = |t: &RuleTerm| -> String {
            match t {
                RuleTerm::Ind(i) => i.clone(),
                RuleTerm::Var(v) => binding[v].clone(),
            }
        };
        body.iter().all(|atom| match atom {
            RuleAtom::Role(r, a, b) => self
                .entailed_roles
                .contains(&(r.clone(), resolve(a), resolve(b))),
            RuleAtom::Class(Concept::Name(c), a) => {
                let ind = resolve(a);
                if self.entailed_classes.contains(&(c.clone(), ind.clone())) {
                    return true;
                }
                if let Some(Concept::Exists(Role::Name(p), filler)) = alias_definitions.get(c) {
                    if let Concept::Name(vn) = filler.as_ref() {
                        if let Some(lit) = vn.strip_prefix("__dt__val__") {
                            if let Some(key) = literal_identity_key(lit) {
                                return self
                                    .entailed_classes
                                    .contains(&(format!("__exact_dv__{p}__{key}"), ind));
                            }
                        }
                    }
                }
                false
            }
            RuleAtom::Same(a, b) => resolve(a) == resolve(b),
            _ => false,
        })
    }

    fn spanning_tree_ground_axiom(
        body: &[RuleAtom],
        head: &[RuleAtom],
        binding: &BTreeMap<String, String>,
    ) -> Option<Axiom> {
        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        enum TermKey {
            Var(String),
            Ind(String),
        }
        let key_of = |t: &RuleTerm| -> TermKey {
            match t {
                RuleTerm::Var(v) => TermKey::Var(v.clone()),
                RuleTerm::Ind(i) => TermKey::Ind(i.clone()),
            }
        };
        let resolve = |k: &TermKey| -> String {
            match k {
                TermKey::Var(v) => binding[v].clone(),
                TermKey::Ind(i) => i.clone(),
            }
        };

        let mut body_terms = BTreeSet::new();
        let mut role_edges: Vec<(usize, String, TermKey, TermKey)> = Vec::new();
        for (idx, atom) in body.iter().enumerate() {
            match atom {
                RuleAtom::Class(_, a) => {
                    body_terms.insert(key_of(a));
                }
                RuleAtom::Role(r, a, b) => {
                    let ka = key_of(a);
                    let kb = key_of(b);
                    body_terms.insert(ka.clone());
                    body_terms.insert(kb.clone());
                    role_edges.push((idx, r.clone(), ka, kb));
                }
                RuleAtom::Same(a, b) | RuleAtom::Diff(a, b) => {
                    body_terms.insert(key_of(a));
                    body_terms.insert(key_of(b));
                }
                _ => return None,
            }
        }
        if body_terms.is_empty() {
            return None;
        }

        // Choose a `root` term in `body_terms` that appears in every head atom.
        let root_candidates: Vec<TermKey> = body_terms.iter().cloned().collect();
        let root = root_candidates.into_iter().find(|cand| {
            head.iter().all(|atom| match atom {
                RuleAtom::Class(_, a) => &key_of(a) == cand,
                RuleAtom::Role(_, a, b) | RuleAtom::Same(a, b) | RuleAtom::Diff(a, b) => {
                    &key_of(a) == cand || &key_of(b) == cand
                }
                _ => false,
            })
        })?;

        // Build BFS spanning tree of `body_terms` rooted at `root`.
        let mut visited: BTreeSet<TermKey> = BTreeSet::from([root.clone()]);
        let mut queue: VecDeque<TermKey> = VecDeque::from([root.clone()]);
        let mut tree_children: BTreeMap<TermKey, Vec<(TermKey, Role)>> = BTreeMap::new();
        let mut used_edge_indices: BTreeSet<usize> = BTreeSet::new();

        while let Some(u) = queue.pop_front() {
            for (idx, r, a, b) in &role_edges {
                if &u == a && !visited.contains(b) {
                    visited.insert(b.clone());
                    used_edge_indices.insert(*idx);
                    tree_children
                        .entry(u.clone())
                        .or_default()
                        .push((b.clone(), Role::Name(r.clone())));
                    queue.push_back(b.clone());
                } else if &u == b && !visited.contains(a) {
                    visited.insert(a.clone());
                    used_edge_indices.insert(*idx);
                    tree_children
                        .entry(u.clone())
                        .or_default()
                        .push((a.clone(), Role::Inverse(r.clone())));
                    queue.push_back(a.clone());
                }
            }
        }
        if visited.len() != body_terms.len() {
            return None;
        }

        // Collect local attachments per term `u`.
        let mut local_parts: BTreeMap<TermKey, Vec<Concept>> = BTreeMap::new();
        for u in &body_terms {
            local_parts.insert(u.clone(), vec![Concept::Nominal(resolve(u))]);
        }
        for (idx, atom) in body.iter().enumerate() {
            match atom {
                RuleAtom::Class(c, a) => {
                    local_parts.entry(key_of(a)).or_default().push(c.clone());
                }
                RuleAtom::Same(a, b) => {
                    let ka = key_of(a);
                    let kb = key_of(b);
                    if resolve(&ka) != resolve(&kb) {
                        local_parts
                            .entry(ka)
                            .or_default()
                            .push(Concept::Nominal(resolve(&kb)));
                    }
                }
                RuleAtom::Diff(a, b) => {
                    let ka = key_of(a);
                    let kb = key_of(b);
                    local_parts
                        .entry(ka)
                        .or_default()
                        .push(Concept::Not(Box::new(Concept::Nominal(resolve(&kb)))));
                }
                RuleAtom::Role(r, a, b) if !used_edge_indices.contains(&idx) => {
                    let ka = key_of(a);
                    let kb = key_of(b);
                    local_parts.entry(ka).or_default().push(Concept::Exists(
                        Role::Name(r.clone()),
                        Box::new(Concept::Nominal(resolve(&kb))),
                    ));
                }
                _ => {}
            }
        }

        fn build_subtree(
            u: &TermKey,
            children: &BTreeMap<TermKey, Vec<(TermKey, Role)>>,
            local_parts: &mut BTreeMap<TermKey, Vec<Concept>>,
        ) -> Concept {
            let mut parts = local_parts.remove(u).unwrap_or_default();
            if let Some(ch_list) = children.get(u) {
                for (child, role) in ch_list {
                    let child_concept = build_subtree(child, children, local_parts);
                    parts.push(Concept::Exists(role.clone(), Box::new(child_concept)));
                }
            }
            mk_and(parts)
        }

        let premise = build_subtree(&root, &tree_children, &mut local_parts);
        let mut head_parts = Vec::new();
        for atom in head {
            match atom {
                RuleAtom::Class(c, _) => head_parts.push(c.clone()),
                RuleAtom::Role(r, a, b) => {
                    let ka = key_of(a);
                    let kb = key_of(b);
                    if ka == root && kb == root {
                        head_parts.push(Concept::Exists(
                            Role::Name(r.clone()),
                            Box::new(Concept::Nominal(resolve(&root))),
                        ));
                    } else if ka == root {
                        head_parts.push(Concept::Exists(
                            Role::Name(r.clone()),
                            Box::new(Concept::Nominal(resolve(&kb))),
                        ));
                    } else {
                        head_parts.push(Concept::Exists(
                            Role::Inverse(r.clone()),
                            Box::new(Concept::Nominal(resolve(&ka))),
                        ));
                    }
                }
                RuleAtom::Same(a, b) => {
                    let ka = key_of(a);
                    let kb = key_of(b);
                    let other = if ka == root { &kb } else { &ka };
                    head_parts.push(Concept::Nominal(resolve(other)));
                }
                RuleAtom::Diff(a, b) => {
                    let ka = key_of(a);
                    let kb = key_of(b);
                    let other = if ka == root { &kb } else { &ka };
                    head_parts.push(Concept::Not(Box::new(Concept::Nominal(resolve(other)))));
                }
                _ => return None,
            }
        }
        let conclusion = if head_parts.is_empty() {
            Concept::Bottom
        } else {
            mk_and(head_parts)
        };
        Some(Axiom::SubClassOf(premise, conclusion))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_role_bound_computes_closure_and_compiles_spanning_tree() {
        let _test_env = crate::test_env::read();
        let src = r#"Ontology(
            Declaration(Class(<http://e#A>))
            Declaration(Class(<http://e#B>))
            Declaration(ObjectProperty(<http://e#r>))
            Declaration(ObjectProperty(<http://e#s>))
            Declaration(ObjectProperty(<http://e#t>))
            Declaration(DataProperty(<http://e#p>))
            Declaration(DataProperty(<http://e#q>))
            SubDataPropertyOf(<http://e#p> <http://e#q>)
            ObjectPropertyAssertion(<http://e#r> <http://e#a> <http://e#b>)
            ObjectPropertyAssertion(<http://e#s> <http://e#b> <http://e#c>)
            DLSafeRule(
                Body(
                    ObjectPropertyAtom(<http://e#r> Variable(<http://e#x>) Variable(<http://e#y>))
                    ObjectPropertyAtom(<http://e#s> Variable(<http://e#y>) Variable(<http://e#z>))
                )
                Head(ObjectPropertyAtom(<http://e#t> Variable(<http://e#x>) Variable(<http://e#z>)))
            )
        )"#;
        let bound = NamedRoleBound::compute(src).expect("bound succeeds");
        assert_eq!(
            bound.reachable_targets_by_full_iri("http://e#t"),
            BTreeSet::from(["http://e#c".to_owned()])
        );
    }

    const ADV_OFN: &str = r#"Prefix(:=<http://ex.org/>)
Ontology(<http://ex.org/adv>
Declaration(ObjectProperty(:r1))
Declaration(ObjectProperty(:r2))
Declaration(ObjectProperty(:s2))
Declaration(ObjectProperty(:r3))
Declaration(ObjectProperty(:s3))
Declaration(ObjectProperty(:r4))
Declaration(ObjectProperty(:s4))
Declaration(ObjectProperty(:t4))
Declaration(ObjectProperty(:r5))
Declaration(ObjectProperty(:r6))
Declaration(ObjectProperty(:s6))
Declaration(ObjectProperty(:r7))
Declaration(ObjectProperty(:r8))
Declaration(ObjectProperty(:r10))
Declaration(ObjectProperty(:r12))
Declaration(ObjectProperty(:s12))
Declaration(ObjectProperty(:r14))
Declaration(ObjectProperty(:s14))
Declaration(ObjectProperty(:t14))
Declaration(ObjectProperty(:q))
Declaration(NamedIndividual(:a1))
Declaration(NamedIndividual(:a2))
Declaration(NamedIndividual(:a3))
Declaration(NamedIndividual(:c3))
Declaration(NamedIndividual(:a4))
Declaration(NamedIndividual(:b4))
Declaration(NamedIndividual(:c4))
Declaration(NamedIndividual(:a5))
Declaration(NamedIndividual(:c5))
Declaration(NamedIndividual(:a6))
Declaration(NamedIndividual(:b6))
Declaration(NamedIndividual(:c6))
Declaration(NamedIndividual(:d6))
Declaration(NamedIndividual(:a7))
Declaration(NamedIndividual(:b7))
Declaration(NamedIndividual(:a8))
Declaration(NamedIndividual(:b8))
Declaration(NamedIndividual(:c8))
Declaration(NamedIndividual(:a10))
Declaration(NamedIndividual(:c10))
Declaration(NamedIndividual(:a12))
Declaration(NamedIndividual(:b12))
Declaration(NamedIndividual(:c12))
Declaration(NamedIndividual(:d12))
Declaration(NamedIndividual(:a14))
Declaration(NamedIndividual(:b14))
Declaration(NamedIndividual(:x14))
Declaration(NamedIndividual(:c14))
Declaration(NamedIndividual(:d14))
Declaration(NamedIndividual(:p1))
Declaration(NamedIndividual(:p2))
Declaration(NamedIndividual(:p3))
Declaration(NamedIndividual(:z0))
Declaration(NamedIndividual(:z1))
Declaration(NamedIndividual(:z2))
Declaration(NamedIndividual(:z3))
Declaration(NamedIndividual(:z4))
Declaration(NamedIndividual(:z5))
Declaration(NamedIndividual(:z6))
Declaration(NamedIndividual(:z7))
Declaration(NamedIndividual(:z8))
Declaration(NamedIndividual(:z9))
Declaration(NamedIndividual(:z10))
Declaration(NamedIndividual(:z11))
Declaration(NamedIndividual(:z12))
Declaration(NamedIndividual(:z13))
Declaration(NamedIndividual(:z14))
Declaration(NamedIndividual(:z15))
Declaration(NamedIndividual(:z16))
Declaration(NamedIndividual(:z17))
Declaration(NamedIndividual(:z18))
Declaration(NamedIndividual(:z19))
Declaration(NamedIndividual(:z20))
Declaration(NamedIndividual(:z21))
Declaration(NamedIndividual(:z22))
Declaration(NamedIndividual(:z23))
Declaration(NamedIndividual(:z24))
Declaration(NamedIndividual(:z25))
Declaration(NamedIndividual(:z26))
Declaration(NamedIndividual(:z27))
Declaration(NamedIndividual(:z28))
Declaration(NamedIndividual(:z29))
Declaration(NamedIndividual(:z30))
Declaration(NamedIndividual(:z31))
Declaration(NamedIndividual(:z32))
Declaration(NamedIndividual(:z33))
Declaration(NamedIndividual(:z34))
Declaration(NamedIndividual(:z35))
Declaration(NamedIndividual(:z36))
Declaration(NamedIndividual(:z37))
Declaration(NamedIndividual(:z38))
Declaration(NamedIndividual(:z39))
Declaration(Class(:A2))
Declaration(Class(:A5))
Declaration(Class(:A6))
Declaration(Class(:A10))
Declaration(Class(:A12))
SameIndividual(:p1 :p2)
SubClassOf(ObjectHasValue(:q :p3) owl:Thing)
ObjectPropertyAssertion(:q :p1 :p3)
ReflexiveObjectProperty(:r1)
SubClassOf(:A2 ObjectHasSelf(:r2))
ClassAssertion(:A2 :a2)
InverseObjectProperties(:r3 :s3)
ObjectPropertyAssertion(:s3 :c3 :a3)
SubObjectPropertyOf(ObjectPropertyChain(:r4 :s4) :t4)
ObjectPropertyAssertion(:r4 :a4 :b4)
ObjectPropertyAssertion(:s4 :b4 :c4)
SubClassOf(:A5 ObjectHasValue(:r5 :c5))
ClassAssertion(:A5 :a5)
FunctionalObjectProperty(:r6)
ObjectPropertyAssertion(:r6 :a6 :b6)
SubClassOf(:A6 ObjectHasValue(:r6 :c6))
ClassAssertion(:A6 :a6)
ObjectPropertyAssertion(:s6 :d6 :b6)
SymmetricObjectProperty(:r7)
ObjectPropertyAssertion(:r7 :a7 :b7)
ObjectPropertyAssertion(:r8 :a8 :b8)
SameIndividual(:b8 :c8)
SubClassOf(:A10 ObjectHasValue(ObjectInverseOf(:r10) :c10))
ClassAssertion(:A10 :a10)
SubClassOf(:A12 ObjectMaxCardinality(1 :r12))
ClassAssertion(:A12 :a12)
ObjectPropertyAssertion(:r12 :a12 :b12)
ObjectPropertyAssertion(:r12 :a12 :c12)
ObjectPropertyAssertion(:s12 :d12 :b12)
InverseFunctionalObjectProperty(:r14)
ObjectPropertyAssertion(:r14 :a14 :x14)
ObjectPropertyAssertion(:r14 :b14 :x14)
ObjectPropertyAssertion(:t14 :d14 :a14)
ObjectPropertyAssertion(:s14 :a14 :c14)
)"#;

    #[test]
    fn named_role_bound_covers_adv_ofn_and_propagates_merges_across_roles() {
        let _test_env = crate::test_env::read();
        let bound = NamedRoleBound::compute(ADV_OFN).expect("bound succeeds on adv.ofn");
        assert!(!bound.forest_exact_for_rules);
        assert!(bound.role_has_self_by_full_iri(":r1"));
        assert!(bound.role_has_self_by_full_iri(":r2"));
        assert!(bound.role_has_self_by_full_iri(":r10"));
        assert_eq!(
            bound.reachable_targets_by_full_iri(":s6"),
            BTreeSet::from([":b6".to_owned(), ":c6".to_owned()])
        );
        assert_eq!(
            bound.reachable_targets_by_full_iri(":s12"),
            BTreeSet::from([":b12".to_owned(), ":c12".to_owned()])
        );
        assert_eq!(
            bound.reachable_targets_by_full_iri(":t14"),
            BTreeSet::from([":a14".to_owned(), ":b14".to_owned()])
        );
        assert_eq!(
            bound.reachable_targets_by_full_iri(":s14"),
            BTreeSet::from([":c14".to_owned()])
        );
        assert_eq!(
            bound.reachable_targets_by_full_iri(":r8"),
            BTreeSet::from([":b8".to_owned(), ":c8".to_owned()])
        );
    }

    #[test]
    fn named_role_bound_adversarial_equality_and_role_closure_cases() {
        let _test_env = crate::test_env::read();
        let cases: &[(&str, &str, &[&str])] = &[
            // 1. Merges through a 3-step chain of functional roles
            (
                "functional_role_chain_merge",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2))
                    Declaration(ObjectProperty(:f3)) Declaration(ObjectProperty(:other))
                    FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2) FunctionalObjectProperty(:f3)
                    ObjectPropertyAssertion(:f1 :a :b1) ObjectPropertyAssertion(:f1 :a :b2)
                    ObjectPropertyAssertion(:f2 :b1 :c1) ObjectPropertyAssertion(:f2 :b2 :c2)
                    ObjectPropertyAssertion(:f3 :c1 :d1) ObjectPropertyAssertion(:f3 :c2 :d2)
                    ObjectPropertyAssertion(:other :x :d1)
                )"#,
                 &[":d1", ":d2"],
            ),
            // 2. Merges through a chain of functional roles seeded by ObjectHasValue
            (
                "functional_chain_with_has_value_merge",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A))
                    Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2)) Declaration(ObjectProperty(:other))
                    FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2)
                    ObjectPropertyAssertion(:f1 :a :b1)
                    SubClassOf(:A ObjectHasValue(:f1 :b2)) ClassAssertion(:A :a)
                    ObjectPropertyAssertion(:f2 :b1 :c1) ObjectPropertyAssertion(:f2 :b2 :c2)
                    ObjectPropertyAssertion(:other :x :c1)
                )"#,
                &[":c1", ":c2"],
            ),
            // 3. Merge of an asserted target under an inverse with an ObjectHasValue target
            (
                "asserted_target_with_has_value_under_inverse",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A))
                    Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                    InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                    ObjectPropertyAssertion(:s :b :a)
                    SubClassOf(:A ObjectHasValue(:r :c)) ClassAssertion(:A :a)
                    ObjectPropertyAssertion(:other :d :b)
                )"#,
                &[":b", ":c"],
            ),
            // 4. Merge of an asserted target with ObjectHasValue(ObjectInverseOf(:s) :c)
            (
                "asserted_target_with_inverse_of_has_value",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A))
                    Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                    InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                    ObjectPropertyAssertion(:r :a :b)
                    SubClassOf(:A ObjectHasValue(ObjectInverseOf(:s) :c)) ClassAssertion(:A :a)
                    ObjectPropertyAssertion(:other :d :b)
                )"#,
                &[":b", ":c"],
            ),
            // 5. Merge of an asserted target with a HasValue target where HasValue is on the inverse role
            (
                "inverse_has_value_source_merge",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A))
                    Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                    Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                    Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:d))
                    InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                    ObjectPropertyAssertion(:r :a :b)
                    SubClassOf(:A ObjectHasValue(:s :a)) ClassAssertion(:A :c)
                    ObjectPropertyAssertion(:other :d :b)
                )"#,
                &[":b", ":c"],
            ),
            // 6. Max cardinality 1 on an inverse role
            (
                "max_cardinality_1_on_inverse_role",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A))
                    Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                    SubClassOf(:A ObjectMaxCardinality(1 ObjectInverseOf(:r)))
                    ClassAssertion(:A :x)
                    ObjectPropertyAssertion(:r :a :x) ObjectPropertyAssertion(:r :b :x)
                    ObjectPropertyAssertion(:other :d :a)
                )"#,
                &[":a", ":b"],
            ),
            // 7. Exact cardinality 1 on an inverse role combined with ObjectHasValue
            (
                "exact_cardinality_1_on_inverse_role_with_has_value",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A)) Declaration(Class(:B))
                    Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                    Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                    Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:x))
                    SubClassOf(:A ObjectExactCardinality(1 ObjectInverseOf(:r)))
                    ClassAssertion(:A :x)
                    ObjectPropertyAssertion(:r :a :x)
                    SubClassOf(:B ObjectHasValue(:r :x)) ClassAssertion(:B :b)
                    ObjectPropertyAssertion(:other :d :a)
                )"#,
                &[":a", ":b"],
            ),
            // 8. Merge that feeds a property chain
            (
                "merge_feeding_property_chain",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:r1))
                    Declaration(ObjectProperty(:r2)) Declaration(ObjectProperty(:other))
                    FunctionalObjectProperty(:f)
                    ObjectPropertyAssertion(:f :x :b1) ObjectPropertyAssertion(:f :x :b2)
                    SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                    ObjectPropertyAssertion(:r1 :a :b1) ObjectPropertyAssertion(:r2 :b2 :c)
                )"#,
                &[":c"],
            ),
            // 9. Two merges (functional + inverse-functional) feeding both steps of a property chain
            (
                "two_merges_feeding_property_chain",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2))
                    Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                    Declaration(ObjectProperty(:other))
                    FunctionalObjectProperty(:f1) InverseFunctionalObjectProperty(:f2)
                    ObjectPropertyAssertion(:f1 :u :b1) ObjectPropertyAssertion(:f1 :u :b2)
                    ObjectPropertyAssertion(:f2 :c1 :v) ObjectPropertyAssertion(:f2 :c2 :v)
                    SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                    ObjectPropertyAssertion(:r1 :a :b1)
                    ObjectPropertyAssertion(:r2 :b2 :c1)
                )"#,
                &[":c1", ":c2"],
            ),
            // 10. Reflexive and HasSelf roles feeding a chain and a functional merge
            (
                "reflexive_and_has_self_in_chain_and_merge",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:B))
                    Declaration(ObjectProperty(:refl)) Declaration(ObjectProperty(:s))
                    Declaration(ObjectProperty(:fself)) Declaration(ObjectProperty(:other))
                    ReflexiveObjectProperty(:refl)
                    SubObjectPropertyOf(ObjectPropertyChain(:refl :s) :other)
                    ObjectPropertyAssertion(:s :a :b)
                    FunctionalObjectProperty(:fself)
                    SubClassOf(:B ObjectHasSelf(:fself)) ClassAssertion(:B :m1)
                    ObjectPropertyAssertion(:fself :m1 :m2)
                    ObjectPropertyAssertion(:other :d :m1)
                )"#,
                &[":b", ":m1", ":m2"],
            ),
            // 11. Symmetric and transitive roles combined with a functional merge
            (
                "symmetric_and_transitive_with_merge",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(ObjectProperty(:sym)) Declaration(ObjectProperty(:other))
                    Declaration(ObjectProperty(:f))
                    SymmetricObjectProperty(:sym) TransitiveObjectProperty(:other)
                    SubObjectPropertyOf(:sym :other) FunctionalObjectProperty(:f)
                    ObjectPropertyAssertion(:sym :b1 :a)
                    ObjectPropertyAssertion(:f :x :b1) ObjectPropertyAssertion(:f :x :b2)
                    ObjectPropertyAssertion(:other :b2 :c)
                )"#,
                &[":a", ":b1", ":b2", ":c"],
            ),
            // 12. Symmetric role with ObjectHasValue
            (
                "symmetric_with_has_value",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A))
                    Declaration(ObjectProperty(:other))
                    Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                    SymmetricObjectProperty(:other)
                    SubClassOf(:A ObjectHasValue(:other :b)) ClassAssertion(:A :a)
                )"#,
                &[":a", ":b"],
            ),
            // 13. Equivalent properties with inverse and functional merge
            (
                "equivalent_properties_with_inverses_and_merge",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(ObjectProperty(:p1)) Declaration(ObjectProperty(:p2))
                    Declaration(ObjectProperty(:p3)) Declaration(ObjectProperty(:other))
                    EquivalentObjectProperties(:p1 :p2)
                    InverseObjectProperties(:p2 :p3)
                    FunctionalObjectProperty(:p2)
                    ObjectPropertyAssertion(:p1 :a :b1)
                    ObjectPropertyAssertion(:p3 :b2 :a)
                    ObjectPropertyAssertion(:other :d :b1)
                )"#,
                &[":b1", ":b2"],
            ),
            // 14. Role hierarchy with inverses and ObjectHasValue feeding a functional merge
            (
                "role_hierarchy_with_inverses_and_has_value",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A))
                    Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))
                    Declaration(ObjectProperty(:t)) Declaration(ObjectProperty(:other))
                    SubObjectPropertyOf(:r ObjectInverseOf(:s))
                    SubObjectPropertyOf(ObjectInverseOf(:s) :t)
                    SubClassOf(:A ObjectHasValue(:r :b)) ClassAssertion(:A :a)
                    FunctionalObjectProperty(:t)
                    ObjectPropertyAssertion(:t :a :c)
                    ObjectPropertyAssertion(:other :d :b)
                )"#,
                &[":b", ":c"],
            ),
            // 15. SameIndividual chain of length 4
            (
                "same_individual_chain_of_length_4",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(ObjectProperty(:other))
                    SameIndividual(:i1 :i2)
                    SameIndividual(:i2 :i3)
                    SameIndividual(:i3 :i4)
                    SameIndividual(:i4 :i5)
                    ObjectPropertyAssertion(:other :src :i1)
                )"#,
                &[":i1", ":i2", ":i3", ":i4", ":i5"],
            ),
            // 16. 3-ary property chain with ObjectHasValue, SameIndividual, and functional merge
            (
                "nary_chain_with_has_value_and_same_individual",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(Class(:A))
                    Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                    Declaration(ObjectProperty(:r3)) Declaration(ObjectProperty(:f))
                    Declaration(ObjectProperty(:other))
                    SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2 :r3) :other)
                    SubClassOf(:A ObjectHasValue(:r1 :b1)) ClassAssertion(:A :a)
                    SameIndividual(:b1 :b2)
                    ObjectPropertyAssertion(:r2 :b2 :c1)
                    FunctionalObjectProperty(:f)
                    ObjectPropertyAssertion(:f :u :c1) ObjectPropertyAssertion(:f :u :c2)
                    ObjectPropertyAssertion(:r3 :c2 :d)
                )"#,
                &[":d"],
            ),
            // 17. Subproperty of a functional role merging endpoints that feed a property chain
            (
                "subproperty_of_functional_feeding_chain",
                r#"Prefix(:=<http://ex.org/>) Ontology(
                    Declaration(ObjectProperty(:subf)) Declaration(ObjectProperty(:f))
                    Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                    Declaration(ObjectProperty(:other))
                    SubObjectPropertyOf(:subf :f)
                    FunctionalObjectProperty(:f)
                    ObjectPropertyAssertion(:subf :u :b1) ObjectPropertyAssertion(:subf :u :b2)
                    SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                    ObjectPropertyAssertion(:r1 :a :b1) ObjectPropertyAssertion(:r2 :b2 :c)
                )"#,
                &[":c"],
            ),
        ];

        for (name, src, expected) in cases {
            let bound = NamedRoleBound::compute(src)
                .unwrap_or_else(|| panic!("NamedRoleBound::compute failed on case {name}"));
            let targets = bound.reachable_targets_by_full_iri(":other");
            for &exp in *expected {
                assert!(
                    targets.contains(exp),
                    "case {name}: missing expected target {exp} in {targets:?}"
                );
            }
        }
    }

    #[test]
    fn named_role_bound_covers_c4_c6_and_20_anonymous_routing_cases() {
        let _test_env = crate::test_env::read();
        let mut pad = String::new();
        for i in 0..10 {
            pad.push_str(&format!("Declaration(ObjectProperty(:pad{i}))\n"));
        }
        for i in 0..30 {
            pad.push_str(&format!("Declaration(NamedIndividual(:z{i}))\n"));
        }
        let cases: &[(&str, &str, &str, &[&str])] = &[
            (
                "c4_inv_func_anon_succ_inv_has_value",
                r#"Declaration(Class(:X4))
                   Declaration(ObjectProperty(:r4)) Declaration(ObjectProperty(:t4)) Declaration(ObjectProperty(:u4))
                   Declaration(NamedIndividual(:d4)) Declaration(NamedIndividual(:e4))
                   Declaration(NamedIndividual(:k4)) Declaration(NamedIndividual(:m4))
                   InverseFunctionalObjectProperty(:r4)
                   ClassAssertion(ObjectSomeValuesFrom(:r4 :X4) :d4)
                   SubClassOf(:X4 ObjectHasValue(ObjectInverseOf(:r4) :e4))
                   ObjectPropertyAssertion(:t4 :k4 :d4)
                   ObjectPropertyAssertion(:u4 :e4 :m4)"#,
                ":t4",
                &[":d4", ":e4"],
            ),
            (
                "c6_complement_min_cardinality_2_merge",
                r#"Declaration(ObjectProperty(:r6)) Declaration(ObjectProperty(:t6))
                   Declaration(NamedIndividual(:a6)) Declaration(NamedIndividual(:b6))
                   Declaration(NamedIndividual(:c6)) Declaration(NamedIndividual(:k6))
                   ClassAssertion(ObjectComplementOf(ObjectMinCardinality(2 :r6)) :a6)
                   ObjectPropertyAssertion(:r6 :a6 :b6)
                   ObjectPropertyAssertion(:r6 :a6 :c6)
                   ObjectPropertyAssertion(:t6 :k6 :b6)"#,
                ":t6",
                &[":b6", ":c6"],
            ),
            // M3.1: subrole existential successor into inverse-functional superrole with inverse HasValue
            (
                "m01_inv_func_subrole_anon_succ_inv_has_value",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:sub_r)) Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   SubObjectPropertyOf(:sub_r :r)
                   InverseFunctionalObjectProperty(:r)
                   ClassAssertion(ObjectSomeValuesFrom(:sub_r :X) :d)
                   SubClassOf(:X ObjectHasValue(ObjectInverseOf(:r) :e))
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            // M3.2: functional role with inverse existential and forward ObjectHasValue
            (
                "m02_func_inv_existential_has_value",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f)
                   ClassAssertion(ObjectSomeValuesFrom(ObjectInverseOf(:f) :X) :d)
                   SubClassOf(:X ObjectHasValue(:f :e))
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            // M3.3: named inverse property existential with functional role and ObjectHasValue
            (
                "m03_named_inv_prop_existential_func_has_value",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:inv_f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f)
                   InverseObjectProperties(:f :inv_f)
                   ClassAssertion(ObjectSomeValuesFrom(:inv_f :X) :d)
                   SubClassOf(:X ObjectHasValue(:f :e))
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            // M3.4: min cardinality 1 creating anonymous witness merged by max cardinality 1 on inverse role
            (
                "m04_min_card_anon_succ_max_card_inv_merge",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   SubClassOf(:A ObjectMaxCardinality(1 ObjectInverseOf(:r)))
                   ClassAssertion(ObjectMinCardinality(1 :r ObjectIntersectionOf(:A ObjectHasValue(ObjectInverseOf(:r) :e))) :d)
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            // M3.5: complement of min cardinality 2 on inverse role with anonymous witness
            (
                "m05_neg_min_card_2_inv_anon_merge",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   SubClassOf(:X ObjectComplementOf(ObjectMinCardinality(2 ObjectInverseOf(:r))))
                   SubClassOf(:X ObjectHasValue(ObjectInverseOf(:r) :e))
                   ClassAssertion(ObjectSomeValuesFrom(:r :X) :d)
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            // M3.6: anonymous subrole witness merging with asserted functional superrole target (no ObjectHasValue)
            (
                "m06_subrole_anon_merge_with_asserted_superrole_target",
                r#"Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   FunctionalObjectProperty(:f)
                   SubObjectPropertyOf(:other :f)
                   ObjectPropertyAssertion(:f :a :b)
                   ClassAssertion(ObjectSomeValuesFrom(:other owl:Thing) :a)"#,
                ":other",
                &[":b"],
            ),
            // M3.7: anonymous subrole witness merging with asserted functional superrole target, cascading to inverse-functional merge
            (
                "m07_subrole_anon_merge_cascading_to_inv_func",
                r#"Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f)
                   SubObjectPropertyOf(:r :f)
                   InverseFunctionalObjectProperty(:r)
                   ObjectPropertyAssertion(:f :b :c)
                   ObjectPropertyAssertion(:r :a :c)
                   ClassAssertion(ObjectSomeValuesFrom(:r owl:Thing) :b)
                   ObjectPropertyAssertion(:other :k :a)"#,
                ":other",
                &[":a", ":b"],
            ),
            // M3.8: cascade through two functional roles over anonymous witness
            (
                "m08_cascade_two_functional_roles_over_anon_witness",
                r#"Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:c1)) Declaration(NamedIndividual(:c2)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2)
                   ObjectPropertyAssertion(:f1 :a :b)
                   ClassAssertion(ObjectSomeValuesFrom(:f1 ObjectHasValue(:f2 :c1)) :a)
                   ObjectPropertyAssertion(:f2 :b :c2)
                   ObjectPropertyAssertion(:other :k :c1)"#,
                ":other",
                &[":c1", ":c2"],
            ),
            // M3.9: cascade through three functional roles over two-hop anonymous existential chain
            (
                "m09_cascade_three_level_anon_functional_chain",
                r#"Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2))
                   Declaration(ObjectProperty(:f3)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))
                   Declaration(NamedIndividual(:d1)) Declaration(NamedIndividual(:d2)) Declaration(NamedIndividual(:k))
                   FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2) FunctionalObjectProperty(:f3)
                   ObjectPropertyAssertion(:f1 :a :b)
                   ObjectPropertyAssertion(:f2 :b :c)
                   ObjectPropertyAssertion(:f3 :c :d2)
                   ClassAssertion(ObjectSomeValuesFrom(:f1 ObjectSomeValuesFrom(:f2 ObjectHasValue(:f3 :d1))) :a)
                   ObjectPropertyAssertion(:other :k :d1)"#,
                ":other",
                &[":d1", ":d2"],
            ),
            // M3.10: 3-role chain over two anonymous middle elements with nested ObjectHasValue
            (
                "m10_chain_over_two_anon_middle_elements_with_nested_has_value",
                r#"Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:r3)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:c))
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2 :r3) :other)
                   ClassAssertion(ObjectSomeValuesFrom(:r1 ObjectSomeValuesFrom(:r2 ObjectHasValue(:r3 :c))) :a)"#,
                ":other",
                &[":c"],
            ),
            // M3.11: chain over anonymous middle element created via named inverse existential
            (
                "m11_chain_over_anon_middle_via_named_inverse_existential",
                r#"Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   InverseObjectProperties(:r2 :s)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   ClassAssertion(ObjectSomeValuesFrom(:s ObjectHasValue(ObjectInverseOf(:r1) :a)) :b)"#,
                ":other",
                &[":b"],
            ),
            // M3.12: chain over anonymous middle element whose anonymous leaf merges with named target via functional superrole
            (
                "m12_chain_into_functional_merging_anon_leaf_with_named",
                r#"Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   SubObjectPropertyOf(:r2 :f)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   FunctionalObjectProperty(:f)
                   ClassAssertion(ObjectSomeValuesFrom(:r1 ObjectIntersectionOf(ObjectSomeValuesFrom(:r2 owl:Thing) ObjectHasValue(:f :b))) :a)"#,
                ":other",
                &[":b"],
            ),
            // M3.13: two anonymous witnesses merged via subroles of a functional role, cascading to inverse-functional merge
            (
                "m13_chain_into_functional_cascading_to_inv_func_merge",
                r#"Declaration(Class(:X1)) Declaration(Class(:X2))
                   Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:f_sub1))
                   Declaration(ObjectProperty(:f_sub2)) Declaration(ObjectProperty(:g)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:k)) Declaration(NamedIndividual(:m))
                   FunctionalObjectProperty(:f)
                   SubObjectPropertyOf(:f_sub1 :f)
                   SubObjectPropertyOf(:f_sub2 :f)
                   InverseFunctionalObjectProperty(:g)
                   SubClassOf(:X1 ObjectHasValue(ObjectInverseOf(:f_sub1) :k))
                   SubClassOf(:X2 ObjectHasValue(ObjectInverseOf(:f_sub2) :k))
                   ClassAssertion(ObjectSomeValuesFrom(:g :X1) :a)
                   ClassAssertion(ObjectSomeValuesFrom(:g :X2) :b)
                   ObjectPropertyAssertion(:other :m :a)"#,
                ":other",
                &[":a", ":b"],
            ),
            // M3.14: anonymous witness merged with named individual by inverse-functional role, feeding a 3-step chain
            (
                "m14_anon_witness_merged_by_inv_func_feeds_chain_middle",
                r#"Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:r3)) Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:c))
                   Declaration(NamedIndividual(:k)) Declaration(NamedIndividual(:m))
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2 :r3) :other)
                   InverseFunctionalObjectProperty(:f)
                   ClassAssertion(ObjectSomeValuesFrom(:r1 ObjectSomeValuesFrom(:r2 ObjectHasValue(:f :k))) :a)
                   ObjectPropertyAssertion(:f :m :k)
                   ObjectPropertyAssertion(:r3 :m :c)"#,
                ":other",
                &[":c"],
            ),
            // M3.15: tree folding across two functional subroles (no ObjectHasValue)
            (
                "m15_tree_folding_across_two_functional_subroles",
                r#"Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:r1))
                   Declaration(ObjectProperty(:r2)) Declaration(ObjectProperty(:inv_r2)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a))
                   FunctionalObjectProperty(:f)
                   SubObjectPropertyOf(:r1 :f)
                   SubObjectPropertyOf(:r2 :f)
                   InverseObjectProperties(:r2 :inv_r2)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :inv_r2) :other)
                   ClassAssertion(ObjectIntersectionOf(ObjectSomeValuesFrom(:r1 owl:Thing) ObjectSomeValuesFrom(:r2 owl:Thing)) :a)"#,
                ":other",
                &[":a"],
            ),
            // M3.16: inverse-functional parent merge in anonymous tree producing self-loop (no ObjectHasValue)
            (
                "m16_inv_func_parent_merge_in_anon_tree_self_loop",
                r#"Declaration(ObjectProperty(:g)) Declaration(ObjectProperty(:f1))
                   Declaration(ObjectProperty(:f2)) Declaration(ObjectProperty(:inv_f2)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a))
                   InverseFunctionalObjectProperty(:g)
                   SubObjectPropertyOf(:f1 :g)
                   SubObjectPropertyOf(:f2 :g)
                   InverseObjectProperties(:f2 :inv_f2)
                   SubObjectPropertyOf(ObjectPropertyChain(:f1 :inv_f2) :other)
                   ClassAssertion(ObjectSomeValuesFrom(:f1 ObjectSomeValuesFrom(:inv_f2 owl:Thing)) :a)"#,
                ":other",
                &[":a"],
            ),
            // M3.17: symmetric + functional role with anonymous successor and ObjectHasValue
            (
                "m17_symmetric_func_anon_succ_has_value_merge",
                r#"Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   SymmetricObjectProperty(:r)
                   FunctionalObjectProperty(:r)
                   ClassAssertion(ObjectSomeValuesFrom(:r ObjectHasValue(:r :e)) :d)
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
            // M3.18: transitive role over two anonymous steps merged with named target by functional role
            (
                "m18_transitive_role_over_two_anon_steps_and_func_merge",
                r#"Declaration(ObjectProperty(:other)) Declaration(ObjectProperty(:f))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:k))
                   TransitiveObjectProperty(:other)
                   FunctionalObjectProperty(:f)
                   ClassAssertion(ObjectSomeValuesFrom(:other ObjectSomeValuesFrom(:other ObjectHasValue(ObjectInverseOf(:f) :k))) :a)
                   ObjectPropertyAssertion(:f :k :b)
                   ObjectPropertyAssertion(:other :b :c)"#,
                ":other",
                &[":b", ":c"],
            ),
            // M3.19: anonymous witness with ObjectHasSelf on subrole of inverse-functional role merging with named source
            (
                "m19_anon_has_self_on_inv_func_subrole_self_loop_and_merge",
                r#"Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:k))
                   InverseFunctionalObjectProperty(:r)
                   SubObjectPropertyOf(:s :r)
                   ClassAssertion(ObjectSomeValuesFrom(:r ObjectHasSelf(:s)) :a)
                   ObjectPropertyAssertion(:r :b :a)
                   ObjectPropertyAssertion(:other :k :a)"#,
                ":other",
                &[":a", ":b"],
            ),
            // M3.20: negated ObjectAllValuesFrom creating anonymous witness with nested ObjectHasValue and inverse-functional merge
            (
                "m20_neg_all_values_anon_witness_with_nested_has_value_merge",
                r#"Declaration(Class(:X))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:e)) Declaration(NamedIndividual(:k))
                   InverseFunctionalObjectProperty(:r)
                   SubClassOf(:X ObjectHasValue(ObjectInverseOf(:r) :e))
                   ClassAssertion(ObjectComplementOf(ObjectAllValuesFrom(:r ObjectComplementOf(:X))) :d)
                   ObjectPropertyAssertion(:other :k :d)"#,
                ":other",
                &[":d", ":e"],
            ),
        ];

        for (name, body, role, expected) in cases {
            let doc = format!("Prefix(:=<http://ex.org/>)\nOntology(<http://ex.org/{name}>\n{pad}{body}\n)");
            let bound = NamedRoleBound::compute(&doc)
                .unwrap_or_else(|| panic!("NamedRoleBound::compute failed on case {name}"));
            let targets = bound.reachable_targets_by_full_iri(role);
            for &exp in *expected {
                assert!(
                    targets.contains(exp),
                    "case {name}: missing expected target {exp} for {role} in {targets:?}"
                );
            }
        }
    }
}
