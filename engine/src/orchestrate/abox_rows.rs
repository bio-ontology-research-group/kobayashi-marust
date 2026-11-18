//! Entailed object property values and different individuals between named
//! individuals (W5b, `km classify --values`, `--different`).
//!
//! # Semantics
//!
//! For a consistent ontology `O`, named individuals `a`, `b` and a named
//! object property `r` of the source (not `owl:topObjectProperty` or
//! `owl:bottomObjectProperty`):
//!
//! * `VALUE r a b` iff `O ⊨ r(a, b)`;
//! * `DIFFERENT a b` iff `O ⊨ a ≠ b`, once per pair with `a < b`.
//!
//! # Mechanism
//!
//! The realization run's probes `P_a ≡ {a}` plus, for every property `r` and
//! individual `b`, a fresh class `V_rb ≡ ∃r.{b}` (`--values`) and, for every
//! individual `b`, `N_b ≡ ¬{b}` (`--different`). The extension only defines
//! fresh names, so it is conservative, and `O ⊨ r(a, b)` iff `{a} ⊑ ∃r.{b}`
//! iff `P_a ⊑ V_rb`, and `O ⊨ a ≠ b` iff `{a} ⊑ ¬{b}` iff `P_a ⊑ N_b`. All
//! pairs come from the one classification of the extended ontology that the
//! realization already needs, instead of one consistency test per pair.

use std::collections::{BTreeMap, BTreeSet};

use super::realize::{fresh_namespace_for, public_name};
use super::{Classification, OrchestrateError};

/// The rows of `--values` and `--different`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AboxRows {
    /// `[r, a, b]` rows, sorted; present iff `--values`.
    pub values: Option<Vec<[String; 3]>>,
    /// `[a, b]` rows with `a < b`, sorted; present iff `--different`.
    pub different: Option<Vec<[String; 2]>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Probe {
    Value(usize, usize),
    Not(usize),
}

/// The probe classes of one extension.
#[derive(Clone, Debug)]
pub struct AboxProbes {
    probes: BTreeMap<String, Probe>,
    roles: Vec<String>,
    individuals: Vec<String>,
    values: bool,
    different: bool,
}

impl AboxProbes {
    pub(super) fn is_probe(&self, name: &str) -> bool {
        self.probes.contains_key(name)
    }
}

/// Sound upper bound on reachable public target individuals per object property
/// for ontologies with `SameIndividual` and/or `ObjectHasValue` where
/// [`crate::frontend::named_role_bound::NamedRoleBound`] declines.
struct FallbackTargetBound {
    unconstrained_target: BTreeSet<String>,
    targets: BTreeMap<String, BTreeSet<String>>,
}

fn is_top_object_property(token: &str) -> bool {
    matches!(
        token,
        "owl:topObjectProperty" | "<http://www.w3.org/2002/07/owl#topObjectProperty>"
    )
}

fn is_public_named_individual(token: &str) -> bool {
    !token.starts_with('"')
        && !token.starts_with("_:")
        && !crate::frontend::lenient::is_skolem_anon_iri(token)
}

impl FallbackTargetBound {
    fn compute(text: &str) -> Option<Self> {
        use crate::frontend::sexpr::Node;

        let mut raw_sources: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut raw_targets: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut unconstrained_source: BTreeSet<String> = BTreeSet::new();
        let mut unconstrained_target: BTreeSet<String> = BTreeSet::new();
        let mut merging_roles: BTreeSet<String> = BTreeSet::new();
        let mut subroles: Vec<((String, bool), (String, bool))> = Vec::new();
        let mut inverses: Vec<(String, String)> = Vec::new();
        let mut chains: Vec<(Vec<(String, bool)>, String)> = Vec::new();
        let mut same_groups: Vec<Vec<String>> = Vec::new();
        let mut disqualified = false;

        fn parse_role_expr(node: &Node<'_>) -> Option<(String, bool)> {
            match node {
                Node::Atom(tok) => {
                    if is_top_object_property(tok) {
                        None
                    } else {
                        Some((public_name(tok), false))
                    }
                }
                Node::List("ObjectInverseOf", args) => {
                    let plain = crate::frontend::parse::strip_annotations(args);
                    let Node::Atom(tok) = plain.first().copied()? else {
                        return None;
                    };
                    if is_top_object_property(tok) {
                        None
                    } else {
                        Some((public_name(tok), true))
                    }
                }
                _ => None,
            }
        }

        #[allow(clippy::too_many_arguments)]
        fn walk_expr(
            node: &Node<'_>,
            raw_sources: &mut BTreeMap<String, BTreeSet<String>>,
            raw_targets: &mut BTreeMap<String, BTreeSet<String>>,
            unconstrained_source: &mut BTreeSet<String>,
            unconstrained_target: &mut BTreeSet<String>,
            merging_roles: &mut BTreeSet<String>,
            disqualified: &mut bool,
        ) {
            if *disqualified {
                return;
            }
            let Node::List(head, args) = node else {
                if let Node::Atom(tok) = node {
                    if is_top_object_property(tok) {
                        *disqualified = true;
                    }
                }
                return;
            };
            let plain = crate::frontend::parse::strip_annotations(args);
            match *head {
                "Annotation" => {}
                "ObjectOneOf" => {
                    *disqualified = true;
                }
                "ObjectHasSelf" => {
                    if let Some(first) = plain.first().copied() {
                        if let Some((r, _)) = parse_role_expr(first) {
                            unconstrained_source.insert(r.clone());
                            unconstrained_target.insert(r);
                        } else {
                            *disqualified = true;
                        }
                    }
                }
                "ObjectHasValue" => {
                    let Some(role_node) = plain.first().copied() else {
                        *disqualified = true;
                        return;
                    };
                    let Some(Node::Atom(ind_tok)) = plain.get(1).copied() else {
                        *disqualified = true;
                        return;
                    };
                    let Some((r, inv)) = parse_role_expr(role_node) else {
                        *disqualified = true;
                        return;
                    };
                    if inv {
                        unconstrained_target.insert(r.clone());
                        if is_public_named_individual(ind_tok) {
                            raw_sources.entry(r).or_default().insert(public_name(ind_tok));
                        }
                    } else {
                        unconstrained_source.insert(r.clone());
                        if is_public_named_individual(ind_tok) {
                            raw_targets.entry(r).or_default().insert(public_name(ind_tok));
                        }
                    }
                }
                "ObjectMaxCardinality" | "ObjectExactCardinality" => {
                    if let Some(role_node) = plain.get(1).copied() {
                        if let Some((r, _)) = parse_role_expr(role_node) {
                            merging_roles.insert(r);
                        } else {
                            *disqualified = true;
                        }
                    }
                    for arg in plain.iter().skip(2) {
                        walk_expr(
                            arg,
                            raw_sources,
                            raw_targets,
                            unconstrained_source,
                            unconstrained_target,
                            merging_roles,
                            disqualified,
                        );
                    }
                }
                "ObjectSomeValuesFrom" | "ObjectAllValuesFrom" => {
                    if let Some(role_node) = plain.first().copied() {
                        if parse_role_expr(role_node).is_none() {
                            *disqualified = true;
                            return;
                        }
                    }
                    for arg in plain.iter().skip(1) {
                        walk_expr(
                            arg,
                            raw_sources,
                            raw_targets,
                            unconstrained_source,
                            unconstrained_target,
                            merging_roles,
                            disqualified,
                        );
                    }
                }
                "ObjectMinCardinality" => {
                    if let Some(role_node) = plain.get(1).copied() {
                        if parse_role_expr(role_node).is_none() {
                            *disqualified = true;
                            return;
                        }
                    }
                    for arg in plain.iter().skip(2) {
                        walk_expr(
                            arg,
                            raw_sources,
                            raw_targets,
                            unconstrained_source,
                            unconstrained_target,
                            merging_roles,
                            disqualified,
                        );
                    }
                }
                "DataSomeValuesFrom"
                | "DataAllValuesFrom"
                | "DataHasValue"
                | "DataMinCardinality"
                | "DataMaxCardinality"
                | "DataExactCardinality"
                | "DataIntersectionOf"
                | "DataUnionOf"
                | "DataComplementOf"
                | "DataOneOf"
                | "DatatypeRestriction" => {}
                _ => {
                    for arg in &plain {
                        walk_expr(
                            arg,
                            raw_sources,
                            raw_targets,
                            unconstrained_source,
                            unconstrained_target,
                            merging_roles,
                            disqualified,
                        );
                    }
                }
            }
        }

        crate::frontend::parse::for_each_ontology_child(text, |node| {
            if disqualified {
                return Ok(());
            }
            let Node::List(head, args) = node else {
                return Ok(());
            };
            let plain = crate::frontend::parse::strip_annotations(args);
            match *head {
                "Prefix"
                | "Import"
                | "Annotation"
                | "AnnotationAssertion"
                | "SubAnnotationPropertyOf"
                | "AnnotationPropertyDomain"
                | "AnnotationPropertyRange"
                | "Declaration" => {}
                "HasKey" | "DLSafeRule" => {
                    disqualified = true;
                }
                "EquivalentClasses" => {
                    if let Some(Node::Atom(first)) = plain.first().copied() {
                        if first.starts_with("<http://km.invalid/") {
                            return Ok(());
                        }
                    }
                    for arg in &plain {
                        walk_expr(
                            arg,
                            &mut raw_sources,
                            &mut raw_targets,
                            &mut unconstrained_source,
                            &mut unconstrained_target,
                            &mut merging_roles,
                            &mut disqualified,
                        );
                    }
                }
                "SubObjectPropertyOf" => {
                    if plain.len() != 2 {
                        disqualified = true;
                        return Ok(());
                    }
                    if let Node::Atom(sup_tok) = plain[1] {
                        if is_top_object_property(sup_tok) {
                            return Ok(());
                        }
                    }
                    let Some((sup_r, sup_inv)) = parse_role_expr(plain[1]) else {
                        disqualified = true;
                        return Ok(());
                    };
                    if let Node::List("ObjectPropertyChain", ch_args) = plain[0] {
                        let ch_plain = crate::frontend::parse::strip_annotations(ch_args);
                        let mut steps = Vec::with_capacity(ch_plain.len());
                        for step in ch_plain {
                            let Some(sr) = parse_role_expr(step) else {
                                disqualified = true;
                                return Ok(());
                            };
                            steps.push(sr);
                        }
                        if sup_inv {
                            let rev: Vec<(String, bool)> =
                                steps.into_iter().rev().map(|(r, inv)| (r, !inv)).collect();
                            chains.push((rev, sup_r));
                        } else {
                            chains.push((steps, sup_r));
                        }
                    } else if let Some(sub_r) = parse_role_expr(plain[0]) {
                        subroles.push((sub_r, (sup_r, sup_inv)));
                    } else {
                        disqualified = true;
                    }
                }
                "EquivalentObjectProperties" => {
                    let mut parsed = Vec::with_capacity(plain.len());
                    for item in &plain {
                        let Some(r) = parse_role_expr(item) else {
                            disqualified = true;
                            return Ok(());
                        };
                        parsed.push(r);
                    }
                    for i in 0..parsed.len() {
                        let next = (i + 1) % parsed.len();
                        subroles.push((parsed[i].clone(), parsed[next].clone()));
                        subroles.push((parsed[next].clone(), parsed[i].clone()));
                    }
                }
                "InverseObjectProperties" => {
                    if plain.len() == 2 {
                        if let (Some((r1, inv1)), Some((r2, inv2))) =
                            (parse_role_expr(plain[0]), parse_role_expr(plain[1]))
                        {
                            if inv1 == inv2 {
                                inverses.push((r1, r2));
                            } else {
                                subroles.push(((r1.clone(), false), (r2.clone(), false)));
                                subroles.push(((r2, false), (r1, false)));
                            }
                        } else {
                            disqualified = true;
                        }
                    }
                }
                "SymmetricObjectProperty" => {
                    if let Some(first) = plain.first().copied() {
                        if let Some((r, _)) = parse_role_expr(first) {
                            inverses.push((r.clone(), r));
                        } else {
                            disqualified = true;
                        }
                    }
                }
                "TransitiveObjectProperty" => {
                    if let Some(first) = plain.first().copied() {
                        if let Some((r, inv)) = parse_role_expr(first) {
                            chains.push((vec![(r.clone(), inv), (r.clone(), inv)], r));
                        } else {
                            disqualified = true;
                        }
                    }
                }
                "ReflexiveObjectProperty" => {
                    if let Some(first) = plain.first().copied() {
                        if let Some((r, _)) = parse_role_expr(first) {
                            unconstrained_source.insert(r.clone());
                            unconstrained_target.insert(r);
                        } else {
                            disqualified = true;
                        }
                    }
                }
                "FunctionalObjectProperty" | "InverseFunctionalObjectProperty" => {
                    if let Some(first) = plain.first().copied() {
                        if let Some((r, _)) = parse_role_expr(first) {
                            merging_roles.insert(r);
                        } else {
                            disqualified = true;
                        }
                    }
                }
                "AsymmetricObjectProperty"
                | "IrreflexiveObjectProperty"
                | "DisjointObjectProperties" => {}
                "ObjectPropertyDomain" | "ObjectPropertyRange" => {
                    if let Some(first) = plain.first().copied() {
                        if parse_role_expr(first).is_none() {
                            disqualified = true;
                            return Ok(());
                        }
                    }
                    for arg in plain.iter().skip(1) {
                        walk_expr(
                            arg,
                            &mut raw_sources,
                            &mut raw_targets,
                            &mut unconstrained_source,
                            &mut unconstrained_target,
                            &mut merging_roles,
                            &mut disqualified,
                        );
                    }
                }
                "ObjectPropertyAssertion" => {
                    if plain.len() == 3 {
                        let Some((r, inv)) = parse_role_expr(plain[0]) else {
                            disqualified = true;
                            return Ok(());
                        };
                        if let (Node::Atom(s_tok), Node::Atom(o_tok)) = (plain[1], plain[2]) {
                            let (src_tok, dst_tok) = if inv { (o_tok, s_tok) } else { (s_tok, o_tok) };
                            if is_public_named_individual(src_tok) {
                                raw_sources.entry(r.clone()).or_default().insert(public_name(src_tok));
                            }
                            if is_public_named_individual(dst_tok) {
                                raw_targets.entry(r).or_default().insert(public_name(dst_tok));
                            }
                        }
                    }
                }
                "NegativeObjectPropertyAssertion"
                | "DataPropertyAssertion"
                | "NegativeDataPropertyAssertion"
                | "DifferentIndividuals"
                | "SubDataPropertyOf"
                | "EquivalentDataProperties"
                | "DisjointDataProperties"
                | "DataPropertyDomain"
                | "DataPropertyRange"
                | "FunctionalDataProperty"
                | "DatatypeDefinition" => {}
                "SameIndividual" => {
                    let mut group = Vec::new();
                    for item in &plain {
                        if let Node::Atom(tok) = item {
                            if is_public_named_individual(tok) {
                                group.push(public_name(tok));
                            }
                        }
                    }
                    if group.len() >= 2 {
                        same_groups.push(group);
                    }
                }
                _ => {
                    for arg in &plain {
                        walk_expr(
                            arg,
                            &mut raw_sources,
                            &mut raw_targets,
                            &mut unconstrained_source,
                            &mut unconstrained_target,
                            &mut merging_roles,
                            &mut disqualified,
                        );
                    }
                }
            }
            Ok(())
        })
        .ok()?;

        if disqualified {
            return None;
        }

        // Build SameIndividual equivalence classes.
        let mut same_adj: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for group in &same_groups {
            for a in group {
                let entry = same_adj.entry(a.clone()).or_default();
                for b in group {
                    entry.insert(b.clone());
                }
            }
        }
        let mut same_class: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for start in same_adj.keys() {
            if same_class.contains_key(start) {
                continue;
            }
            let mut comp = BTreeSet::new();
            let mut stack = vec![start.clone()];
            while let Some(cur) = stack.pop() {
                if comp.insert(cur.clone()) {
                    if let Some(nbrs) = same_adj.get(&cur) {
                        for n in nbrs {
                            if !comp.contains(n) {
                                stack.push(n.clone());
                            }
                        }
                    }
                }
            }
            for member in &comp {
                same_class.insert(member.clone(), comp.clone());
            }
        }
        for set in raw_sources.values_mut().chain(raw_targets.values_mut()) {
            let extra: Vec<String> = set
                .iter()
                .flat_map(|ind| same_class.get(ind).into_iter().flatten().cloned())
                .collect();
            set.extend(extra);
        }

        // ConvertInverseRoles into signed subroles.
        for (r1, r2) in &inverses {
            subroles.push(((r1.clone(), false), (r2.clone(), true)));
            subroles.push(((r2.clone(), true), (r1.clone(), false)));
            subroles.push(((r1.clone(), true), (r2.clone(), false)));
            subroles.push(((r2.clone(), false), (r1.clone(), true)));
        }

        // Propagate sources, targets, unconstrained_source, unconstrained_target to fixpoint.
        let get_set = |r: &str, inv: bool, src: &BTreeMap<String, BTreeSet<String>>, dst: &BTreeMap<String, BTreeSet<String>>| -> Vec<String> {
            let map = if inv { src } else { dst };
            map.get(r).into_iter().flatten().cloned().collect()
        };
        let is_unconstrained_dst = |r: &str, inv: bool, usrc: &BTreeSet<String>, udst: &BTreeSet<String>| -> bool {
            if inv { usrc.contains(r) } else { udst.contains(r) }
        };
        let is_unconstrained_src = |r: &str, inv: bool, usrc: &BTreeSet<String>, udst: &BTreeSet<String>| -> bool {
            if inv { udst.contains(r) } else { usrc.contains(r) }
        };

        loop {
            let mut changed = false;
            for ((sub_r, sub_inv), (sup_r, sup_inv)) in &subroles {
                let dst_vals = get_set(sub_r, *sub_inv, &raw_sources, &raw_targets);
                let src_vals = get_set(sub_r, !*sub_inv, &raw_sources, &raw_targets);
                let ud = is_unconstrained_dst(sub_r, *sub_inv, &unconstrained_source, &unconstrained_target);
                let us = is_unconstrained_src(sub_r, *sub_inv, &unconstrained_source, &unconstrained_target);
                if *sup_inv {
                    let e_src = raw_sources.entry(sup_r.clone()).or_default();
                    for v in dst_vals {
                        changed |= e_src.insert(v);
                    }
                    let e_dst = raw_targets.entry(sup_r.clone()).or_default();
                    for v in src_vals {
                        changed |= e_dst.insert(v);
                    }
                    if ud {
                        changed |= unconstrained_source.insert(sup_r.clone());
                    }
                    if us {
                        changed |= unconstrained_target.insert(sup_r.clone());
                    }
                } else {
                    let e_dst = raw_targets.entry(sup_r.clone()).or_default();
                    for v in dst_vals {
                        changed |= e_dst.insert(v);
                    }
                    let e_src = raw_sources.entry(sup_r.clone()).or_default();
                    for v in src_vals {
                        changed |= e_src.insert(v);
                    }
                    if ud {
                        changed |= unconstrained_target.insert(sup_r.clone());
                    }
                    if us {
                        changed |= unconstrained_source.insert(sup_r.clone());
                    }
                }
            }
            for (steps, sup_r) in &chains {
                if let (Some((first_r, first_inv)), Some((last_r, last_inv))) = (steps.first(), steps.last()) {
                    let dst_vals = get_set(last_r, *last_inv, &raw_sources, &raw_targets);
                    let src_vals = get_set(first_r, !*first_inv, &raw_sources, &raw_targets);
                    let ud = is_unconstrained_dst(last_r, *last_inv, &unconstrained_source, &unconstrained_target);
                    let us = is_unconstrained_src(first_r, *first_inv, &unconstrained_source, &unconstrained_target);
                    let e_dst = raw_targets.entry(sup_r.clone()).or_default();
                    for v in dst_vals {
                        changed |= e_dst.insert(v);
                    }
                    let e_src = raw_sources.entry(sup_r.clone()).or_default();
                    for v in src_vals {
                        changed |= e_src.insert(v);
                    }
                    if ud {
                        changed |= unconstrained_target.insert(sup_r.clone());
                    }
                    if us {
                        changed |= unconstrained_source.insert(sup_r.clone());
                    }
                }
            }
            if !merging_roles.is_empty() {
                // If any active role has max-cardinality or (inverse-)functionality,
                // conservatively pool all known named endpoints across active roles.
                let any_active_merging = merging_roles.iter().any(|r| {
                    unconstrained_source.contains(r)
                        || unconstrained_target.contains(r)
                        || raw_sources.get(r).is_some_and(|s| !s.is_empty())
                        || raw_targets.get(r).is_some_and(|s| !s.is_empty())
                });
                if any_active_merging {
                    let mut all_known = BTreeSet::new();
                    for s in raw_sources.values().chain(raw_targets.values()) {
                        all_known.extend(s.iter().cloned());
                    }
                    for r in &merging_roles {
                        let e_dst = raw_targets.entry(r.clone()).or_default();
                        for v in &all_known {
                            changed |= e_dst.insert(v.clone());
                        }
                        let e_src = raw_sources.entry(r.clone()).or_default();
                        for v in &all_known {
                            changed |= e_src.insert(v.clone());
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        Some(FallbackTargetBound {
            unconstrained_target,
            targets: raw_targets,
        })
    }
}

/// The probe axioms for `roles` and `individuals` (source spellings).
pub(super) fn extension(
    text: &str,
    roles: &[String],
    individuals: &[String],
    values: bool,
    different: bool,
) -> (String, AboxProbes) {
    let ns = fresh_namespace_for(text, "aboxrows");
    let mut out = String::new();
    let mut probes = BTreeMap::new();
    if values {
        let large = roles.len().saturating_mul(individuals.len()) >= 256;
        let role_bound = large
            .then(|| crate::frontend::named_role_bound::NamedRoleBound::compute(text))
            .flatten();
        let fallback_bound = (large && role_bound.is_none())
            .then(|| FallbackTargetBound::compute(text))
            .flatten();
        for (r, role) in roles.iter().enumerate() {
            let pub_role = public_name(role);
            if let Some(bound) = &role_bound {
                let has_self = bound.role_has_self_by_full_iri(&pub_role);
                let targets = bound.reachable_targets_by_full_iri(&pub_role);
                if !has_self {
                    for (b, individual) in individuals.iter().enumerate() {
                        if !targets.contains(&public_name(individual)) {
                            continue;
                        }
                        let probe = format!("{ns}value{r}_{b}");
                        out.push_str(&format!(
                            "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({role} ObjectOneOf({individual})))\n"
                        ));
                        probes.insert(probe, Probe::Value(r, b));
                    }
                    continue;
                }
            } else if let Some(bound) = &fallback_bound {
                if !bound.unconstrained_target.contains(&pub_role) {
                    if let Some(targets) = bound.targets.get(&pub_role) {
                        for (b, individual) in individuals.iter().enumerate() {
                            if !targets.contains(&public_name(individual)) {
                                continue;
                            }
                            let probe = format!("{ns}value{r}_{b}");
                            out.push_str(&format!(
                                "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({role} ObjectOneOf({individual})))\n"
                            ));
                            probes.insert(probe, Probe::Value(r, b));
                        }
                    }
                    continue;
                }
            }
            for (b, individual) in individuals.iter().enumerate() {
                let probe = format!("{ns}value{r}_{b}");
                out.push_str(&format!(
                    "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({role} ObjectOneOf({individual})))\n"
                ));
                probes.insert(probe, Probe::Value(r, b));
            }
        }
    }
    if different {
        for (b, individual) in individuals.iter().enumerate() {
            let probe = format!("{ns}not{b}");
            out.push_str(&format!(
                "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectComplementOf(ObjectOneOf({individual})))\n"
            ));
            probes.insert(probe, Probe::Not(b));
        }
    }
    let probes = AboxProbes {
        probes,
        roles: roles.iter().map(|r| public_name(r)).collect(),
        individuals: individuals.iter().map(|a| public_name(a)).collect(),
        values,
        different,
    };
    (out, probes)
}

/// Remove the probes from the classification and read the rows off the
/// subsumptions `P_a ⊑ probe`. `individual_of` maps the realization probe
/// class of each individual to its public name.
pub(super) fn split(
    extended: &mut Classification,
    probes: &AboxProbes,
    individual_of: &BTreeMap<String, String>,
) -> Result<AboxRows, OrchestrateError> {
    let probe = |name: &str| probes.probes.get(name).copied();
    let unsatisfiable: Vec<Probe> = extended.unsatisfiable.iter().filter_map(|n| probe(n)).collect();
    extended.unsatisfiable.retain(|name| probe(name).is_none());
    let mut values = BTreeSet::new();
    let mut different = BTreeSet::new();
    extended.subsumptions.retain(|[low, high]| {
        let (low_probe, high_probe) = (probe(low), probe(high));
        if low_probe.is_none() && high_probe.is_none() {
            return true;
        }
        if let (Some(a), Some(p)) = (individual_of.get(low), high_probe) {
            match p {
                Probe::Value(r, b) => {
                    values.insert([probes.roles[r].clone(), a.clone(), probes.individuals[b].clone()]);
                }
                Probe::Not(b) => {
                    let b = &probes.individuals[b];
                    if a != b {
                        let (x, y) = if a < b { (a, b) } else { (b, a) };
                        different.insert([x.clone(), y.clone()]);
                    }
                }
            }
        }
        false
    });
    if extended.consistent && unsatisfiable.iter().any(|p| matches!(p, Probe::Not(_))) {
        // `¬{b}` is unsatisfiable only when the domain is `{b}`; then no
        // other individual is different from `b`, and the rows above are
        // already right. Nothing to report.
    }
    Ok(AboxRows {
        values: probes.values.then(|| values.into_iter().collect()),
        different: probes.different.then(|| different.into_iter().collect()),
    })
}
