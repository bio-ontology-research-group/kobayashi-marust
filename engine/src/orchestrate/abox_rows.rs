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

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::frontend::sexpr::Node;

use super::realize::{fresh_namespace_for, prefix_bindings, public_name, Realization};
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
        let role_bound = (roles.len().saturating_mul(individuals.len()) >= 256)
            .then(|| crate::frontend::named_role_bound::NamedRoleBound::compute(text))
            .flatten();
        for (r, role) in roles.iter().enumerate() {
            let pub_role = public_name(role);
            if let Some(bound) = &role_bound {
                let has_self = bound.role_has_self_by_full_iri(&pub_role);
                if !has_self {
                    let targets = bound.reachable_targets_by_full_iri(&pub_role);
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

/// Result of analyzing the exported consistency model for `--values` and
/// `--different`: deductively proved rows plus any undecided residual queries
/// that could not be refuted by a verified model or merged-pair saturation and
/// therefore go to the exact probe reduction.
#[derive(Clone, Debug, Default)]
pub(super) struct ModelAboxPlan {
    pub proved_values: BTreeSet<[String; 3]>,
    pub proved_different: BTreeSet<[String; 2]>,
    pub residual_value_targets: BTreeSet<(usize, usize)>,
    pub residual_value_sources: BTreeSet<usize>,
    pub residual_different_pairs: BTreeSet<(usize, usize)>,
}

/// Build the conservative probe extension for only the residual `(r, b)` value
/// targets and `(a, b)` different-individual pairs that were neither
/// constructively proved nor refuted by the model shortcut.
pub(super) fn residual_extension(
    text: &str,
    roles: &[String],
    individuals: &[String],
    values: bool,
    different: bool,
    plan: &ModelAboxPlan,
) -> (String, Vec<(String, String)>, AboxProbes) {
    let ind_ns = fresh_namespace_for(text, "realize");
    let ns = fresh_namespace_for(text, "aboxrows");
    let mut need_ind_probes: BTreeSet<usize> = BTreeSet::new();
    let mut need_not_probes: BTreeSet<usize> = BTreeSet::new();
    let mut kept_value_targets: Vec<(usize, usize)> = Vec::new();
    if values && !plan.residual_value_targets.is_empty() {
        let role_bound = (roles.len().saturating_mul(individuals.len()) >= 256)
            .then(|| crate::frontend::named_role_bound::NamedRoleBound::compute(text))
            .flatten();
        for &(r, b) in &plan.residual_value_targets {
            if let (Some(role), Some(ind)) = (roles.get(r), individuals.get(b)) {
                if let Some(bound) = &role_bound {
                    let pub_role = public_name(role);
                    if !bound.role_has_self_by_full_iri(&pub_role) {
                        let targets = bound.reachable_targets_by_full_iri(&pub_role);
                        if !targets.contains(&public_name(ind)) {
                            continue;
                        }
                    }
                }
                kept_value_targets.push((r, b));
            }
        }
    }
    if !kept_value_targets.is_empty() {
        need_ind_probes.extend(plan.residual_value_sources.iter().copied());
    }
    if different {
        for &(a, b) in &plan.residual_different_pairs {
            need_ind_probes.insert(a);
            need_not_probes.insert(b);
        }
    }
    let mut out = String::new();
    let mut ind_probes = Vec::with_capacity(need_ind_probes.len());
    for i in need_ind_probes {
        if let Some(ind) = individuals.get(i) {
            let probe = format!("{ind_ns}individual{i}");
            out.push_str(&format!(
                "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectOneOf({ind}))\n"
            ));
            ind_probes.push((probe, public_name(ind)));
        }
    }
    let mut probes = BTreeMap::new();
    for (r, b) in kept_value_targets {
        if let (Some(role), Some(ind)) = (roles.get(r), individuals.get(b)) {
            let probe = format!("{ns}value{r}_{b}");
            out.push_str(&format!(
                "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({role} ObjectOneOf({ind})))\n"
            ));
            probes.insert(probe, Probe::Value(r, b));
        }
    }
    if different {
        for b in need_not_probes {
            if let Some(ind) = individuals.get(b) {
                let probe = format!("{ns}not{b}");
                out.push_str(&format!(
                    "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectComplementOf(ObjectOneOf({ind})))\n"
                ));
                probes.insert(probe, Probe::Not(b));
            }
        }
    }
    let abox_probes = AboxProbes {
        probes,
        roles: roles.iter().map(|r| public_name(r)).collect(),
        individuals: individuals.iter().map(|a| public_name(a)).collect(),
        values,
        different,
    };
    (out, ind_probes, abox_probes)
}

#[allow(clippy::too_many_arguments)]
/// Guard bound on the rounds of `saturate_horn_in_place`; reaching it
/// declines the model plan instead of using a partly saturated model.
const HORN_SATURATION_MAX_ROUNDS: usize = 100_000;
/// Guard bound on the steps of one quotient-graph merge test; reaching it
/// makes the pair `Undecided` (exact residual probe).
const GRAPH_MERGE_MAX_STEPS: usize = 32;

pub(super) fn from_exported_model(
    text: &str,
    roles: &[String],
    individuals: &[String],
    values_requested: bool,
    different_requested: bool,
    classification: &Classification,
    realization: &Realization,
    raw: &super::model_export::RawModel,
    meta: &super::frontend_run::Meta,
) -> Option<ModelAboxPlan> {
    if !classification.consistent {
        return Some(ModelAboxPlan::default());
    }
    let bound_disabled = crate::frontend::named_role_bound::NamedRoleBound::bound_disabled();
    if bound_disabled && !different_requested {
        return None;
    }
    if !matches!(raw.route, "el-canonical" | "cb-horn" | "ht-bridge") {
        return None;
    }
    if raw.partial_reason.is_some() && raw.route != "ht-bridge" {
        return None;
    }
    if text.contains("DLSafeRule(") || text.contains("HasKey(") {
        return None;
    }

    let prefixes = prefix_bindings(text).ok()?;
    let expand_tok = |token: &str| -> String {
        let trimmed = token.trim();
        if let Some(iri) = trimmed.strip_prefix('<').and_then(|t| t.strip_suffix('>')) {
            return iri.to_string();
        }
        trimmed
            .split_once(':')
            .and_then(|(prefix, local)| prefixes.get(prefix).map(|ns| format!("{ns}{local}")))
            .unwrap_or_else(|| trimmed.to_string())
    };

    let mut ind_lookup: HashMap<String, String> = HashMap::new();
    let mut pub_ind_to_idx: HashMap<String, usize> = HashMap::new();
    let mut pub_individuals: Vec<String> = Vec::with_capacity(individuals.len());
    for (idx, tok) in individuals.iter().enumerate() {
        let pub_ind = public_name(tok);
        let exp_ind = expand_tok(tok);
        ind_lookup.insert(pub_ind.clone(), pub_ind.clone());
        ind_lookup.insert(exp_ind, pub_ind.clone());
        pub_ind_to_idx.insert(pub_ind.clone(), idx);
        pub_individuals.push(pub_ind);
    }
    for (short, full) in &meta.iri_map {
        if let Some(pub_ind) = ind_lookup.get(full).cloned() {
            ind_lookup.entry(short.clone()).or_insert(pub_ind);
        }
    }

    let mut role_lookup: HashMap<String, String> = HashMap::new();
    let mut pub_role_to_idx: HashMap<String, usize> = HashMap::new();
    for (idx, tok) in roles.iter().enumerate() {
        let pub_r = public_name(tok);
        let exp_r = expand_tok(tok);
        role_lookup.insert(pub_r.clone(), pub_r.clone());
        role_lookup.insert(exp_r, pub_r.clone());
        pub_role_to_idx.insert(pub_r, idx);
    }
    let mut full_to_short: HashMap<&str, &str> = HashMap::with_capacity(meta.iri_map.len());
    for (short, full) in &meta.iri_map {
        full_to_short.entry(full.as_str()).or_insert(short.as_str());
        if let Some(pub_r) = role_lookup.get(full).cloned() {
            role_lookup.entry(short.clone()).or_insert(pub_r);
        }
    }
    let resolve_role_short = |tok: &str| -> String {
        let pub_r = public_name(tok);
        let exp_r = expand_tok(tok);
        if let Some(&short) = full_to_short
            .get(exp_r.as_str())
            .or_else(|| full_to_short.get(pub_r.as_str()))
        {
            return short.to_string();
        }
        pub_r
    };
    let resolve_class_iri = |tok: &str| -> String {
        let exp = expand_tok(tok);
        meta.iri_map.get(&exp).cloned().unwrap_or(exp)
    };

    let mut one_refl: HashSet<(usize, String, usize)> = HashSet::new();
    let _ = crate::engine::close_edges_under_rbox_rows(&meta.rbox, 1, &mut one_refl);
    let refl_roles: Vec<String> = one_refl.into_iter().map(|(_, r, _)| r).collect();

    let use_base = raw.route == "ht-bridge" && !raw.base_labels.is_empty();
    let mut labels: Vec<Vec<String>>;
    let mut edge_set: HashSet<(usize, String, usize)>;
    let mut elem_inds: Vec<Vec<String>>;
    let mut ind_to_elem: HashMap<String, usize> = HashMap::new();
    // Individuals the exported model does not contain (stand-in elements).
    let mut stand_ins: HashSet<String> = HashSet::new();

    if raw.abox_elided || raw.route == "el-canonical" {
        let mut init_same: Vec<(String, String)> = Vec::new();
        for [a, b] in &realization.same {
            init_same.push((a.clone(), b.clone()));
        }
        if text.contains("SameIndividual(") {
            let _ = crate::frontend::parse::for_each_ontology_child(text, |node| {
                let Node::List(head, args) = node else {
                    return Ok(());
                };
                if *head == "SameIndividual" {
                    let inds: Vec<String> = args
                        .iter()
                        .filter(|a| a.head() != Some("Annotation"))
                        .filter_map(|n| n.as_atom())
                        .filter_map(|t| {
                            ind_lookup
                                .get(&expand_tok(t))
                                .or_else(|| ind_lookup.get(&public_name(t)))
                                .cloned()
                        })
                        .collect();
                    for w in inds.windows(2) {
                        init_same.push((w[0].clone(), w[1].clone()));
                    }
                }
                Ok(())
            });
        }
        let mut s_adj: HashMap<&str, Vec<&str>> = HashMap::new();
        for (a, b) in &init_same {
            s_adj.entry(a.as_str()).or_default().push(b.as_str());
            s_adj.entry(b.as_str()).or_default().push(a.as_str());
        }
        labels = Vec::new();
        edge_set = HashSet::new();
        elem_inds = Vec::new();
        for pub_ind in &pub_individuals {
            if ind_to_elem.contains_key(pub_ind) {
                continue;
            }
            let mut comp: Vec<String> = Vec::new();
            let mut stack = vec![pub_ind.as_str()];
            let u_new = labels.len();
            while let Some(cur) = stack.pop() {
                if !ind_to_elem.contains_key(cur) {
                    ind_to_elem.insert(cur.to_string(), u_new);
                    comp.push(cur.to_string());
                    if let Some(nbrs) = s_adj.get(cur) {
                        stack.extend(nbrs.iter().copied());
                    }
                }
            }
            comp.sort();
            comp.dedup();
            let lbl: Vec<String> = comp.iter().map(|i| format!("__nom__{i}")).collect();
            labels.push(lbl);
            elem_inds.push(comp);
            for r in &refl_roles {
                edge_set.insert((u_new, r.clone(), u_new));
            }
        }
    } else {
        labels = if use_base {
            raw.base_labels.clone()
        } else {
            raw.labels.clone()
        };
        edge_set = if use_base {
            raw.base_edges.iter().cloned().collect()
        } else {
            raw.edges.iter().cloned().collect()
        };
        elem_inds = vec![Vec::new(); labels.len()];
        for (u, lbl) in labels.iter().enumerate() {
            for item in lbl.iter().chain(raw.contexts.get(u)) {
                if let Some(rest) = item.strip_prefix("__nom__") {
                    let full = meta.iri_map.get(rest).map(String::as_str).unwrap_or(rest);
                    if let Some(pub_ind) = ind_lookup
                        .get(full)
                        .or_else(|| ind_lookup.get(rest))
                        .cloned()
                    {
                        if !elem_inds[u].contains(&pub_ind) {
                            elem_inds[u].push(pub_ind.clone());
                        }
                        ind_to_elem.entry(pub_ind).or_insert(u);
                    }
                }
            }
            elem_inds[u].sort();
            elem_inds[u].dedup();
        }
        for pub_ind in &pub_individuals {
            if !ind_to_elem.contains_key(pub_ind) {
                let u_new = labels.len();
                stand_ins.insert(pub_ind.clone());
                labels.push(vec![format!("__nom__{pub_ind}")]);
                elem_inds.push(vec![pub_ind.clone()]);
                ind_to_elem.insert(pub_ind.clone(), u_new);
                for r in &refl_roles {
                    edge_set.insert((u_new, r.clone(), u_new));
                }
            }
        }
    }

    let n_elems = labels.len();
    let mut elem_classes: Vec<HashSet<String>> = vec![HashSet::new(); n_elems];
    let mut entailed_elem_classes: Vec<HashSet<String>> = vec![HashSet::new(); n_elems];
    for u in 0..n_elems {
        for ind in &elem_inds[u] {
            let nom = format!("__nom__{ind}");
            elem_classes[u].insert(nom.clone());
            entailed_elem_classes[u].insert(nom);
        }
    }
    for (u, lbl) in labels.iter().enumerate() {
        for item in lbl {
            if item.starts_with("__") || item.starts_with("Q_") {
                continue;
            }
            let full = meta.iri_map.get(item).cloned().unwrap_or_else(|| item.clone());
            if !full.starts_with("http://km.invalid/") && !full.starts_with("_:") {
                elem_classes[u].insert(full);
            }
        }
    }
    for [ind_pub, class_pub] in &realization.types {
        if let Some(&u) = ind_to_elem.get(ind_pub) {
            let exp = expand_tok(class_pub);
            elem_classes[u].insert(exp.clone());
            elem_classes[u].insert(class_pub.clone());
            entailed_elem_classes[u].insert(exp);
            entailed_elem_classes[u].insert(class_pub.clone());
        }
    }

    let mut subs_map: HashMap<String, Vec<String>> = HashMap::new();
    for [sub, sup] in &classification.subsumptions {
        if !sub.starts_with("http://km.invalid/") && !sup.starts_with("http://km.invalid/") {
            subs_map
                .entry(expand_tok(sub))
                .or_default()
                .push(expand_tok(sup));
            subs_map.entry(sub.clone()).or_default().push(sup.clone());
        }
    }
    let close_elem_classes = |classes: &mut [HashSet<String>]| {
        for set in classes.iter_mut() {
            let mut stack: Vec<String> = set.iter().cloned().collect();
            while let Some(c) = stack.pop() {
                if let Some(sups) = subs_map.get(&c) {
                    for sup in sups {
                        if set.insert(sup.clone()) {
                            stack.push(sup.clone());
                        }
                    }
                }
            }
        }
    };
    close_elem_classes(&mut elem_classes);

    let mut same_pairs: Vec<(String, String)> = Vec::new();
    for [a, b] in &realization.same {
        same_pairs.push((a.clone(), b.clone()));
    }
    let mut diff_ind_groups: Vec<Vec<String>> = Vec::new();
    let mut disjoint_class_groups: Vec<Vec<String>> = Vec::new();
    let mut class_disjoint_inds: Vec<(String, String)> = Vec::new();
    let mut class_has_value: Vec<(String, String, bool, String)> = Vec::new();
    let mut class_has_self: Vec<(String, String)> = Vec::new();
    let mut source_role_assertions: Vec<(usize, String, usize)> = Vec::new();
    let mut neg_role_assertions: Vec<(String, usize, usize)> = Vec::new();
    let mut irrefl_roles: HashSet<String> = HashSet::new();
    let mut asym_roles: HashSet<String> = HashSet::new();
    let mut disjoint_role_groups: Vec<Vec<String>> = Vec::new();
    let mut func_obj_roles: HashSet<String> = HashSet::new();
    let mut inv_func_obj_roles: HashSet<String> = HashSet::new();
    let mut func_data_props: HashSet<String> = HashSet::new();
    let mut sub_data_props: HashMap<String, Vec<String>> = HashMap::new();
    let mut data_domains: Vec<(String, String)> = Vec::new();
    let mut obj_domains: Vec<(String, String)> = Vec::new();
    let mut obj_ranges: Vec<(String, String)> = Vec::new();
    let mut source_data_assertions: Vec<(usize, String, String)> = Vec::new();
    let mut elem_neg_classes: Vec<HashSet<String>> = vec![HashSet::new(); n_elems];

    fn collect_has_value_rhs<'a>(
        node: &'a Node<'a>,
        out: &mut Vec<(&'a str, bool, &'a str)>,
        self_out: &mut Vec<&'a str>,
    ) {
        let Node::List(head, args) = node else { return };
        let plain: Vec<&Node<'a>> = args
            .iter()
            .filter(|a| a.head() != Some("Annotation"))
            .collect();
        match *head {
            "ObjectIntersectionOf" => {
                for op in plain {
                    collect_has_value_rhs(op, out, self_out);
                }
            }
            "ObjectHasSelf" if !plain.is_empty() => match plain[0] {
                Node::Atom(r) => self_out.push(r),
                Node::List("ObjectInverseOf", r_args) => {
                    if let Some(r) = r_args.first().and_then(Node::as_atom) {
                        self_out.push(r);
                    }
                }
                _ => {}
            },
            "ObjectHasValue" if plain.len() >= 2 => {
                if let Some(ind) = plain[1].as_atom() {
                    match plain[0] {
                        Node::Atom(r) => out.push((r, false, ind)),
                        Node::List("ObjectInverseOf", r_args) => {
                            if let Some(r) = r_args.first().and_then(Node::as_atom) {
                                out.push((r, true, ind));
                            }
                        }
                        _ => {}
                    }
                }
            }
            "ObjectSomeValuesFrom" if plain.len() >= 2 => {
                if let Node::List("ObjectOneOf", inds) = plain[1] {
                    if inds.len() == 1 {
                        if let Some(ind) = inds[0].as_atom() {
                            match plain[0] {
                                Node::Atom(r) => out.push((r, false, ind)),
                                Node::List("ObjectInverseOf", r_args) => {
                                    if let Some(r) = r_args.first().and_then(Node::as_atom) {
                                        out.push((r, true, ind));
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    let _ = crate::frontend::parse::for_each_ontology_child(text, |node| {
        let Node::List(head, args) = node else {
            return Ok(());
        };
        let plain: Vec<&Node<'_>> = args
            .iter()
            .filter(|a| a.head() != Some("Annotation"))
            .collect();
        match *head {
            "SameIndividual" => {
                let inds: Vec<String> = plain
                    .iter()
                    .filter_map(|n| n.as_atom())
                    .filter_map(|t| {
                        ind_lookup
                            .get(&expand_tok(t))
                            .or_else(|| ind_lookup.get(&public_name(t)))
                            .cloned()
                    })
                    .collect();
                for w in inds.windows(2) {
                    same_pairs.push((w[0].clone(), w[1].clone()));
                }
            }
            "DifferentIndividuals" => {
                let inds: Vec<String> = plain
                    .iter()
                    .filter_map(|n| n.as_atom())
                    .filter_map(|t| {
                        ind_lookup
                            .get(&expand_tok(t))
                            .or_else(|| ind_lookup.get(&public_name(t)))
                            .cloned()
                    })
                    .collect();
                if inds.len() >= 2 {
                    diff_ind_groups.push(inds);
                }
            }
            "DisjointClasses" | "DisjointUnion" => {
                let slice = if *head == "DisjointUnion" && !plain.is_empty() {
                    &plain[1..]
                } else {
                    &plain[..]
                };
                let mut named_group: Vec<String> = Vec::new();
                let mut one_ofs: Vec<Vec<String>> = Vec::new();
                for item in slice {
                    if let Some(c) = item.as_atom() {
                        named_group.push(resolve_class_iri(c));
                    } else if let Node::List("ObjectOneOf", inds) = item {
                        let group: Vec<String> = inds
                            .iter()
                            .filter_map(|n| n.as_atom())
                            .filter_map(|t| {
                                ind_lookup
                                    .get(&expand_tok(t))
                                    .or_else(|| ind_lookup.get(&public_name(t)))
                                    .cloned()
                            })
                            .collect();
                        if !group.is_empty() {
                            one_ofs.push(group);
                        }
                    }
                }
                if named_group.len() >= 2 {
                    disjoint_class_groups.push(named_group.clone());
                }
                for c in &named_group {
                    for grp in &one_ofs {
                        for ind in grp {
                            class_disjoint_inds.push((c.clone(), ind.clone()));
                        }
                    }
                }
            }
            "SubClassOf" if plain.len() == 2 => {
                if let Some(lhs) = plain[0].as_atom() {
                    let lhs_iri = resolve_class_iri(lhs);
                    let mut hvs = Vec::new();
                    let mut selfs = Vec::new();
                    collect_has_value_rhs(plain[1], &mut hvs, &mut selfs);
                    for r_tok in selfs {
                        class_has_self.push((lhs_iri.clone(), resolve_role_short(r_tok)));
                    }
                    for (r_tok, inv, ind_tok) in hvs {
                        if let Some(pub_ind) = ind_lookup
                            .get(&expand_tok(ind_tok))
                            .or_else(|| ind_lookup.get(&public_name(ind_tok)))
                            .cloned()
                        {
                            class_has_value.push((
                                lhs_iri.clone(),
                                resolve_role_short(r_tok),
                                inv,
                                pub_ind,
                            ));
                        }
                    }
                    if let Node::List("ObjectComplementOf", inner) = plain[1] {
                        if let Some(rhs) = inner.first().and_then(Node::as_atom) {
                            disjoint_class_groups.push(vec![lhs_iri, resolve_class_iri(rhs)]);
                        } else if let Some(Node::List("ObjectOneOf", inds)) = inner.first() {
                            for n in inds {
                                if let Some(t) = n.as_atom() {
                                    if let Some(pub_ind) = ind_lookup
                                        .get(&expand_tok(t))
                                        .or_else(|| ind_lookup.get(&public_name(t)))
                                        .cloned()
                                    {
                                        class_disjoint_inds.push((lhs_iri.clone(), pub_ind));
                                    }
                                }
                            }
                        }
                    } else if let Node::List("DataMaxCardinality" | "DataExactCardinality", c_args) =
                        plain[1]
                    {
                        if c_args.len() >= 2 && c_args[0].as_atom() == Some("1") {
                            if let Some(p) = c_args[1].as_atom() {
                                if matches!(
                                    lhs,
                                    "owl:Thing" | "<http://www.w3.org/2002/07/owl#Thing>"
                                ) {
                                    func_data_props.insert(expand_tok(p));
                                }
                            }
                        }
                    } else if let Node::List(
                        "ObjectMaxCardinality" | "ObjectExactCardinality",
                        c_args,
                    ) = plain[1]
                    {
                        if c_args.len() >= 2 && c_args[0].as_atom() == Some("1") {
                            if c_args.len() == 2
                                || c_args.get(2).and_then(Node::as_atom).is_some_and(|f| {
                                    matches!(
                                        f,
                                        "owl:Thing" | "<http://www.w3.org/2002/07/owl#Thing>"
                                    )
                                })
                            {
                                if matches!(
                                    lhs,
                                    "owl:Thing" | "<http://www.w3.org/2002/07/owl#Thing>"
                                ) {
                                    if let Some(r) = c_args[1].as_atom() {
                                        func_obj_roles.insert(resolve_role_short(r));
                                    }
                                }
                            }
                        }
                    }
                } else if let (Node::List("ObjectIntersectionOf", inter), Some(rhs)) =
                    (plain[0], plain[1].as_atom())
                {
                    if matches!(rhs, "owl:Nothing" | "<http://www.w3.org/2002/07/owl#Nothing>")
                        && inter.len() == 2
                    {
                        if let (Some(c1), Some(c2)) = (inter[0].as_atom(), inter[1].as_atom()) {
                            disjoint_class_groups
                                .push(vec![resolve_class_iri(c1), resolve_class_iri(c2)]);
                        }
                    }
                }
            }
            "EquivalentClasses" if plain.len() >= 2 => {
                for i in 0..plain.len() {
                    for j in 0..plain.len() {
                        if i == j {
                            continue;
                        }
                        if let Some(lhs) = plain[i].as_atom() {
                            let lhs_iri = resolve_class_iri(lhs);
                            let mut hvs = Vec::new();
                            let mut selfs = Vec::new();
                            collect_has_value_rhs(plain[j], &mut hvs, &mut selfs);
                            for r_tok in selfs {
                                class_has_self.push((lhs_iri.clone(), resolve_role_short(r_tok)));
                            }
                            for (r_tok, inv, ind_tok) in hvs {
                                if let Some(pub_ind) = ind_lookup
                                    .get(&expand_tok(ind_tok))
                                    .or_else(|| ind_lookup.get(&public_name(ind_tok)))
                                    .cloned()
                                {
                                    class_has_value.push((
                                        lhs_iri.clone(),
                                        resolve_role_short(r_tok),
                                        inv,
                                        pub_ind,
                                    ));
                                }
                            }
                            if let Node::List("ObjectComplementOf", inner) = plain[j] {
                                if let Some(rhs) = inner.first().and_then(Node::as_atom) {
                                    disjoint_class_groups
                                        .push(vec![lhs_iri, resolve_class_iri(rhs)]);
                                }
                            }
                        }
                    }
                }
            }
            "ClassAssertion" if plain.len() == 2 => {
                if let Some(ind_tok) = plain[1].as_atom() {
                    if let Some(&u) = ind_lookup
                        .get(&expand_tok(ind_tok))
                        .or_else(|| ind_lookup.get(&public_name(ind_tok)))
                        .and_then(|pub_i| ind_to_elem.get(pub_i))
                    {
                        if let Some(c_tok) = plain[0].as_atom() {
                            let c_iri = resolve_class_iri(c_tok);
                            elem_classes[u].insert(c_iri.clone());
                            entailed_elem_classes[u].insert(c_iri);
                        } else if let Node::List("ObjectComplementOf", inner) = plain[0] {
                            if let Some(c) = inner.first().and_then(Node::as_atom) {
                                elem_neg_classes[u].insert(resolve_class_iri(c));
                            }
                        }
                    }
                }
            }
            "ObjectPropertyAssertion" if plain.len() == 3 => {
                if let (Some(a_tok), Some(b_tok)) = (plain[1].as_atom(), plain[2].as_atom()) {
                    let ua = ind_lookup
                        .get(&expand_tok(a_tok))
                        .or_else(|| ind_lookup.get(&public_name(a_tok)))
                        .and_then(|p| ind_to_elem.get(p))
                        .copied();
                    let ub = ind_lookup
                        .get(&expand_tok(b_tok))
                        .or_else(|| ind_lookup.get(&public_name(b_tok)))
                        .and_then(|p| ind_to_elem.get(p))
                        .copied();
                    if let (Some(ua), Some(ub)) = (ua, ub) {
                        match plain[0] {
                            Node::Atom(r) => {
                                let rs = resolve_role_short(r);
                                edge_set.insert((ua, rs.clone(), ub));
                                source_role_assertions.push((ua, rs, ub));
                            }
                            Node::List("ObjectInverseOf", r_args) => {
                                if let Some(r) = r_args.first().and_then(Node::as_atom) {
                                    let rs = resolve_role_short(r);
                                    edge_set.insert((ub, rs.clone(), ua));
                                    source_role_assertions.push((ub, rs, ua));
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            "NegativeObjectPropertyAssertion" if plain.len() == 3 => {
                if let (Some(a_tok), Some(b_tok)) = (plain[1].as_atom(), plain[2].as_atom()) {
                    let ua = ind_lookup
                        .get(&expand_tok(a_tok))
                        .or_else(|| ind_lookup.get(&public_name(a_tok)))
                        .and_then(|p| ind_to_elem.get(p))
                        .copied();
                    let ub = ind_lookup
                        .get(&expand_tok(b_tok))
                        .or_else(|| ind_lookup.get(&public_name(b_tok)))
                        .and_then(|p| ind_to_elem.get(p))
                        .copied();
                    if let (Some(ua), Some(ub)) = (ua, ub) {
                        match plain[0] {
                            Node::Atom(r) => {
                                neg_role_assertions.push((resolve_role_short(r), ua, ub));
                            }
                            Node::List("ObjectInverseOf", r_args) => {
                                if let Some(r) = r_args.first().and_then(Node::as_atom) {
                                    neg_role_assertions.push((resolve_role_short(r), ub, ua));
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            "IrreflexiveObjectProperty" if !plain.is_empty() => {
                if let Some(r) = plain[0].as_atom() {
                    irrefl_roles.insert(resolve_role_short(r));
                }
            }
            "AsymmetricObjectProperty" if !plain.is_empty() => {
                if let Some(r) = plain[0].as_atom() {
                    asym_roles.insert(resolve_role_short(r));
                }
            }
            "DisjointObjectProperties" if plain.len() >= 2 => {
                let grp: Vec<String> = plain
                    .iter()
                    .filter_map(|n| n.as_atom())
                    .map(&resolve_role_short)
                    .collect();
                if grp.len() >= 2 {
                    disjoint_role_groups.push(grp);
                }
            }
            "FunctionalObjectProperty" if !plain.is_empty() => {
                match plain[0] {
                    Node::Atom(r) => {
                        func_obj_roles.insert(resolve_role_short(r));
                    }
                    Node::List("ObjectInverseOf", r_args) => {
                        if let Some(r) = r_args.first().and_then(Node::as_atom) {
                            inv_func_obj_roles.insert(resolve_role_short(r));
                        }
                    }
                    _ => {}
                }
            }
            "InverseFunctionalObjectProperty" if !plain.is_empty() => {
                match plain[0] {
                    Node::Atom(r) => {
                        inv_func_obj_roles.insert(resolve_role_short(r));
                    }
                    Node::List("ObjectInverseOf", r_args) => {
                        if let Some(r) = r_args.first().and_then(Node::as_atom) {
                            func_obj_roles.insert(resolve_role_short(r));
                        }
                    }
                    _ => {}
                }
            }
            "FunctionalDataProperty" if !plain.is_empty() => {
                if let Some(p) = plain[0].as_atom() {
                    func_data_props.insert(expand_tok(p));
                }
            }
            "SubDataPropertyOf" if plain.len() == 2 => {
                if let (Some(sub), Some(sup)) = (plain[0].as_atom(), plain[1].as_atom()) {
                    sub_data_props
                        .entry(expand_tok(sub))
                        .or_default()
                        .push(expand_tok(sup));
                }
            }
            "EquivalentDataProperties" if plain.len() >= 2 => {
                let props: Vec<String> = plain
                    .iter()
                    .filter_map(|n| n.as_atom())
                    .map(&expand_tok)
                    .collect();
                for i in 0..props.len() {
                    for j in 0..props.len() {
                        if i != j {
                            sub_data_props
                                .entry(props[i].clone())
                                .or_default()
                                .push(props[j].clone());
                        }
                    }
                }
            }
            "DataPropertyDomain" if plain.len() == 2 => {
                if let (Some(p), Some(c)) = (plain[0].as_atom(), plain[1].as_atom()) {
                    data_domains.push((expand_tok(p), resolve_class_iri(c)));
                }
            }
            "ObjectPropertyDomain" if plain.len() == 2 => {
                if let (Some(r), Some(c)) = (plain[0].as_atom(), plain[1].as_atom()) {
                    obj_domains.push((resolve_role_short(r), resolve_class_iri(c)));
                }
            }
            "ObjectPropertyRange" if plain.len() == 2 => {
                if let (Some(r), Some(c)) = (plain[0].as_atom(), plain[1].as_atom()) {
                    obj_ranges.push((resolve_role_short(r), resolve_class_iri(c)));
                }
            }
            "DataPropertyAssertion" if plain.len() >= 3 => {
                if let (Some(p_tok), Some(ind_tok)) = (plain[0].as_atom(), plain[1].as_atom()) {
                    if let Some(&u) = ind_lookup
                        .get(&expand_tok(ind_tok))
                        .or_else(|| ind_lookup.get(&public_name(ind_tok)))
                        .and_then(|p| ind_to_elem.get(p))
                    {
                        let lit_parts: Option<Vec<&str>> =
                            plain[2..].iter().map(|n| n.as_atom()).collect();
                        if let Some(parts) = lit_parts {
                            let raw_lit = parts.concat();
                            let lit = if let Some((lex, dt_tok)) = raw_lit.rsplit_once("^^") {
                                if !dt_tok.starts_with('<') {
                                    let exp_dt = expand_tok(dt_tok);
                                    if exp_dt.contains("://") {
                                        format!("{lex}^^<{exp_dt}>")
                                    } else {
                                        raw_lit
                                    }
                                } else {
                                    raw_lit
                                }
                            } else {
                                raw_lit
                            };
                            source_data_assertions.push((u, expand_tok(p_tok), lit));
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    });

    close_elem_classes(&mut entailed_elem_classes);

    let mut proved_edge_set: HashSet<(usize, String, usize)> = source_role_assertions
        .iter()
        .cloned()
        .collect();
    for u in 0..n_elems {
        for r in &refl_roles {
            proved_edge_set.insert((u, r.clone(), u));
        }
    }
    for (owner_iri, prop_iri, lit) in &raw.extra_values {
        if let Some(&u) = ind_lookup
            .get(owner_iri)
            .and_then(|pub_i| ind_to_elem.get(pub_i))
        {
            source_data_assertions.push((u, expand_tok(prop_iri), lit.clone()));
        }
    }
    let mut closed_data_assertions: Vec<(usize, String, String)> = Vec::new();
    let mut init_data_dom_added = false;
    let mut init_entailed_data_dom_added = false;
    for (u, p, lit) in source_data_assertions {
        let mut stack = vec![p];
        let mut seen = HashSet::new();
        while let Some(cur) = stack.pop() {
            if seen.insert(cur.clone()) {
                for (dp, dc) in &data_domains {
                    if &cur == dp {
                        if elem_classes[u].insert(dc.clone()) {
                            init_data_dom_added = true;
                        }
                        if entailed_elem_classes[u].insert(dc.clone()) {
                            init_entailed_data_dom_added = true;
                        }
                    }
                }
                closed_data_assertions.push((u, cur.clone(), lit.clone()));
                if let Some(sups) = sub_data_props.get(&cur) {
                    stack.extend(sups.iter().cloned());
                }
            }
        }
    }
    if init_data_dom_added {
        close_elem_classes(&mut elem_classes);
    }
    if init_entailed_data_dom_added {
        close_elem_classes(&mut entailed_elem_classes);
    }

    for round in 0..8 {
        let mut round_edge_added = false;
        for u in 0..n_elems {
            for (c_iri, r_short) in &class_has_self {
                if entailed_elem_classes[u].contains(c_iri)
                    && proved_edge_set.insert((u, r_short.clone(), u))
                {
                    round_edge_added = true;
                }
                if elem_classes[u].contains(c_iri) && edge_set.insert((u, r_short.clone(), u)) {
                    round_edge_added = true;
                }
            }
            for (c_iri, r_short, inv, target_ind) in &class_has_value {
                if let Some(&v) = ind_to_elem.get(target_ind) {
                    let edge = if *inv {
                        (v, r_short.clone(), u)
                    } else {
                        (u, r_short.clone(), v)
                    };
                    if entailed_elem_classes[u].contains(c_iri)
                        && proved_edge_set.insert(edge.clone())
                    {
                        round_edge_added = true;
                    }
                    if elem_classes[u].contains(c_iri) && edge_set.insert(edge) {
                        round_edge_added = true;
                    }
                }
            }
        }
        if round == 0 || round_edge_added {
            crate::engine::close_edges_under_rbox_rows(&meta.rbox, n_elems, &mut proved_edge_set)
                .ok()?;
            crate::engine::close_edges_under_rbox_rows(&meta.rbox, n_elems, &mut edge_set).ok()?;
        }

        let mut dom_ran_added = false;
        let mut entailed_dom_ran_added = false;
        if !obj_domains.is_empty() || !obj_ranges.is_empty() {
            for (u, r, v) in &proved_edge_set {
                for (dr, dc) in &obj_domains {
                    if r == dr && entailed_elem_classes[*u].insert(dc.clone()) {
                        entailed_dom_ran_added = true;
                    }
                }
                for (rr, rc) in &obj_ranges {
                    if r == rr && entailed_elem_classes[*v].insert(rc.clone()) {
                        entailed_dom_ran_added = true;
                    }
                }
            }
            for (u, r, v) in &edge_set {
                for (dr, dc) in &obj_domains {
                    if r == dr && elem_classes[*u].insert(dc.clone()) {
                        dom_ran_added = true;
                    }
                }
                for (rr, rc) in &obj_ranges {
                    if r == rr && elem_classes[*v].insert(rc.clone()) {
                        dom_ran_added = true;
                    }
                }
            }
        }
        if dom_ran_added {
            close_elem_classes(&mut elem_classes);
        }
        if entailed_dom_ran_added {
            close_elem_classes(&mut entailed_elem_classes);
        }
        if !dom_ran_added && !entailed_dom_ran_added {
            break;
        }
    }

    // A reconstructed structure (elided ABox, or the EL canonical model whose
    // named part is rebuilt from the source) holds only the named individuals
    // and, later, a bounded number of Skolem witnesses. It is not a model, so
    // its named edges do not bound the entailed ones: composite roles (chains,
    // transitivity) also hold between named individuals through anonymous
    // elements, on a path that leaves `a` into its anonymous tree and returns
    // (`c1(a, a)` from `s1(a, x)`, `s3(x, a)` with `s1 ∘ s3 ⊑ c1`), possibly
    // composed with ABox edges. `ExcursionBound` adds those candidates to the
    // upper bound; the residual probes decide them.
    // Individuals that occur in no logical axiom (only in declarations or
    // annotations) are absent from the exported model, whose stand-in
    // elements carry no classes; their rows (for example `s(x, x)` from
    // `⊤ ⊑ ∃s.Self`, or an excursion loop) were lost. Such an individual is
    // interchangeable with a fresh one: without nominals or the universal
    // role it can only be related to itself, so its loops on every role go to
    // the residual probes; with them, the exact probe run decides everything.
    let fresh_inds: Vec<usize> = if values_requested && !bound_disabled {
        let mut mentioned: HashSet<String> = HashSet::new();
        fn atoms<'a>(node: &Node<'a>, out: &mut Vec<&'a str>) {
            match node {
                Node::Atom(a) => out.push(a),
                Node::List(_, args) => {
                    for a in args {
                        atoms(a, out);
                    }
                }
            }
        }
        let _ = crate::frontend::parse::for_each_ontology_child(text, |node| {
            if matches!(node.head(), Some("Declaration" | "AnnotationAssertion")) {
                return Ok(());
            }
            let mut out = Vec::new();
            atoms(node, &mut out);
            for t in out {
                if let Some(p) = ind_lookup.get(&expand_tok(t)).or_else(|| ind_lookup.get(&public_name(t))) {
                    mentioned.insert(p.clone());
                }
            }
            Ok(())
        });
        // A mentioned individual missing from the model has no reliable
        // edges at all: let the exact probes answer.
        if stand_ins.iter().any(|p| mentioned.contains(p)) {
            return None;
        }
        pub_individuals
            .iter()
            .enumerate()
            .filter(|(_, p)| !mentioned.contains(*p))
            .map(|(i, _)| i)
            .collect()
    } else {
        Vec::new()
    };
    // The TBox facts a fresh individual can have: loops on `HasSelf`,
    // reflexive and excursion roles, and with nominals edges to and from any
    // individual. `None` (anonymous individuals in assertions, the universal
    // role, a fenced chain) falls back to the exact probe run.
    let fresh_spec = if fresh_inds.is_empty() {
        None
    } else {
        Some(ExcursionSpec::collect(text, &meta.rbox, &|tok: &str| resolve_role_short(tok))?)
    };
    let reconstructed = raw.abox_elided || raw.route == "el-canonical";
    let excursion_spec = if reconstructed && values_requested && !bound_disabled {
        Some(ExcursionSpec::collect(text, &meta.rbox, &|tok: &str| resolve_role_short(tok))?)
    } else {
        None
    };
    let excursion_ok = match &excursion_spec {
        Some(spec) => ExcursionBound::compute(spec, &meta.rbox, n_elems, &edge_set).all_proved(&proved_edge_set),
        None => true,
    };

    // Fast path for `--values` without `--different`: when the ontology has no
    // `ObjectHasValue`, `ObjectOneOf`, or `ObjectHasSelf` constructs that could
    // derive new role edges between named individuals during clause saturation,
    // and every named-individual edge in `edge_set` and every anonymous-excursion
    // candidate is already in `proved_edge_set`, `proved_edge_set` and
    // `edge_set` are already final on `0..n_elems`.
    let has_elided_func_hazard = raw.abox_elided && {
        if text.contains("ObjectMaxCardinality(")
            || text.contains("ObjectExactCardinality(")
            || text.contains("ObjectMinCardinality(")
        {
            true
        } else if func_obj_roles.is_empty() && inv_func_obj_roles.is_empty() {
            false
        } else if n_elems <= 256 {
            true
        } else {
            let mut seen_src: HashMap<(usize, &str), usize> = HashMap::new();
            let mut seen_dst: HashMap<(&str, usize), usize> = HashMap::new();
            let mut collision = false;
            for (u, r, v) in &edge_set {
                if *u >= n_elems || *v >= n_elems {
                    continue;
                }
                if func_obj_roles.contains(r.as_str()) {
                    if let Some(&prev_v) = seen_src.get(&(*u, r.as_str())) {
                        if prev_v != *v {
                            collision = true;
                            break;
                        }
                    } else {
                        seen_src.insert((*u, r.as_str()), *v);
                    }
                }
                if inv_func_obj_roles.contains(r.as_str()) {
                    if let Some(&prev_u) = seen_dst.get(&(r.as_str(), *v)) {
                        if prev_u != *u {
                            collision = true;
                            break;
                        }
                    } else {
                        seen_dst.insert((r.as_str(), *v), *u);
                    }
                }
            }
            collision
        }
    };
    if !different_requested
        && !has_elided_func_hazard
        && !text.contains("ObjectHasValue(")
        && !text.contains("ObjectOneOf(")
        && !text.contains("ObjectHasSelf(")
        && edge_set
            .iter()
            .all(|e| e.0 >= n_elems || e.2 >= n_elems || proved_edge_set.contains(e))
        && excursion_ok
        && fresh_inds.is_empty()
    {
        let mut same_adj: HashMap<&str, Vec<&str>> = HashMap::new();
        for (a, b) in &same_pairs {
            same_adj.entry(a.as_str()).or_default().push(b.as_str());
            same_adj.entry(b.as_str()).or_default().push(a.as_str());
        }
        let mut same_comp: HashMap<&str, usize> = HashMap::new();
        let mut cid = 0usize;
        for ind in &pub_individuals {
            if same_comp.contains_key(ind.as_str()) {
                continue;
            }
            cid += 1;
            let mut stack = vec![ind.as_str()];
            while let Some(cur) = stack.pop() {
                if same_comp.insert(cur, cid).is_none() {
                    if let Some(nbrs) = same_adj.get(cur) {
                        stack.extend(nbrs.iter().copied());
                    }
                }
            }
        }
        let mut plan = ModelAboxPlan::default();
        if values_requested {
            for (u, r, v) in &proved_edge_set {
                if *u >= n_elems || *v >= n_elems {
                    continue;
                }
                let full_r = meta.iri_map.get(r).map(String::as_str).unwrap_or(r.as_str());
                let Some(pub_r) = role_lookup.get(full_r).or_else(|| role_lookup.get(r)) else {
                    continue;
                };
                if u != v {
                    for a in &elem_inds[*u] {
                        for b in &elem_inds[*v] {
                            plan.proved_values
                                .insert([pub_r.clone(), a.clone(), b.clone()]);
                        }
                    }
                } else {
                    for a in &elem_inds[*u] {
                        for b in &elem_inds[*u] {
                            if a == b || same_comp.get(a.as_str()) == same_comp.get(b.as_str()) {
                                plan.proved_values
                                    .insert([pub_r.clone(), a.clone(), b.clone()]);
                            }
                        }
                    }
                }
            }
        }
        return Some(plan);
    }

    // Parse normalized DL-clauses of `text` to run Horn saturation on merged
    // individual pairs `M_0 / (u = v)`.
    let f_res = {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_NO_SEPARABLE_ABOX_ELISION", "1");
        std::env::set_var("KM_NO_FAST_SEPARABLE_ABOX_PARSE", "1");
        std::env::set_var("KM_NOMINALS", "1");
        std::env::set_var("KM_CARDS", "1");
        std::env::set_var("KM_DATATYPES", "1");
        std::env::set_var("KM_ROUTE", "auto");
        crate::frontend::ofn_to_clauses_for_classifier(text).ok()?
    };
    if f_res.abox_inconsistent || !f_res.rules.is_empty() {
        return None;
    }

    let canon_concept = |c: &str| -> String {
        if matches!(
            c,
            "owl:Thing" | "Thing" | "⊤" | "http://www.w3.org/2002/07/owl#Thing"
        ) {
            return "owl:Thing".to_string();
        }
        if matches!(
            c,
            "owl:Nothing" | "Nothing" | "⊥" | "http://www.w3.org/2002/07/owl#Nothing"
        ) {
            return "owl:Nothing".to_string();
        }
        if let Some(rest) = c.strip_prefix("__nom__") {
            let full = f_res
                .iri_map
                .get(rest)
                .or_else(|| meta.iri_map.get(rest))
                .map(String::as_str)
                .unwrap_or(rest);
            let pub_i = ind_lookup
                .get(full)
                .or_else(|| ind_lookup.get(rest))
                .map(String::as_str)
                .unwrap_or(full);
            return format!("__nom__{pub_i}");
        }
        f_res
            .iri_map
            .get(c)
            .or_else(|| meta.iri_map.get(c))
            .cloned()
            .unwrap_or_else(|| c.to_string())
    };
    let canon_role = |r: &str| -> (String, bool) {
        if let Some(base) = r.strip_prefix("__inv__") {
            let full = f_res
                .iri_map
                .get(base)
                .or_else(|| meta.iri_map.get(base))
                .map(String::as_str)
                .unwrap_or(base);
            (resolve_role_short(full), true)
        } else {
            let full = f_res
                .iri_map
                .get(r)
                .or_else(|| meta.iri_map.get(r))
                .map(String::as_str)
                .unwrap_or(r);
            (resolve_role_short(full), false)
        }
    };
    let resolve_ind_elem = |ind_name: &str| -> Option<usize> {
        let full = f_res
            .iri_map
            .get(ind_name)
            .or_else(|| meta.iri_map.get(ind_name))
            .map(String::as_str)
            .unwrap_or(ind_name);
        let pub_i = ind_lookup.get(full).or_else(|| ind_lookup.get(ind_name))?;
        ind_to_elem.get(pub_i).copied()
    };

    #[derive(Clone, Debug)]
    struct ConceptClauseRule {
        body: Vec<String>,
        heads: Vec<String>,
        nom_merge: Option<usize>,
    }
    #[derive(Clone, Debug)]
    enum RoleHeadAction {
        Clash,
        AddX(String),
        AddY(String),
        AddRole(String, bool),
        MergeXY,
        MergeXElem(usize),
        MergeYElem(usize),
        Disj(Vec<(bool, String)>),
    }
    #[derive(Clone, Debug)]
    struct RoleClauseRule {
        role: String,
        self_only: bool,
        body_x: Vec<String>,
        body_y: Vec<String>,
        action: RoleHeadAction,
    }
    #[derive(Clone, Debug)]
    struct HasValueClauseRule {
        body: Vec<String>,
        role: String,
        inv: bool,
        target_elem: usize,
    }
    #[derive(Clone, Debug)]
    struct ExistentialGroup {
        body: Vec<String>,
        role: Option<(String, bool)>,
        fillers: Vec<String>,
    }
    #[derive(Clone, Debug)]
    struct QualFuncRule {
        role: String,
        inv: bool,
        max_n: usize,
        body_x: Vec<String>,
        body_y: Vec<String>,
    }

    let mut concept_rules: Vec<ConceptClauseRule> = Vec::new();
    let mut role_rules: Vec<RoleClauseRule> = Vec::new();
    let mut has_value_rules: Vec<HasValueClauseRule> = Vec::new();
    let mut skolem_groups: HashMap<(String, String), ExistentialGroup> = HashMap::new();
    let mut qual_func_rules: Vec<QualFuncRule> = Vec::new();
    let mut singleton_concepts: HashSet<String> = HashSet::new();
    let mut skolem_ineqs: Vec<(Vec<String>, String, String)> = Vec::new();
    let mut has_unhandled_clause = false;

    // A model element is a data value when the model labels it with the data
    // sort or a data property edge ends in it; every other element is an
    // object. Object-only rules (bodies guarded by the object sort) must not
    // reach data values.
    let data_role_set: HashSet<String> = f_res
        .data_roles
        .iter()
        .map(|r| canon_role(r).0)
        .collect();
    let mut data_value_elem = vec![false; n_elems];
    for (u, lbl) in labels.iter().enumerate() {
        if lbl.iter().any(|l| l == crate::frontend::sorts::DATA_SORT) {
            data_value_elem[u] = true;
        }
    }
    for (_, r, t) in edge_set.iter().chain(proved_edge_set.iter()) {
        if *t < n_elems && data_role_set.contains(r) {
            data_value_elem[*t] = true;
        }
    }
    for u in 0..n_elems {
        let sort = if data_value_elem[u] {
            crate::frontend::sorts::DATA_SORT
        } else {
            crate::frontend::sorts::OBJECT_SORT
        };
        elem_classes[u].insert("owl:Thing".to_string());
        elem_classes[u].insert(sort.to_string());
        entailed_elem_classes[u].insert("owl:Thing".to_string());
        entailed_elem_classes[u].insert(sort.to_string());
        for ind in &elem_inds[u] {
            let nom_c = format!("__nom__{ind}");
            elem_classes[u].insert(nom_c.clone());
            entailed_elem_classes[u].insert(nom_c);
        }
    }
    for entry in &f_res.nominal_abox.individuals {
        if let Some(u) = resolve_ind_elem(&entry.individual) {
            for marker in &entry.assertion_markers {
                let cc = canon_concept(marker);
                elem_classes[u].insert(cc.clone());
                entailed_elem_classes[u].insert(cc);
            }
        }
    }
    for ra in &f_res.nominal_abox.role_assertions {
        if let (Some(us), Some(ut)) = (resolve_ind_elem(&ra.source), resolve_ind_elem(&ra.target)) {
            let (rs, inv) = canon_role(&ra.role);
            let edge = if inv { (ut, rs, us) } else { (us, rs, ut) };
            edge_set.insert(edge.clone());
            proved_edge_set.insert(edge);
        }
    }
    for ra in &f_res.nominal_abox.negative_role_assertions {
        if let (Some(us), Some(ut)) = (resolve_ind_elem(&ra.source), resolve_ind_elem(&ra.target)) {
            let (rs, inv) = canon_role(&ra.role);
            if inv {
                neg_role_assertions.push((rs, ut, us));
            } else {
                neg_role_assertions.push((rs, us, ut));
            }
        }
    }
    for (a, b) in &f_res.nominal_abox.different {
        if let (Some(pa), Some(pb)) = (
             resolve_ind_elem(a).and_then(|u| elem_inds[u].first().cloned()),
            resolve_ind_elem(b).and_then(|u| elem_inds[u].first().cloned()),
        ) {
            diff_ind_groups.push(vec![pa, pb]);
        }
    }


    use crate::json_io::{JAtom, JTerm};
    for cl in &f_res.clauses {
        if cl.head.len() == 1
            && matches!(
                cl.head[0],
                JAtom::Concept { ref concept, .. }
                    if concept == crate::frontend::sorts::OBJECT_SORT
                        || concept == crate::frontend::sorts::DATA_SORT
            )
        {
            continue;
        }
        let mut body: Vec<&JAtom> = cl
            .body
            .iter()
            .filter(|a| !matches!(a, JAtom::Concept { concept, .. } if concept == crate::frontend::sorts::OBJECT_SORT))
            .collect();
        let body_has_data_sort = body.iter().any(|a| {
            matches!(a, JAtom::Concept { concept, .. } if concept == crate::frontend::sorts::DATA_SORT)
        });
        let head: Vec<&JAtom> = cl
            .head
            .iter()
            .filter(|a| {
                body_has_data_sort
                    || !matches!(a, JAtom::Concept { concept, .. } if concept == crate::frontend::sorts::DATA_SORT)
            })
            .collect();
        // Every element carries exactly one sort, so the head disjunct `D(t)`
        // is the body guard `O(t)`: `→ C(x) ∨ D(x)` (the sorted `⊤ ⊑ C`) holds
        // on objects only. Dropping the disjunct without the guard put `C` on
        // data values. A body guard `O(t)` stays when it is the only atom.
        let object_guards: Vec<JAtom> = if body_has_data_sort {
            Vec::new()
        } else {
            cl.head
                .iter()
                .filter_map(|a| match a {
                    JAtom::Concept { concept, term } if concept == crate::frontend::sorts::DATA_SORT => {
                        Some(JAtom::Concept {
                            concept: crate::frontend::sorts::OBJECT_SORT.to_string(),
                            term: term.clone(),
                        })
                    }
                    _ => None,
                })
                .collect()
        };
        if body.is_empty() && object_guards.is_empty() {
            body = cl.body.iter().collect();
        }
        body.extend(object_guards.iter());

        // Ground ABox clauses
        let all_ground = body.iter().chain(head.iter()).all(|a| match a {
            JAtom::Concept { term, .. } => matches!(term, JTerm::Ind { .. }),
            JAtom::Role { source, target, .. } => {
                matches!(source, JTerm::Ind { .. }) && matches!(target, JTerm::Ind { .. })
            }
            JAtom::Eq { left, right } => {
                matches!(left, JTerm::Ind { .. }) && matches!(right, JTerm::Ind { .. })
            }
        });
        if all_ground && (!body.is_empty() || !head.is_empty()) {
            match (body.as_slice(), head.as_slice()) {
                ([], [JAtom::Concept { concept, term: JTerm::Ind { name } }]) => {
                    if let Some(u) = resolve_ind_elem(name) {
                        let cc = canon_concept(concept);
                        elem_classes[u].insert(cc.clone());
                        entailed_elem_classes[u].insert(cc);
                    }
                    continue;
                }
                ([JAtom::Concept { concept, term: JTerm::Ind { name } }], []) => {
                    if let Some(u) = resolve_ind_elem(name) {
                        elem_neg_classes[u].insert(canon_concept(concept));
                    }
                    continue;
                }
                (
                    [],
                    [JAtom::Role {
                        role,
                        source: JTerm::Ind { name: s },
                        target: JTerm::Ind { name: t },
                    }],
                ) => {
                    if let (Some(us), Some(ut)) = (resolve_ind_elem(s), resolve_ind_elem(t)) {
                        let (rs, inv) = canon_role(role);
                        let edge = if inv { (ut, rs, us) } else { (us, rs, ut) };
                        edge_set.insert(edge.clone());
                        proved_edge_set.insert(edge);
                    }
                    continue;
                }
                (
                    [JAtom::Role {
                        role,
                        source: JTerm::Ind { name: s },
                        target: JTerm::Ind { name: t },
                    }],
                    [],
                ) => {
                    if let (Some(us), Some(ut)) = (resolve_ind_elem(s), resolve_ind_elem(t)) {
                        let (rs, inv) = canon_role(role);
                        if inv {
                            neg_role_assertions.push((rs, ut, us));
                        } else {
                            neg_role_assertions.push((rs, us, ut));
                        }
                    }
                    continue;
                }
                (
                    [JAtom::Eq {
                        left: JTerm::Ind { name: l },
                        right: JTerm::Ind { name: r },
                    }],
                    [],
                ) => {
                    if let (Some(pa), Some(pb)) = (
                        resolve_ind_elem(l).and_then(|u| elem_inds[u].first().cloned()),
                        resolve_ind_elem(r).and_then(|u| elem_inds[u].first().cloned()),
                    ) {
                        diff_ind_groups.push(vec![pa, pb]);
                    }
                    continue;
                }
                _ => continue,
            }
        }

        // Skolem existential clauses: `[B_1(x), ...] -> [r(x, f(x))]` or `[C(f(x))]`
        if head.len() == 1
            && body.iter().all(|a| matches!(a, JAtom::Concept { term: JTerm::Var { .. }, .. }))
        {
            let mut fun_key: Option<(String, String, Option<(String, bool)>, Option<String>)> = None;
            match head[0] {
                JAtom::Role {
                    role,
                    source: JTerm::Var { name: vx },
                    target: JTerm::Fun { function, arg },
                } => {
                    if let JTerm::Var { name: av } = arg.as_ref() {
                        if av == vx {
                            let (rs, inv) = canon_role(role);
                            fun_key = Some((function.clone(), vx.clone(), Some((rs, inv)), None));
                        }
                    }
                }
                JAtom::Role {
                    role,
                    source: JTerm::Fun { function, arg },
                    target: JTerm::Var { name: vx },
                } => {
                    if let JTerm::Var { name: av } = arg.as_ref() {
                        if av == vx {
                            let (rs, inv) = canon_role(role);
                            fun_key = Some((function.clone(), vx.clone(), Some((rs, !inv)), None));
                        }
                    }
                }
                JAtom::Concept {
                    concept,
                    term: JTerm::Fun { function, arg },
                } => {
                    if let JTerm::Var { name: av } = arg.as_ref() {
                        fun_key = Some((
                            function.clone(),
                            av.clone(),
                            None,
                            Some(canon_concept(concept)),
                        ));
                    }
                }
                _ => {}
            }
            if let Some((fn_name, vx, role_opt, filler_opt)) = fun_key {
                if body.iter().all(|a| matches!(a, JAtom::Concept { term: JTerm::Var { name }, .. } if name == &vx)) {
                    let b_concepts: Vec<String> = body
                        .iter()
                        .filter_map(|a| match a {
                            JAtom::Concept { concept, .. } => Some(canon_concept(concept)),
                            _ => None,
                        })
                        .collect();
                    let entry = skolem_groups
                        .entry((fn_name, vx))
                        .or_insert_with(|| ExistentialGroup {
                            body: b_concepts.clone(),
                            role: None,
                            fillers: Vec::new(),
                        });
                    for bc in b_concepts {
                        if !entry.body.contains(&bc) {
                            entry.body.push(bc);
                        }
                    }
                    if let Some(ro) = role_opt {
                        entry.role = Some(ro);
                    }
                    if let Some(fl) = filler_opt {
                        if !entry.fillers.contains(&fl) {
                            entry.fillers.push(fl);
                        }
                    }
                    continue;
                }
            }
        }

        // Skolem distinctness for min-cardinality: `[Concept(M, x), ..., Eq(f1(x), f2(x))] -> []`
        if head.is_empty() && body.iter().any(|a| matches!(a, JAtom::Eq { .. })) {
            let mut eqs = Vec::new();
            let mut b_concepts = Vec::new();
            let mut var_x: Option<&str> = None;
            let mut ok = true;
            for a in &body {
                match a {
                    JAtom::Eq {
                        left: JTerm::Fun { function: f1, arg: a1 },
                        right: JTerm::Fun { function: f2, arg: a2 },
                    } => {
                        if let (JTerm::Var { name: v1 }, JTerm::Var { name: v2 }) =
                            (a1.as_ref(), a2.as_ref())
                        {
                            if v1 == v2 && (var_x.is_none() || var_x == Some(v1.as_str())) {
                                var_x = Some(v1.as_str());
                                eqs.push((f1.clone(), f2.clone()));
                            } else {
                                ok = false;
                            }
                        } else {
                            ok = false;
                        }
                    }
                    JAtom::Concept {
                        concept,
                        term: JTerm::Var { name },
                    } => {
                        if var_x.is_none() || var_x == Some(name.as_str()) {
                            var_x = Some(name.as_str());
                            b_concepts.push(canon_concept(concept));
                        } else {
                            ok = false;
                        }
                    }
                    _ => ok = false,
                }
            }
            if ok && eqs.len() == 1 {
                let (f1, f2) = eqs.pop().unwrap();
                skolem_ineqs.push((b_concepts, f1, f2));
                continue;
            }
        }

        // Singleton uniqueness: `[Concept(N, y0), Concept(N, y1)] -> [Eq(y0, y1)]`
        if body.len() == 2
            && head.len() == 1
            && matches!(
                head[0],
                JAtom::Eq {
                    left: JTerm::Var { .. },
                    right: JTerm::Var { .. }
                }
            )
        {
            if let (
                JAtom::Concept {
                    concept: c1,
                    term: JTerm::Var { name: v1 },
                },
                JAtom::Concept {
                    concept: c2,
                    term: JTerm::Var { name: v2 },
                },
            ) = (body[0], body[1])
            {
                let cc1 = canon_concept(c1);
                let cc2 = canon_concept(c2);
                if cc1 == cc2 && v1 != v2 {
                    singleton_concepts.insert(cc1);
                    continue;
                }
            }
        }

        let body_roles: Vec<(&str, &JTerm, &JTerm)> = body
            .iter()
            .filter_map(|a| match a {
                JAtom::Role {
                    role,
                    source,
                    target,
                } => Some((role.as_str(), source, target)),
                _ => None,
            })
            .collect();

        // Pure concept clauses on a single variable `x`
        if body_roles.is_empty()
            && body.iter().all(|a| matches!(a, JAtom::Concept { term: JTerm::Var { .. }, .. }))
        {
            let mut vars: HashSet<&str> = HashSet::new();
            for a in &body {
                if let JAtom::Concept { term: JTerm::Var { name }, .. } = a {
                    vars.insert(name.as_str());
                }
            }
            for a in &head {
                match a {
                    JAtom::Concept { term: JTerm::Var { name }, .. } => {
                        vars.insert(name.as_str());
                    }
                    JAtom::Role {
                        source: JTerm::Var { name },
                        target: JTerm::Ind { .. },
                        ..
                    }
                    | JAtom::Role {
                        source: JTerm::Ind { .. },
                        target: JTerm::Var { name },
                        ..
                    }
                    | JAtom::Role {
                        source: JTerm::Var { name },
                        target: JTerm::Var { .. },
                        ..
                    } => {
                        vars.insert(name.as_str());
                    }
                    JAtom::Eq {
                        left: JTerm::Var { name },
                        right: JTerm::Ind { .. },
                    }
                    | JAtom::Eq {
                        left: JTerm::Ind { .. },
                        right: JTerm::Var { name },
                    } => {
                        vars.insert(name.as_str());
                    }
                    _ => {}
                }
            }
            if vars.len() <= 1 {
                let b_concepts: Vec<String> = body
                    .iter()
                    .filter_map(|a| match a {
                        JAtom::Concept { concept, .. } => Some(canon_concept(concept)),
                        _ => None,
                    })
                    .collect();
                if head.len() == 1 {
                    match head[0] {
                        JAtom::Role {
                            role,
                            source: JTerm::Var { .. },
                            target: JTerm::Ind { name: ind },
                        } => {
                            if let Some(u_t) = resolve_ind_elem(ind) {
                                let (rs, inv) = canon_role(role);
                                has_value_rules.push(HasValueClauseRule {
                                    body: b_concepts,
                                    role: rs,
                                    inv,
                                    target_elem: u_t,
                                });
                                continue;
                            }
                        }
                        JAtom::Role {
                            role,
                            source: JTerm::Ind { name: ind },
                            target: JTerm::Var { .. },
                        } => {
                            if let Some(u_t) = resolve_ind_elem(ind) {
                                let (rs, inv) = canon_role(role);
                                has_value_rules.push(HasValueClauseRule {
                                    body: b_concepts,
                                    role: rs,
                                    inv: !inv,
                                    target_elem: u_t,
                                });
                                continue;
                            }
                        }
                        JAtom::Role {
                            role,
                            source: JTerm::Var { name: s },
                            target: JTerm::Var { name: t },
                        } if s == t => {
                            let (rs, _) = canon_role(role);
                            if b_concepts.is_empty() || b_concepts == ["owl:Thing"] {
                                for u in 0..n_elems {
                                    edge_set.insert((u, rs.clone(), u));
                                    proved_edge_set.insert((u, rs.clone(), u));
                                }
                            } else {
                                for bc in &b_concepts {
                                    class_has_self.push((bc.clone(), rs.clone()));
                                }
                            }
                            continue;
                        }
                        JAtom::Eq {
                            left: JTerm::Var { .. },
                            right: JTerm::Ind { name: ind },
                        }
                        | JAtom::Eq {
                            left: JTerm::Ind { name: ind },
                            right: JTerm::Var { .. },
                        } => {
                            if let Some(u_o) = resolve_ind_elem(ind) {
                                concept_rules.push(ConceptClauseRule {
                                    body: b_concepts,
                                    heads: Vec::new(),
                                    nom_merge: Some(u_o),
                                });
                                continue;
                            }
                        }
                        _ => {}
                    }
                }
                if head.iter().all(|a| matches!(a, JAtom::Concept { term: JTerm::Var { .. }, .. })) {
                    let mut h_concepts: Vec<String> = Vec::new();
                    let mut nom_merge = None;
                    for a in &head {
                        if let JAtom::Concept { concept, .. } = a {
                            let cc = canon_concept(concept);
                            if cc != "owl:Nothing" {
                                if head.len() == 1 {
                                    if let Some(pub_i) = cc.strip_prefix("__nom__") {
                                        nom_merge = ind_to_elem.get(pub_i).copied();
                                    }
                                }
                                h_concepts.push(cc);
                            }
                        }
                    }
                    if b_concepts.iter().any(|b| h_concepts.contains(b)) {
                        continue;
                    }
                    concept_rules.push(ConceptClauseRule {
                        body: b_concepts,
                        heads: h_concepts,
                        nom_merge,
                    });
                    continue;
                }
            }
        }

        // Single-role body clauses `[r(x, y), A(x), C(y)] -> head`
        if body_roles.len() == 1 {
            let (raw_r, s_term, t_term) = body_roles[0];
            let (r_short, r_inv) = canon_role(raw_r);
            let (x_term, y_term) = if r_inv {
                (t_term, s_term)
            } else {
                (s_term, t_term)
            };
            let self_only = x_term == y_term;
            let mut body_x = Vec::new();
            let mut body_y = Vec::new();
            if let JTerm::Ind { name: ind_x } = x_term {
                if let Some(u_x) = resolve_ind_elem(ind_x) {
                    if let Some(p_x) = elem_inds[u_x].first() {
                        body_x.push(format!("__nom__{p_x}"));
                    }
                }
            }
            if let JTerm::Ind { name: ind_y } = y_term {
                if let Some(u_y) = resolve_ind_elem(ind_y) {
                    if let Some(p_y) = elem_inds[u_y].first() {
                        body_y.push(format!("__nom__{p_y}"));
                    }
                }
            }
            let mut body_ok = true;
            for a in &body {
                match a {
                    JAtom::Role { .. } => {}
                    JAtom::Concept { concept, term } => {
                        let cc = canon_concept(concept);
                        if cc == "owl:Thing" {
                            continue;
                        }
                        if term == x_term {
                            body_x.push(cc);
                        } else if term == y_term {
                            body_y.push(cc);
                        } else {
                            body_ok = false;
                        }
                    }
                    _ => body_ok = false,
                }
            }
            if body_ok {
                let action_opt = match head.as_slice() {
                    [] => Some(RoleHeadAction::Clash),
                    [JAtom::Concept { concept, term }] => {
                        let cc = canon_concept(concept);
                        if cc == "owl:Nothing" {
                            Some(RoleHeadAction::Clash)
                        } else if term == x_term {
                            if let Some(pub_i) = cc.strip_prefix("__nom__") {
                                ind_to_elem
                                    .get(pub_i)
                                    .copied()
                                    .map(RoleHeadAction::MergeXElem)
                            } else {
                                Some(RoleHeadAction::AddX(cc))
                            }
                        } else if term == y_term {
                            if let Some(pub_i) = cc.strip_prefix("__nom__") {
                                ind_to_elem
                                    .get(pub_i)
                                    .copied()
                                    .map(RoleHeadAction::MergeYElem)
                            } else {
                                Some(RoleHeadAction::AddY(cc))
                            }
                        } else {
                            None
                        }
                    }
                    [JAtom::Role {
                        role: h_role,
                        source: hs,
                        target: ht,
                    }] => {
                        let (hrs, hinv) = canon_role(h_role);
                        let (hx, hy) = if hinv { (ht, hs) } else { (hs, ht) };
                        if hx == x_term && hy == y_term {
                            Some(RoleHeadAction::AddRole(hrs, false))
                        } else if hx == y_term && hy == x_term {
                            Some(RoleHeadAction::AddRole(hrs, true))
                        } else {
                            None
                        }
                    }
                    [JAtom::Eq { left, right }] => {
                        if (left == x_term && right == y_term) || (left == y_term && right == x_term)
                        {
                            Some(RoleHeadAction::MergeXY)
                        } else if left == x_term {
                            if let JTerm::Ind { name } = right {
                                resolve_ind_elem(name).map(RoleHeadAction::MergeXElem)
                            } else {
                                None
                            }
                        } else if right == x_term {
                            if let JTerm::Ind { name } = left {
                                resolve_ind_elem(name).map(RoleHeadAction::MergeXElem)
                            } else {
                                None
                            }
                        } else if left == y_term {
                            if let JTerm::Ind { name } = right {
                                resolve_ind_elem(name).map(RoleHeadAction::MergeYElem)
                            } else {
                                None
                            }
                        } else if right == y_term {
                            if let JTerm::Ind { name } = left {
                                resolve_ind_elem(name).map(RoleHeadAction::MergeYElem)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    many if many.len() >= 2 => {
                        let mut disj = Vec::new();
                        let mut all_ok = true;
                        for ha in many {
                            if let JAtom::Concept { concept, term } = ha {
                                let cc = canon_concept(concept);
                                if term == x_term {
                                    disj.push((false, cc));
                                } else if term == y_term {
                                    disj.push((true, cc));
                                } else {
                                    all_ok = false;
                                }
                            } else {
                                all_ok = false;
                            }
                        }
                        all_ok.then_some(RoleHeadAction::Disj(disj))
                    }
                    _ => None,
                };
                if let Some(action) = action_opt {
                    role_rules.push(RoleClauseRule {
                        role: r_short,
                        self_only,
                        body_x,
                        body_y,
                        action,
                    });
                    continue;
                }
            }
        }

        // Multi-role body clauses: functionality / at-most-N / disjoint / asymmetric / chain
        if body_roles.len() >= 2 {
            // Disjoint / asymmetric 2-role clash: `[r1(x, y), r2(x, y)] -> []` or `[r(x, y), r(y, x)] -> []`
            if body_roles.len() == 2 && body.len() == 2 && head.is_empty() {
                let (r1, s1, t1) = body_roles[0];
                let (r2, s2, t2) = body_roles[1];
                let (rs1, inv1) = canon_role(r1);
                let (rs2, inv2) = canon_role(r2);
                let (x1, y1) = if inv1 { (t1, s1) } else { (s1, t1) };
                let (x2, y2) = if inv2 { (t2, s2) } else { (s2, t2) };
                if x1 == x2 && y1 == y2 {
                    disjoint_role_groups.push(vec![rs1, rs2]);
                    continue;
                } else if x1 == y2 && y1 == x2 && rs1 == rs2 {
                    asym_roles.insert(rs1);
                    continue;
                }
            }
            // Role chain `[r1(x, y), r2(y, z), ...] -> [r3(x, z)]` (already handled by `meta.rbox`)
            if body_roles.len() >= 2
                && body.len() == body_roles.len()
                && head.len() == 1
                && matches!(head[0], JAtom::Role { .. })
            {
                continue;
            }
            // At-most-N / functionality: `k` role atoms on the same base role sharing `x`, with `Eq(y_i, y_j)` in head
            let norm_roles: Vec<(String, &JTerm, &JTerm)> = body_roles
                .iter()
                .map(|&(r, s, t)| {
                    let (rs, inv) = canon_role(r);
                    if inv {
                        (rs, t, s)
                    } else {
                        (rs, s, t)
                    }
                })
                .collect();
            let first_r = &norm_roles[0].0;
            if norm_roles.iter().all(|(r, _, _)| r == first_r)
                && !head.is_empty()
                && head.iter().all(|a| matches!(a, JAtom::Eq { .. }))
            {
                let shared_src = norm_roles.iter().all(|(_, s, _)| *s == norm_roles[0].1);
                let shared_tgt = norm_roles.iter().all(|(_, _, t)| *t == norm_roles[0].2);
                if shared_src || shared_tgt {
                    let center = if shared_src {
                        norm_roles[0].1
                    } else {
                        norm_roles[0].2
                    };
                    let mut body_x = Vec::new();
                    let mut body_y = Vec::new();
                    for a in &body {
                        if let JAtom::Concept { concept, term } = a {
                            let cc = canon_concept(concept);
                            if cc == "owl:Thing" {
                                continue;
                            }
                            if term == center {
                                body_x.push(cc);
                            } else if !body_y.contains(&cc) {
                                body_y.push(cc);
                            }
                        }
                    }
                    let max_n = body_roles.len() - 1;
                    qual_func_rules.push(QualFuncRule {
                        role: first_r.clone(),
                        inv: !shared_src,
                        max_n,
                        body_x,
                        body_y,
                    });
                    continue;
                }
            }
        }
        has_unhandled_clause = true;
    }

    // Sorted so the witness materialization below (whose element numbering and
    // witness reuse depend on this order) is the same in every run.
    let mut skolem_vec: Vec<((String, String), ExistentialGroup)> =
        skolem_groups.into_iter().collect();
    skolem_vec.sort_by(|a, b| a.0.cmp(&b.0));
    let skolem_vec: Vec<(String, ExistentialGroup)> =
        skolem_vec.into_iter().map(|((fn_name, _), grp)| (fn_name, grp)).collect();
    for (_, grp) in &skolem_vec {
        if let Some((ref r_short, inv)) = grp.role {
            for f in &grp.fillers {
                if let Some(rest) = f.strip_prefix("__nom__") {
                    if let Some(&target_elem) = ind_to_elem
                        .get(rest)
                        .or_else(|| ind_lookup.get(rest).and_then(|p| ind_to_elem.get(p)))
                    {
                        has_value_rules.push(HasValueClauseRule {
                            body: grp.body.clone(),
                            role: r_short.clone(),
                            inv,
                            target_elem,
                        });
                    }
                }
            }
        }
    }

    // Build trigger indexes for fast rule lookup. Every saturation below pops
    // a concept from a worklist and checks the rules indexed under it, so a
    // rule must be indexed under EVERY body concept: indexed under `body[0]`
    // only, the rule `A ⊓ B → C` is never re-examined when `B` is derived after
    // `A` was popped, and whether it fires depends on the (randomly seeded)
    // `HashSet` iteration order of the worklist. That lost the clash of
    // `p3.ofn` in about half of all runs and made `NotDifferent` claim a
    // model that was not one.
    fn index_by_every_body_concept(
        index: &mut HashMap<String, Vec<usize>>,
        idx: usize,
        body: &[String],
    ) {
        let mut seen: HashSet<&str> = HashSet::new();
        for b in body {
            if seen.insert(b.as_str()) {
                index.entry(b.clone()).or_default().push(idx);
            }
        }
    }
    let mut empty_body_concept_rules: Vec<usize> = Vec::new();
    let mut concept_rules_by_trigger: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, cr) in concept_rules.iter().enumerate() {
        if cr.body.is_empty() {
            empty_body_concept_rules.push(idx);
        } else {
            index_by_every_body_concept(&mut concept_rules_by_trigger, idx, &cr.body);
        }
    }
    let mut empty_body_hv_rules: Vec<usize> = Vec::new();
    let mut hv_rules_by_trigger: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, hv) in has_value_rules.iter().enumerate() {
        if hv.body.is_empty() {
            empty_body_hv_rules.push(idx);
        } else {
            index_by_every_body_concept(&mut hv_rules_by_trigger, idx, &hv.body);
        }
    }
    let mut role_rules_by_role: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, rr) in role_rules.iter().enumerate() {
        role_rules_by_role
            .entry(rr.role.clone())
            .or_default()
            .push(idx);
    }
    let mut skolem_by_trigger: HashMap<String, Vec<usize>> = HashMap::new();
    let mut empty_body_skolem: Vec<usize> = Vec::new();
    for (idx, (_, grp)) in skolem_vec.iter().enumerate() {
        if grp.body.is_empty() {
            empty_body_skolem.push(idx);
        } else {
            skolem_by_trigger
                .entry(grp.body[0].clone())
                .or_default()
                .push(idx);
        }
    }
    let mut cards_by_marker: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, card) in f_res.cardinalities.iter().enumerate() {
        cards_by_marker
            .entry(canon_concept(&card.marker))
            .or_default()
            .push(idx);
    }

    let has_horn_merges = raw.abox_elided
        && (!func_obj_roles.is_empty()
            || !inv_func_obj_roles.is_empty()
            || qual_func_rules.iter().any(|qf| qf.max_n == 1)
            || concept_rules
                .iter()
                .any(|cr| cr.nom_merge.is_some() && cr.heads.len() <= 1)
            || role_rules.iter().any(|rr| {
                matches!(
                    rr.action,
                    RoleHeadAction::MergeXElem(_)
                        | RoleHeadAction::MergeYElem(_)
                        | RoleHeadAction::MergeXY
                )
            }));

    // Set when a saturation stops at its guard bound before its fixpoint; the
    // plan is then declined so the caller runs the exact probe path.
    let horn_saturation_cut = std::cell::Cell::new(false);
    let unrepresented_named_merge = std::cell::Cell::new(false);
    // Saturate a `(classes, edges)` state under deterministic 1-head Horn rules
    let saturate_horn_in_place = |classes: &mut [HashSet<String>],
                                  edges: &mut HashSet<(usize, String, usize)>|
     -> Vec<(usize, usize)> {
        let num = classes.len();
        let mut uf: Vec<usize> = (0..num).collect();
        fn find_uf(uf: &mut [usize], mut x: usize) -> usize {
            while uf[x] != x {
                uf[x] = uf[uf[x]];
                x = uf[x];
            }
            x
        }
        fn union_uf(uf: &mut [usize], a: usize, b: usize) -> bool {
            let ra = find_uf(uf, a);
            let rb = find_uf(uf, b);
            if ra == rb {
                return false;
            }
            let (keep, drop_el) = (ra.min(rb), ra.max(rb));
            uf[drop_el] = keep;
            true
        }
        let _ = crate::engine::close_edges_under_rbox_rows(&meta.rbox, num, edges);
        close_elem_classes(classes);
        // Run to the fixpoint. The state (classes from rule heads, edges over
        // `num` elements, the union-find partition) is finite and every round
        // that sets `changed` grows it, so the loop terminates. A former cap of
        // 8 rounds stopped the saturation of the model `M_0` early. The bound
        // below is a guard only: hitting it marks the plan as unusable.
        let mut reached_fixpoint = false;
        for _round in 0..HORN_SATURATION_MAX_ROUNDS {
            let mut changed = false;
            let mut merged_any = false;
            for u in 0..num {
                let mut work: Vec<String> = classes[u].iter().cloned().collect();
                for &idx in &empty_body_concept_rules {
                    let cr = &concept_rules[idx];
                    if cr.heads.len() == 1 && cr.nom_merge.is_none() {
                        let h = &cr.heads[0];
                        if classes[u].insert(h.clone()) {
                            work.push(h.clone());
                            changed = true;
                        }
                    } else if cr.heads.len() <= 1 {
                        if let Some(u_o) = cr.nom_merge {
                            if u_o < num && union_uf(&mut uf, u, u_o) {
                                merged_any = true;
                            }
                        }
                    }
                }
                while let Some(c) = work.pop() {
                    if let Some(sups) = subs_map.get(&c) {
                        for sup in sups {
                            if classes[u].insert(sup.clone()) {
                                work.push(sup.clone());
                                changed = true;
                            }
                        }
                    }
                    if let Some(indices) = concept_rules_by_trigger.get(&c) {
                        for &idx in indices {
                            let cr = &concept_rules[idx];
                            if cr.heads.len() == 1
                                && cr.nom_merge.is_none()
                                && cr.body.iter().all(|b| classes[u].contains(b))
                            {
                                let h = &cr.heads[0];
                                if classes[u].insert(h.clone()) {
                                    work.push(h.clone());
                                    changed = true;
                                }
                            } else if cr.heads.len() <= 1
                                && cr.body.iter().all(|b| classes[u].contains(b))
                            {
                                // `[B(x)] -> [x = o]` (head `{o}` or none):
                                // a Horn nominal merge.
                                if let Some(u_o) = cr.nom_merge {
                                    if u_o < num && union_uf(&mut uf, u, u_o) {
                                        merged_any = true;
                                    }
                                }
                            }
                        }
                    }
                }
                for (c_iri, r_short) in &class_has_self {
                    if classes[u].contains(c_iri) && edges.insert((u, r_short.clone(), u)) {
                        changed = true;
                    }
                }
                for &idx in &empty_body_hv_rules {
                    let hv = &has_value_rules[idx];
                    if hv.target_elem < num {
                        let edge = if hv.inv {
                            (hv.target_elem, hv.role.clone(), u)
                        } else {
                            (u, hv.role.clone(), hv.target_elem)
                        };
                        if edges.insert(edge) {
                            changed = true;
                        }
                    }
                }
                let snap_c: Vec<String> = classes[u].iter().cloned().collect();
                for c in &snap_c {
                    if let Some(indices) = hv_rules_by_trigger.get(c) {
                        for &idx in indices {
                            let hv = &has_value_rules[idx];
                            if hv.target_elem < num
                                && hv.body.iter().all(|b| classes[u].contains(b))
                            {
                                let edge = if hv.inv {
                                    (hv.target_elem, hv.role.clone(), u)
                                } else {
                                    (u, hv.role.clone(), hv.target_elem)
                                };
                                if edges.insert(edge) {
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
            let edge_snap: Vec<(usize, String, usize)> = edges.iter().cloned().collect();
            for &(u, ref r, v) in &edge_snap {
                let Some(indices) = role_rules_by_role.get(r) else {
                    continue;
                };
                for &idx in indices {
                    let rr = &role_rules[idx];
                    if rr.self_only && u != v {
                        continue;
                    }
                    if !rr.body_x.iter().all(|b| classes[u].contains(b))
                        || !rr.body_y.iter().all(|b| classes[v].contains(b))
                    {
                        continue;
                    }
                    match &rr.action {
                        RoleHeadAction::AddX(d) => {
                            if classes[u].insert(d.clone()) {
                                changed = true;
                            }
                        }
                        RoleHeadAction::AddY(d) => {
                            if classes[v].insert(d.clone()) {
                                changed = true;
                            }
                        }
                        RoleHeadAction::AddRole(s, inv) => {
                            let edge = if *inv {
                                (v, s.clone(), u)
                            } else {
                                (u, s.clone(), v)
                            };
                            if edges.insert(edge) {
                                changed = true;
                            }
                        }
                        RoleHeadAction::MergeXElem(u_o) if *u_o < num => {
                            if union_uf(&mut uf, u, *u_o) {
                                merged_any = true;
                            }
                        }
                        RoleHeadAction::MergeYElem(u_o) if *u_o < num => {
                            if union_uf(&mut uf, v, *u_o) {
                                merged_any = true;
                            }
                        }
                        RoleHeadAction::MergeXY => {
                            if union_uf(&mut uf, u, v) {
                                merged_any = true;
                            }
                        }
                        _ => {}
                    }
                }
            }
            if has_horn_merges {
                if !func_obj_roles.is_empty() || !inv_func_obj_roles.is_empty() {
                    let mut func_seen: HashMap<(usize, &str), usize> = HashMap::new();
                    let mut inv_func_seen: HashMap<(usize, &str), usize> = HashMap::new();
                    for &(u, ref r, v) in &edge_snap {
                        let ru = find_uf(&mut uf, u);
                        let rv = find_uf(&mut uf, v);
                        if func_obj_roles.contains(r.as_str()) {
                            if let Some(&v0) = func_seen.get(&(ru, r.as_str())) {
                                if union_uf(&mut uf, v0, rv) {
                                    merged_any = true;
                                }
                            } else {
                                func_seen.insert((ru, r.as_str()), rv);
                            }
                        }
                        if inv_func_obj_roles.contains(r.as_str()) {
                            if let Some(&u0) = inv_func_seen.get(&(rv, r.as_str())) {
                                if union_uf(&mut uf, u0, ru) {
                                    merged_any = true;
                                }
                            } else {
                                inv_func_seen.insert((rv, r.as_str()), ru);
                            }
                        }
                    }
                }
                for qf in &qual_func_rules {
                    if qf.max_n != 1 {
                        continue;
                    }
                    let mut seen_target: HashMap<usize, usize> = HashMap::new();
                    for &(s, ref r, t) in &edge_snap {
                        if r != &qf.role {
                            continue;
                        }
                        let (center, target) = if qf.inv { (t, s) } else { (s, t) };
                        let rc = find_uf(&mut uf, center);
                        let rt = find_uf(&mut uf, target);
                        if !qf
                            .body_x
                            .iter()
                            .all(|b| classes[rc].contains(b) || classes[center].contains(b))
                            || !qf
                                .body_y
                                .iter()
                                .all(|b| classes[rt].contains(b) || classes[target].contains(b))
                        {
                            continue;
                        }
                        if let Some(&t0) = seen_target.get(&rc) {
                            if union_uf(&mut uf, t0, rt) {
                                merged_any = true;
                            }
                        } else {
                            seen_target.insert(rc, rt);
                        }
                    }
                }
                let any_non_root = (0..num).any(|u| find_uf(&mut uf, u) != u);
                if merged_any || (changed && any_non_root) {
                    for u in 0..num {
                        let r = find_uf(&mut uf, u);
                        if r != u {
                            let cu: Vec<String> = classes[u].iter().cloned().collect();
                            for c in cu {
                                if classes[r].insert(c) {
                                    changed = true;
                                }
                            }
                        }
                    }
                    for u in 0..num {
                        let r = find_uf(&mut uf, u);
                        if r != u {
                            let cr: Vec<String> = classes[r].iter().cloned().collect();
                            for c in cr {
                                if classes[u].insert(c) {
                                    changed = true;
                                }
                            }
                        }
                    }
                    let cur_edges: Vec<(usize, String, usize)> = edges.iter().cloned().collect();
                    for (s, role, t) in cur_edges {
                        let rs = find_uf(&mut uf, s);
                        let rt = find_uf(&mut uf, t);
                        if (rs != s || rt != t) && edges.insert((rs, role, rt)) {
                            changed = true;
                        }
                    }
                    if merged_any {
                        changed = true;
                    }
                }
            }
            if changed {
                let _ = crate::engine::close_edges_under_rbox_rows(&meta.rbox, num, edges);
                close_elem_classes(classes);
            } else {
                reached_fixpoint = true;
                break;
            }
        }
        if !reached_fixpoint {
            horn_saturation_cut.set(true);
        }
        // Two named elements forced equal by Horn rules (a nominal domain,
        // `⊤ ⊑ =1 r` with a nominal domain, `B ⊑ {o}`) when the plan does not
        // carry Horn merges (`has_horn_merges` needs an elided ABox): the
        // structure keeps them apart, so it is not a model and its rows of the
        // merged individuals are incomplete (g7002_0026 lost `t0(a1, a0)`,
        // f4104_41 lost 3,240 VALUE rows). Decline; the exact probes answer.
        if !has_horn_merges
            && (0..num.min(n_elems)).any(|u| {
                let r = find_uf(&mut uf, u);
                r != u && r < n_elems
            })
        {
            unrepresented_named_merge.set(true);
        }
        let mut merged_named_pairs: Vec<(usize, usize)> = Vec::new();
        if has_horn_merges && (0..num).any(|u| find_uf(&mut uf, u) != u) {
            let mut members_by_root: HashMap<usize, Vec<usize>> = HashMap::new();
            for u in 0..num.min(n_elems) {
                let r = find_uf(&mut uf, u);
                if r != u && r < n_elems {
                    merged_named_pairs.push((r, u));
                }
                if r < n_elems {
                    members_by_root.entry(r).or_default().push(u);
                }
            }
            let cur_edges: Vec<(usize, String, usize)> = edges.iter().cloned().collect();
            for (s, role, t) in cur_edges {
                let rs = find_uf(&mut uf, s);
                let rt = find_uf(&mut uf, t);
                edges.insert((rs, role.clone(), rt));
                if rs < n_elems && rt < n_elems {
                    if let (Some(ms), Some(mt)) =
                        (members_by_root.get(&rs), members_by_root.get(&rt))
                    {
                        if ms.len() > 1 || mt.len() > 1 {
                            for &us in ms {
                                for &ut in mt {
                                    edges.insert((us, role.clone(), ut));
                                }
                            }
                        }
                    }
                }
            }
        }
        merged_named_pairs
    };

    // First saturate initial element classes/edges so normalizer definers (`Q_0`, ...) hold
    let mut proved_merges = saturate_horn_in_place(&mut entailed_elem_classes, &mut proved_edge_set);
    let _ = saturate_horn_in_place(&mut elem_classes, &mut edge_set);

    // Materialize Skolem existential witnesses on `elem_classes`/`edge_set`
    // and `entailed_elem_classes`/`proved_edge_set` so universal restrictions and
    // existential checks see asserted existential successors (`d2.ofn`, `adv4`, `13700`).
    let mut n_total_elems = n_elems;
    // `skolem_witness_of[(u, f)]` is the element that stands for the Skolem
    // term `f(u)` in the entailed structure `H_0`: only an element created here
    // for exactly that term while the group's body is entailed at `u`. The
    // Skolem inequality test `[M(x), f1(x) = f2(x)] -> []` below concludes a
    // clash from `find(w1) == find(w2)`, which is sound only if `w1` and `w2`
    // are the terms `f1(u)` and `f2(u)`. A reused successor that merely
    // carries the fillers is not: two functions of a min-cardinality could map
    // to the same reused element, and every merge touching `u` then reported a
    // clash (g7001_0022: `≥ 2 s0.D` at `a2` made `a2` "different" from all).
    let mut skolem_witness_of: HashMap<(usize, String), usize> = HashMap::new();
    let sk_rounds = if has_horn_merges { 3 } else { 2 };
    for _sk_round in 0..sk_rounds {
        let cur_limit = n_total_elems;
        let mut added_sk = false;
        let mut proved_out: HashMap<(usize, String), Vec<usize>> = HashMap::new();
        let mut proved_in: HashMap<(usize, String), Vec<usize>> = HashMap::new();
        for &(s, ref r, t) in &proved_edge_set {
            proved_out.entry((s, r.clone())).or_default().push(t);
            proved_in.entry((t, r.clone())).or_default().push(s);
        }
        let mut model_out: HashMap<(usize, String), Vec<usize>> = HashMap::new();
        let mut model_in: HashMap<(usize, String), Vec<usize>> = HashMap::new();
        for &(s, ref r, t) in &edge_set {
            model_out.entry((s, r.clone())).or_default().push(t);
            model_in.entry((t, r.clone())).or_default().push(s);
        }
        for (fn_name, grp) in &skolem_vec {
            let Some((ref r_short, inv)) = grp.role else {
                continue;
            };
            let is_data_role = data_role_set.contains(r_short);
            for u in 0..cur_limit {
                let in_entailed = grp.body.iter().all(|b| entailed_elem_classes[u].contains(b));
                let in_model = grp.body.iter().all(|b| elem_classes[u].contains(b));
                if !in_entailed && !in_model {
                    continue;
                }
                let key = (u, r_short.clone());
                let existing_entailed = if in_entailed {
                    let targets = if inv {
                        proved_in.get(&key)
                    } else {
                        proved_out.get(&key)
                    };
                    targets.and_then(|list| {
                        list.iter().copied().find(|&target| {
                            target < entailed_elem_classes.len()
                                && grp
                                    .fillers
                                    .iter()
                                    .all(|f| entailed_elem_classes[target].contains(f))
                        })
                    })
                } else {
                    None
                };
                let existing_model = if in_model {
                    let targets = if inv {
                        model_in.get(&key)
                    } else {
                        model_out.get(&key)
                    };
                    targets.and_then(|list| {
                        list.iter().copied().find(|&target| {
                            target < elem_classes.len()
                                && grp.fillers.iter().all(|f| elem_classes[target].contains(f))
                        })
                    })
                } else {
                    None
                };
                let already_in_entailed = !in_entailed || existing_entailed.is_some();
                let already_in_model = !in_model || existing_model.is_some();
                if !already_in_entailed || !already_in_model {
                    let w_sk = n_total_elems;
                    n_total_elems += 1;
                    if in_entailed && !already_in_entailed {
                        skolem_witness_of.entry((u, fn_name.clone())).or_insert(w_sk);
                    }
                    let sort_tag = if is_data_role {
                        crate::frontend::sorts::DATA_SORT
                    } else {
                        crate::frontend::sorts::OBJECT_SORT
                    };
                    let mut f_set: HashSet<String> = grp.fillers.iter().cloned().collect();
                    f_set.insert("owl:Thing".to_string());
                    f_set.insert(sort_tag.to_string());
                    elem_classes.push(f_set.clone());
                    entailed_elem_classes.push(if in_entailed {
                        f_set
                    } else {
                        let mut s = HashSet::new();
                        s.insert("owl:Thing".to_string());
                        s.insert(sort_tag.to_string());
                        s
                    });
                    elem_neg_classes.push(HashSet::new());
                    elem_inds.push(Vec::new());
                    let edge = if inv {
                        (w_sk, r_short.clone(), u)
                    } else {
                        (u, r_short.clone(), w_sk)
                    };
                    edge_set.insert(edge.clone());
                    if in_entailed {
                        proved_edge_set.insert(edge);
                    }
                    added_sk = true;
                }
            }
        }
        if added_sk {
            proved_merges.extend(saturate_horn_in_place(
                &mut entailed_elem_classes,
                &mut proved_edge_set,
            ));
            let _ = saturate_horn_in_place(&mut elem_classes, &mut edge_set);
        } else {
            break;
        }
    }
    if horn_saturation_cut.get() {
        if std::env::var_os("KM_TIMING").is_some() {
            eprintln!("KM_TIMING abox_rows: Horn saturation hit its guard bound; plan declined");
        }
        return None;
    }
    if unrepresented_named_merge.get() {
        if std::env::var_os("KM_TIMING").is_some() {
            eprintln!("KM_TIMING abox_rows: Horn rules merge named individuals the plan keeps apart; plan declined");
        }
        return None;
    }
    for (u_root, u_mem) in proved_merges {
        for a in &elem_inds[u_root] {
            for b in &elem_inds[u_mem] {
                same_pairs.push((a.clone(), b.clone()));
            }
        }
    }

    let mut same_adj: HashMap<&str, Vec<&str>> = HashMap::new();
    for (a, b) in &same_pairs {
        same_adj.entry(a.as_str()).or_default().push(b.as_str());
        same_adj.entry(b.as_str()).or_default().push(a.as_str());
    }
    let mut same_comp: HashMap<&str, usize> = HashMap::new();
    let mut cid = 0usize;
    for ind in &pub_individuals {
        if same_comp.contains_key(ind.as_str()) {
            continue;
        }
        cid += 1;
        let mut stack = vec![ind.as_str()];
        while let Some(cur) = stack.pop() {
            if same_comp.insert(cur, cid).is_none() {
                if let Some(nbrs) = same_adj.get(cur) {
                    stack.extend(nbrs.iter().copied());
                }
            }
        }
    }

    let mut plan = ModelAboxPlan::default();

    if values_requested && bound_disabled {
        for r_idx in 0..roles.len() {
            for b_idx in 0..individuals.len() {
                plan.residual_value_targets.insert((r_idx, b_idx));
            }
        }
        for a_idx in 0..individuals.len() {
            plan.residual_value_sources.insert(a_idx);
        }
    } else if values_requested {
        let has_non_horn_elem_merge = !raw.abox_elided
            && raw.route != "el-canonical"
            && (0..n_elems).any(|u| {
                elem_inds[u].len() > 1 && {
                    let c0 = same_comp.get(elem_inds[u][0].as_str());
                    elem_inds[u][1..]
                        .iter()
                        .any(|ind| same_comp.get(ind.as_str()) != c0)
                }
            });
        if has_non_horn_elem_merge {
            let raw_elided = super::model_export::RawModel {
                route: raw.route,
                contexts: Vec::new(),
                labels: Vec::new(),
                edges: Vec::new(),
                blocked: Vec::new(),
                witness_exact: raw.witness_exact,
                witness_exact_by_class: BTreeMap::new(),
                witnesses: BTreeMap::new(),
                extra_witnesses: Vec::new(),
                closure: raw.closure,
                partial_reason: None,
                extra_values: raw.extra_values.clone(),
                base_labels: Vec::new(),
                base_edges: Vec::new(),
                abox_elided: true,
            };
            if let Some(unmerged_plan) = from_exported_model(
                text,
                roles,
                individuals,
                true,
                false,
                classification,
                realization,
                &raw_elided,
                meta,
            ) {
                plan.proved_values = unmerged_plan.proved_values;
            }
        } else {
            for (u, r, v) in &proved_edge_set {
                if *u >= n_elems || *v >= n_elems {
                    continue;
                }
                let full_r = meta.iri_map.get(r).map(String::as_str).unwrap_or(r.as_str());
                let Some(pub_r) = role_lookup.get(full_r).or_else(|| role_lookup.get(r)) else {
                    continue;
                };
                if u != v {
                    for a in &elem_inds[*u] {
                        for b in &elem_inds[*v] {
                            plan.proved_values
                                .insert([pub_r.clone(), a.clone(), b.clone()]);
                        }
                    }
                } else {
                    for a in &elem_inds[*u] {
                        for b in &elem_inds[*u] {
                            if a == b || same_comp.get(a.as_str()) == same_comp.get(b.as_str()) {
                                plan.proved_values
                                    .insert([pub_r.clone(), a.clone(), b.clone()]);
                            }
                        }
                    }
                }
            }
        }
        for (u, r, v) in &edge_set {
            if *u >= n_elems || *v >= n_elems {
                continue;
            }
            let full_r = meta.iri_map.get(r).map(String::as_str).unwrap_or(r.as_str());
            let Some(pub_r) = role_lookup.get(full_r).or_else(|| role_lookup.get(r)) else {
                continue;
            };
            let Some(&r_idx) = pub_role_to_idx.get(pub_r) else {
                continue;
            };
            for a in &elem_inds[*u] {
                for b in &elem_inds[*v] {
                    let row = [pub_r.clone(), a.clone(), b.clone()];
                    if !plan.proved_values.contains(&row) {
                        if let (Some(&a_idx), Some(&b_idx)) =
                            (pub_ind_to_idx.get(a), pub_ind_to_idx.get(b))
                        {
                            plan.residual_value_targets.insert((r_idx, b_idx));
                            plan.residual_value_sources.insert(a_idx);
                        }
                    }
                }
            }
        }
        let value_trace = std::env::var_os("KM_DIFF_TRACE").is_some();
        if value_trace {
            eprintln!(
                "KM_DIFF_TRACE values: n_elems={n_elems} individuals={} targets after model edges={}",
                individuals.len(),
                plan.residual_value_targets.len()
            );
        }
        if let Some(spec) = &fresh_spec {
            let mut input = spec.input.clone();
            input.flag_named_self_and_nominal = true;
            for (u, r, v) in &edge_set {
                if *u < n_elems && *v < n_elems {
                    input.named_roles.insert(r.clone());
                }
            }
            let nominal = spec.input.merge_into_named || !spec.input.nominal_roles.is_empty();
            let fresh_roles = crate::frontend::named_role_bound::excursion_roles(&meta.rbox, &input);
            for r in &fresh_roles {
                let full_r = meta.iri_map.get(r).map(String::as_str).unwrap_or(r.as_str());
                let Some(pub_r) = role_lookup.get(full_r).or_else(|| role_lookup.get(r)) else {
                    continue;
                };
                let Some(&r_idx) = pub_role_to_idx.get(pub_r) else {
                    continue;
                };
                for &x in &fresh_inds {
                    let px = &pub_individuals[x];
                    let others: Vec<usize> = if nominal { (0..pub_individuals.len()).collect() } else { vec![x] };
                    for y in others {
                        let py = &pub_individuals[y];
                        if !plan.proved_values.contains(&[pub_r.clone(), px.clone(), py.clone()]) {
                            plan.residual_value_targets.insert((r_idx, y));
                            plan.residual_value_sources.insert(x);
                        }
                        if y != x && !plan.proved_values.contains(&[pub_r.clone(), py.clone(), px.clone()]) {
                            plan.residual_value_targets.insert((r_idx, x));
                            plan.residual_value_sources.insert(y);
                        }
                    }
                }
            }
        }
        // Anonymous-excursion candidates, recomputed on the final `edge_set`
        // (Horn merges may have joined components): every unproved row of an
        // excursion role inside one component goes to the residual probes.
        if let Some(spec) = &excursion_spec {
            let bound = ExcursionBound::compute(spec, &meta.rbox, n_elems, &edge_set);
            let mut comp_inds: HashMap<usize, Vec<&String>> = HashMap::new();
            for u in 0..n_elems {
                comp_inds.entry(bound.comp[u]).or_default().extend(elem_inds[u].iter());
            }
            let comp_of_ind: HashMap<&str, usize> = (0..n_elems)
                .flat_map(|u| elem_inds[u].iter().map(move |a| (a.as_str(), u)))
                .map(|(a, u)| (a, bound.comp[u]))
                .collect();
            for r in &bound.roles {
                let full_r = meta.iri_map.get(r).map(String::as_str).unwrap_or(r.as_str());
                let Some(pub_r) = role_lookup.get(full_r).or_else(|| role_lookup.get(r)) else {
                    continue;
                };
                let Some(&r_idx) = pub_role_to_idx.get(pub_r) else {
                    continue;
                };
                let mut proved_into: HashMap<&str, usize> = HashMap::new();
                for [pr, a, b] in &plan.proved_values {
                    if pr == pub_r && comp_of_ind.get(a.as_str()) == comp_of_ind.get(b.as_str()) {
                        *proved_into.entry(b.as_str()).or_default() += 1;
                    }
                }
                for inds in comp_inds.values() {
                    let mut open = false;
                    for b in inds {
                        if proved_into.get(b.as_str()).copied().unwrap_or(0) < inds.len() {
                            if let Some(&b_idx) = pub_ind_to_idx.get(b.as_str()) {
                                plan.residual_value_targets.insert((r_idx, b_idx));
                                open = true;
                            }
                        }
                    }
                    if open {
                        for a in inds {
                            if let Some(&a_idx) = pub_ind_to_idx.get(a.as_str()) {
                                plan.residual_value_sources.insert(a_idx);
                            }
                        }
                    }
                }
            }
        }
        // Isolated, unconstrained individuals have no VALUE rows at all. An
        // individual `a` that occurs only in its declaration, annotations and
        // `ClassAssertion(A, a)` with named `A` (the set `S_a`) is isolated.
        // If the TBox holds at an element whose atomic classes are exactly
        // `S_a` and that has no successors (checked by `holds_at_bare`, see
        // MODEL-EXPORT.md), take any model `I` of `O` and re-point `a` to a new
        // such element: nothing else changes (no element has an edge to it, no
        // nominal names `a`, no universal role), so the result is a model of
        // `O` in which `a` has no edge. No row `r(a, x)` or `r(x, a)` is then
        // entailed, and its excursion candidates need no probe
        // (ore_ont_14012: 112 probe targets, 300 s timeout before).
        if !plan.residual_value_targets.is_empty() || !plan.residual_value_sources.is_empty() {
            let bare = bare_unconstrained_individuals(text, &|t: &str| {
                ind_lookup.get(&expand_tok(t)).or_else(|| ind_lookup.get(&public_name(t))).cloned()
            }, &expand_tok);
            if !bare.is_empty() {
                let is_bare = |i: usize| bare.contains(pub_individuals[i].as_str());
                let before = plan.residual_value_targets.len();
                plan.residual_value_targets.retain(|&(_, b)| !is_bare(b));
                plan.residual_value_sources.retain(|&a| !is_bare(a));
                if std::env::var_os("KM_TIMING").is_some() {
                    eprintln!(
                        "KM_TIMING abox_rows: {} bare individuals; value targets {} -> {}",
                        bare.len(),
                        before,
                        plan.residual_value_targets.len()
                    );
                }
            }
        }
        if value_trace {
            let roles_used: BTreeSet<usize> = plan.residual_value_targets.iter().map(|t| t.0).collect();
            let inds_used: BTreeSet<usize> = plan.residual_value_targets.iter().map(|t| t.1).collect();
            eprintln!(
                "KM_DIFF_TRACE values: fresh_inds={} excursion={} targets={} roles={:?} target_inds={} sources={} sample={:?}",
                fresh_inds.len(),
                excursion_spec.is_some(),
                plan.residual_value_targets.len(),
                roles_used.iter().map(|&r| roles[r].as_str()).collect::<Vec<_>>(),
                inds_used.len(),
                plan.residual_value_sources.len(),
                inds_used.iter().take(5).map(|&b| individuals[b].as_str()).collect::<Vec<_>>()
            );
        }
    }

    // An element of the exported model that holds several individuals whose
    // sameness is not proved (`same_comp`) is a choice of that model, not an
    // entailment: with `⊤ ⊑ {a8, a9}` the model puts `a0, a2, ...` into the
    // element of `a9`. Every element-level argument below reads an element as
    // one individual: `DifferentIndividuals(a9, a3)` made the two elements
    // different and printed `DIFFERENT a0 a8` and 13 more rows that are not
    // entailed (nc8302_0001; 2,225 rows in 750 cover cases). Then every pair
    // goes to the exact probe instead.
    let unproved_element_merge = (0..n_elems).any(|u| {
        elem_inds[u].len() > 1 && {
            let c0 = same_comp.get(elem_inds[u][0].as_str());
            elem_inds[u][1..].iter().any(|ind| same_comp.get(ind.as_str()) != c0)
        }
    });
    if different_requested && unproved_element_merge {
        for a in 0..individuals.len() {
            for b in (a + 1)..individuals.len() {
                plan.residual_different_pairs.insert((a, b));
            }
        }
        if std::env::var_os("KM_TIMING").is_some() {
            eprintln!(
                "KM_TIMING abox_rows: model elements merge individuals not proved same; {} pairs to the probes",
                plan.residual_different_pairs.len()
            );
        }
    } else if different_requested {
        let pair_key = |u: usize, v: usize| -> (usize, usize) { (u.min(v), u.max(v)) };
        let mut diff: HashSet<(usize, usize)> = HashSet::new();

        // (D1) Explicit `DifferentIndividuals`
        for grp in &diff_ind_groups {
            for i in 0..grp.len() {
                for j in (i + 1)..grp.len() {
                    if let (Some(&u), Some(&v)) =
                        (ind_to_elem.get(&grp[i]), ind_to_elem.get(&grp[j]))
                    {
                        if u != v {
                            diff.insert(pair_key(u, v));
                        }
                    }
                }
            }
        }

        // (D2) Entailed disjoint / complement classes
        let mut disjoint_pairs: HashSet<(String, String)> = HashSet::new();
        for grp in &disjoint_class_groups {
            for i in 0..grp.len() {
                for j in (i + 1)..grp.len() {
                    let (c1, c2) = (&grp[i], &grp[j]);
                    disjoint_pairs.insert((c1.clone(), c2.clone()));
                    disjoint_pairs.insert((c2.clone(), c1.clone()));
                }
            }
        }
        for rule in &concept_rules {
            if rule.heads.is_empty() && rule.nom_merge.is_none() && rule.body.len() == 2 {
                disjoint_pairs.insert((rule.body[0].clone(), rule.body[1].clone()));
                disjoint_pairs.insert((rule.body[1].clone(), rule.body[0].clone()));
            }
        }
        let ind_elems: Vec<usize> = (0..n_elems)
            .filter(|&u| !elem_inds[u].is_empty())
            .collect();
        if !disjoint_pairs.is_empty() {
            let mut class_to_elems: HashMap<&str, Vec<usize>> = HashMap::new();
            for &u in &ind_elems {
                for c in &entailed_elem_classes[u] {
                    class_to_elems.entry(c.as_str()).or_default().push(u);
                }
            }
            for (c1, c2) in &disjoint_pairs {
                if let (Some(us), Some(vs)) =
                    (class_to_elems.get(c1.as_str()), class_to_elems.get(c2.as_str()))
                {
                    for &u in us {
                        for &v in vs {
                            if u != v {
                                diff.insert(pair_key(u, v));
                            }
                        }
                    }
                }
            }
        }
        for (c_iri, ind_pub) in &class_disjoint_inds {
            if let Some(&v) = ind_to_elem.get(ind_pub) {
                for &u in &ind_elems {
                    if u != v && entailed_elem_classes[u].contains(c_iri) {
                        diff.insert(pair_key(u, v));
                    }
                }
            }
        }
        for &u in &ind_elems {
            if !elem_neg_classes[u].is_empty() {
                for neg_c in &elem_neg_classes[u] {
                    for &v in &ind_elems {
                        if u != v && entailed_elem_classes[v].contains(neg_c) {
                            diff.insert(pair_key(u, v));
                        }
                    }
                }
            }
        }
        // Value projection digits (`frontend::value_projection`) do not make
        // two individuals different: the digits of two values clash only on
        // an element of the counted guard class `C` (`C ⊓ digit_0 ⊓ digit_1 ⊑
        // ⊥`), and an element outside `C` may carry both values. Functional
        // properties are decided by (D4) below; the pair tests and the exact
        // probes decide the rest.

        // (D3) Entailed role edges (`proved_edge_set`) + negative/irreflexive/asymmetric/disjoint roles
        for &(ref r, ua, ub) in &neg_role_assertions {
            for &(u, ref er, v) in &proved_edge_set {
                if er == r && u < n_elems && v < n_elems {
                    if v == ub && u != ua {
                        diff.insert(pair_key(u, ua));
                    }
                    if u == ua && v != ub {
                        diff.insert(pair_key(v, ub));
                    }
                }
            }
        }
        if !irrefl_roles.is_empty() || !asym_roles.is_empty() {
            for &(u, ref r, v) in &proved_edge_set {
                if u < n_elems && v < n_elems && u != v && (irrefl_roles.contains(r) || asym_roles.contains(r)) {
                    diff.insert(pair_key(u, v));
                }
            }
        }
        if !disjoint_role_groups.is_empty() {
            let mut edges_by_role: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
            for &(u, ref r, v) in &proved_edge_set {
                if u < n_elems && v < n_elems {
                    edges_by_role.entry(r.as_str()).or_default().push((u, v));
                }
            }
            for grp in &disjoint_role_groups {
                for i in 0..grp.len() {
                    for j in (i + 1)..grp.len() {
                        let e1 = edges_by_role
                            .get(grp[i].as_str())
                            .map(Vec::as_slice)
                            .unwrap_or(&[]);
                        let e2 = edges_by_role
                            .get(grp[j].as_str())
                            .map(Vec::as_slice)
                            .unwrap_or(&[]);
                        // Merging the two named ends that keep the edges
                        // `p(u1, v1)` and `q(u2, v2)` apart would make them
                        // one edge of two disjoint properties. A loop at `x`
                        // with an edge from or to `y` keeps `x` and `y` apart.
                        for &(u1, v1) in e1 {
                            for &(u2, v2) in e2 {
                                if u1 == u2 && v1 != v2 {
                                    diff.insert(pair_key(v1, v2));
                                }
                                if v1 == v2 && u1 != u2 {
                                    diff.insert(pair_key(u1, u2));
                                }
                                if u1 == v2 && v1 == u2 && u1 != v1 {
                                    diff.insert(pair_key(u1, v1));
                                }
                                for ((x, loop_x), (a, b)) in [((u1, v1), (u2, v2)), ((u2, v2), (u1, v1))] {
                                    if x != loop_x {
                                        continue;
                                    }
                                    if a == x && b != x {
                                        diff.insert(pair_key(x, b));
                                    }
                                    if b == x && a != x {
                                        diff.insert(pair_key(x, a));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // (D4) Functional data properties on closed source `DataPropertyAssertion`s
        let mut func_data_conflict_pairs: HashSet<(usize, usize)> = HashSet::new();
        if !func_data_props.is_empty() && !closed_data_assertions.is_empty() {
            let mut by_prop: HashMap<&str, Vec<(usize, &str)>> = HashMap::new();
            for (u, p, lit) in &closed_data_assertions {
                if func_data_props.contains(p.as_str()) {
                    by_prop.entry(p.as_str()).or_default().push((*u, lit.as_str()));
                }
            }
            for list in by_prop.values() {
                for i in 0..list.len() {
                    for j in (i + 1)..list.len() {
                        let (u1, l1) = list[i];
                        let (u2, l2) = list[j];
                        if u1 != u2 && l1 != l2 {
                            let k1 = format!("__dt__val__{l1}");
                            let k2 = format!("__dt__val__{l2}");
                            match crate::frontend::datatypes::bridge_exact_value_equal(&k1, &k2) {
                                Some(false) => {
                                    diff.insert(pair_key(u1, u2));
                                    func_data_conflict_pairs.insert(pair_key(u1, u2));
                                }
                                None => {
                                    func_data_conflict_pairs.insert(pair_key(u1, u2));
                                }
                                Some(true) => {}
                            }
                        }
                    }
                }
            }
        }

        // (D5) Fixpoint propagation under functional and inverse-functional object properties
        if (!func_obj_roles.is_empty() || !inv_func_obj_roles.is_empty()) && !diff.is_empty() {
            let mut func_edges: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
            let mut inv_func_edges: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
            for &(u, ref r, v) in &proved_edge_set {
                if u < n_elems && v < n_elems {
                    if func_obj_roles.contains(r.as_str()) {
                        func_edges.entry(r.as_str()).or_default().push((u, v));
                    }
                    if inv_func_obj_roles.contains(r.as_str()) {
                        inv_func_edges.entry(r.as_str()).or_default().push((u, v));
                    }
                }
            }
            loop {
                let before = diff.len();
                for list in func_edges.values() {
                    for i in 0..list.len() {
                        for j in (i + 1)..list.len() {
                            let (u1, x1) = list[i];
                            let (u2, x2) = list[j];
                            if u1 != u2 && x1 != x2 && diff.contains(&pair_key(x1, x2)) {
                                diff.insert(pair_key(u1, u2));
                            }
                        }
                    }
                }
                for list in inv_func_edges.values() {
                    for i in 0..list.len() {
                        for j in (i + 1)..list.len() {
                            let (x1, u1) = list[i];
                            let (x2, u2) = list[j];
                            if u1 != u2 && x1 != x2 && diff.contains(&pair_key(x1, x2)) {
                                diff.insert(pair_key(u1, u2));
                            }
                        }
                    }
                }
                if diff.len() == before {
                    break;
                }
            }
        }

        // Now test every remaining pair `(u, v)` (`u < v` in `ind_elems`):
        // - If merging `u` and `v` in the full model `M_0` (`elem_classes`, `edge_set`)
        //   saturates without a clash and satisfies all clauses/cardinalities of `O`,
        //   `M_0 / (u = v)` is a verified model of `O ∪ {a = b}`, proving `O ⊭ a ≠ b`!
        // - If merging `u` and `v` in the minimal entailed Horn graph `H_0`
        //   (`entailed_elem_classes`, `proved_edge_set`) derives a deterministic Horn
        //   clash (`⊥`), then `O ∪ {a = b} ⊨ ⊥` in all models, proving `O ⊨ a ≠ b`!
        // - Every other pair goes into `plan.residual_different_pairs` for the exact
        //   probe test (`P_a ⊑ ¬{b}`)!
        let refl_set: HashSet<&str> = refl_roles.iter().map(String::as_str).collect();
        let mut has_non_refl_edge = vec![false; n_total_elems];
        for &(u, ref r, v) in &edge_set {
            if u != v || !refl_set.contains(r.as_str()) {
                has_non_refl_edge[u] = true;
                has_non_refl_edge[v] = true;
            }
        }
        for &(_, ua, ub) in &neg_role_assertions {
            has_non_refl_edge[ua] = true;
            has_non_refl_edge[ub] = true;
        }
        for hv in &has_value_rules {
            if hv.target_elem < n_total_elems {
                has_non_refl_edge[hv.target_elem] = true;
            }
        }
        for cr in &concept_rules {
            if let Some(u_o) = cr.nom_merge {
                if u_o < n_total_elems {
                    has_non_refl_edge[u_o] = true;
                }
            }
        }

        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        enum PairVerdict {
            NotDifferent,
            HornClash,
            Undecided,
        }

        // Individuals with an asserted value of a data property that a
        // functional or at-most clause restricts. Neither structure carries
        // the asserted literal as a valued data successor (the model's data
        // elements carry no literal class on the routes that rewrite data
        // assertions as classes), so a merge that joins such an individual
        // with a different value of that property looked clash-free and the
        // plan published "not different" without a probe: `Functional(d0)`,
        // `d0(a3, 1)`, `(d0 value 2)(a5)` lost `DIFFERENT a3 a5`, and
        // `A ⊑ ≤1 d1`, `A(a0)`, `d1(a3, 2)`, `d1(a3, 3)` lost `DIFFERENT a0 a3`.
        // A merge that touches one of them is not decided here; the exact
        // residual probe decides it.
        // Clause roles and source property tokens use different spellings
        // (short frontend names, full IRIs); accept a match in any of them.
        let mut restricted_data_roles: HashSet<String> = func_data_props.clone();
        for qf in &qual_func_rules {
            restricted_data_roles.insert(qf.role.clone());
            if let Some(spelled) = f_res.iri_map.get(&qf.role) {
                restricted_data_roles.insert(spelled.clone());
                restricted_data_roles.insert(expand_tok(spelled));
            }
        }
        let mut restricted_data_elem = vec![false; n_elems];
        for (u, p, _) in &closed_data_assertions {
            let short = resolve_role_short(p);
            let restricted = restricted_data_roles.contains(p)
                || restricted_data_roles.contains(&short)
                || full_to_short.get(p.as_str()).is_some_and(|s| restricted_data_roles.contains(*s))
                || meta.iri_map.get(p).is_some_and(|s| restricted_data_roles.contains(s));
            if *u < n_elems && restricted {
                restricted_data_elem[*u] = true;
            }
        }
        if std::env::var_os("KM_DIFF_TRACE").is_some() {
            eprintln!(
                "KM_DIFF_TRACE restricted data roles {restricted_data_roles:?} closed {closed_data_assertions:?} elements {:?}",
                (0..n_elems).filter(|&u| restricted_data_elem[u]).collect::<Vec<_>>()
            );
        }

        let clash_trace = std::env::var_os("KM_DIFF_TRACE").is_some();
        macro_rules! horn_clash {
            () => {{
                if clash_trace {
                    eprintln!("KM_DIFF_TRACE clash at abox_rows.rs:{}", line!());
                }
                PairVerdict::HornClash
            }};
        }
        let check_dt_val_clash = |c_set: &HashSet<String>, horn_only: bool| -> Option<PairVerdict> {
            let vals: Vec<&str> = c_set
                .iter()
                .map(String::as_str)
                .filter(|c| c.starts_with("__dt__val__"))
                .collect();
            if vals.len() >= 2 {
                for i in 0..vals.len() {
                    for j in (i + 1)..vals.len() {
                        match crate::frontend::datatypes::bridge_exact_value_equal(vals[i], vals[j])
                        {
                            Some(false) => return Some(horn_clash!()),
                            None if !horn_only => return Some(PairVerdict::Undecided),
                            _ => {}
                        }
                    }
                }
            }
            None
        };

        // Fast concept-only saturation for pure-concept individual elements `(u, v)`
        // that have no non-reflexive edges.
        let test_pure_concept_merge = |u: usize, v: usize, horn_only: bool| -> PairVerdict {
            let base = if horn_only {
                &entailed_elem_classes
            } else {
                &elem_classes
            };
            let mut merged: HashSet<String> = base[u]
                .iter()
                .chain(base[v].iter())
                .filter(|c| !c.starts_with("__nom__"))
                .cloned()
                .collect();
            for ind in elem_inds[u].iter().chain(elem_inds[v].iter()) {
                merged.insert(format!("__nom__{ind}"));
            }
            let neg_merged: HashSet<&str> = elem_neg_classes[u]
                .iter()
                .chain(elem_neg_classes[v].iter())
                .map(String::as_str)
                .collect();
            let mut work: Vec<String> = merged.iter().cloned().collect();
            for &idx in &empty_body_concept_rules {
                let cr = &concept_rules[idx];
                if cr.heads.is_empty() && cr.nom_merge.is_none() {
                    return horn_clash!();
                }
                if let Some(u_o) = cr.nom_merge {
                    if u_o != u && u_o != v {
                        return PairVerdict::Undecided;
                    }
                } else if cr.heads.len() == 1 {
                    let h = &cr.heads[0];
                    if merged.insert(h.clone()) {
                        work.push(h.clone());
                    }
                } else if !horn_only && !cr.heads.iter().any(|h| merged.contains(h)) {
                    return PairVerdict::Undecided;
                }
            }
            while let Some(c) = work.pop() {
                if let Some(sups) = subs_map.get(&c) {
                    for sup in sups {
                        if merged.insert(sup.clone()) {
                            work.push(sup.clone());
                        }
                    }
                }
                if let Some(indices) = concept_rules_by_trigger.get(&c) {
                    for &idx in indices {
                        let cr = &concept_rules[idx];
                        if cr.body.iter().all(|b| merged.contains(b)) {
                            if cr.heads.is_empty() && cr.nom_merge.is_none() {
                                return horn_clash!();
                            }
                            if let Some(u_o) = cr.nom_merge {
                                if u_o != u && u_o != v {
                                    return PairVerdict::Undecided;
                                }
                            } else if cr.heads.len() == 1 {
                                let h = &cr.heads[0];
                                if let Some(pub_i) = h.strip_prefix("__nom__") {
                                    if !elem_inds[u].iter().any(|x| x == pub_i)
                                        && !elem_inds[v].iter().any(|x| x == pub_i)
                                    {
                                        return PairVerdict::Undecided;
                                    }
                                }
                                if merged.insert(h.clone()) {
                                    work.push(h.clone());
                                }
                            } else if !horn_only && !cr.heads.iter().any(|h| merged.contains(h)) {
                                return PairVerdict::Undecided;
                            }
                        }
                    }
                }
            }
            for &nc in &neg_merged {
                if merged.contains(nc) {
                    return horn_clash!();
                }
            }
            if let Some(v_dt) = check_dt_val_clash(&merged, horn_only) {
                return v_dt;
            }
            for c in &merged {
                if let Some(indices) = hv_rules_by_trigger.get(c) {
                    for &idx in indices {
                        if has_value_rules[idx].body.iter().all(|b| merged.contains(b)) {
                            return PairVerdict::Undecided;
                        }
                    }
                }
                if let Some(indices) = skolem_by_trigger.get(c) {
                    for &idx in indices {
                        if skolem_vec[idx].1.body.iter().all(|b| merged.contains(b)) {
                            return PairVerdict::Undecided;
                        }
                    }
                }
            }
            if !empty_body_hv_rules.is_empty() || !empty_body_skolem.is_empty() {
                return PairVerdict::Undecided;
            }
            if !horn_only {
                let touches_blocked = raw
                    .blocked
                    .iter()
                    .any(|&(b, blk)| b == u || b == v || blk == u || blk == v);
                if has_unhandled_clause || touches_blocked {
                    return PairVerdict::Undecided;
                }
                for c in &merged {
                    if let Some(indices) = cards_by_marker.get(c) {
                        for &idx in indices {
                            let card = &f_res.cardinalities[idx];
                            if card.min && card.n >= 1 {
                                return PairVerdict::Undecided;
                            }
                        }
                    }
                }
            }
            if restricted_data_elem[u] || restricted_data_elem[v] {
                return PairVerdict::Undecided;
            }
            PairVerdict::NotDifferent
        };

        let mut adj_edges_m: Vec<Vec<(usize, String, usize)>> = vec![Vec::new(); n_total_elems];
        for e in &edge_set {
            adj_edges_m[e.0].push(e.clone());
            if e.2 != e.0 {
                adj_edges_m[e.2].push(e.clone());
            }
        }
        let mut adj_edges_h: Vec<Vec<(usize, String, usize)>> = vec![Vec::new(); n_total_elems];
        for e in &proved_edge_set {
            adj_edges_h[e.0].push(e.clone());
            if e.2 != e.0 {
                adj_edges_h[e.2].push(e.clone());
            }
        }
        let has_trans_or_chain_rbox = meta.rbox.iter().any(|row| row.len() >= 3);

        // Full quotient-graph saturation for edge-bearing pairs `(u_init, v_init)`
        let test_graph_merge = |u_init: usize,
                                v_init: usize,
                                horn_only: bool,
                                cur_diff: &HashSet<(usize, usize)>|
         -> PairVerdict {
            let mut uf: Vec<usize> = (0..n_total_elems).collect();
            fn find(uf: &mut [usize], mut x: usize) -> usize {
                while uf[x] != x {
                    uf[x] = uf[uf[x]];
                    x = uf[x];
                }
                x
            }
            let base_c = if horn_only {
                &entailed_elem_classes
            } else {
                &elem_classes
            };
            let base_e = if horn_only {
                &proved_edge_set
            } else {
                &edge_set
            };
            let base_adj = if horn_only {
                &adj_edges_h
            } else {
                &adj_edges_m
            };

            // Copy-on-write element concept sets: only modified elements are cloned
            let mut c_overrides: HashMap<usize, HashSet<String>> = HashMap::new();
            let mut dirty_elems: HashSet<usize> = HashSet::new();
            let mut all_dirty_elems: HashSet<usize> = HashSet::new();
            let mut extra_edges: HashSet<(usize, String, usize)> = HashSet::new();
            let mut full_e_set: Option<HashSet<(usize, String, usize)>> = None;

            let mut merge_queue: Vec<(usize, usize)> = vec![(u_init, v_init)];
            // Members of each union-find class with more than one element.
            let mut class_members: HashMap<usize, Vec<usize>> = HashMap::new();
            let mut elem_has_non_refl: Vec<bool> = has_non_refl_edge.clone();
            // Roots whose class contains an individual of `restricted_data_elem`.
            let mut restricted_roots: HashSet<usize> = HashSet::new();
            let mut merged_restricted_data = false;
            // The step bound only guards against a runaway loop. A merge that
            // has not reached its fixpoint within it proves nothing either way:
            // falling through used to return `NotDifferent` for an unsaturated
            // quotient, which silently dropped a `DIFFERENT` row. Such a pair
            // is now `Undecided` and goes to the exact residual probe.
            let mut saturated = false;
            for _step in 0..GRAPH_MERGE_MAX_STEPS {
                let mut any_merged = false;
                let mut need_rbox_reclose = false;
                while let Some((a, b)) = merge_queue.pop() {
                    let ra = find(&mut uf, a);
                    let rb = find(&mut uf, b);
                    if ra == rb {
                        continue;
                    }
                    let (keep, drop_el) = (ra.min(rb), ra.max(rb));
                    // The classes being joined, not just their roots, must be
                    // free of a proved difference: after `u = v` the root of
                    // `{u, v}` stands for both, and a later merge with `w`
                    // clashes when `w != v` is proved even if `w != u` is not
                    // (g8301_366: `a2 = a4`, then `≤ 1 r1` merges `a7` into
                    // the class, and `a7 != a2` is asserted).
                    let mk = class_members.remove(&keep).unwrap_or_else(|| vec![keep]);
                    let md = class_members.remove(&drop_el).unwrap_or_else(|| vec![drop_el]);
                    let proved_apart = mk.iter().filter(|&&x| x < n_elems).any(|&x| {
                        md.iter().filter(|&&y| y < n_elems).any(|&y| {
                            cur_diff.contains(&pair_key(x, y))
                                || func_data_conflict_pairs.contains(&pair_key(x, y))
                        })
                    });
                    let mut joined = mk;
                    joined.extend(md);
                    class_members.insert(keep, joined);
                    if proved_apart {
                        return if horn_only {
                            horn_clash!()
                        } else {
                            PairVerdict::Undecided
                        };
                    }
                    let nr_k = elem_has_non_refl[keep];
                    let nr_d = elem_has_non_refl[drop_el];
                    if nr_k && nr_d {
                        need_rbox_reclose = true;
                    } else if nr_k && !nr_d {
                        if base_adj[drop_el]
                            .iter()
                            .any(|(_, r, _)| !base_e.contains(&(keep, r.clone(), keep)))
                        {
                            need_rbox_reclose = true;
                        }
                    } else if !nr_k && nr_d {
                        if base_adj[keep]
                            .iter()
                            .any(|(_, r, _)| !base_e.contains(&(drop_el, r.clone(), drop_el)))
                        {
                            need_rbox_reclose = true;
                        }
                        elem_has_non_refl[keep] = true;
                    } else if base_adj[drop_el]
                        .iter()
                        .any(|(_, r, _)| !base_e.contains(&(keep, r.clone(), keep)))
                        && base_adj[keep]
                            .iter()
                            .any(|(_, r, _)| !base_e.contains(&(drop_el, r.clone(), drop_el)))
                    {
                        need_rbox_reclose = true;
                    }
                    let restricted = |x: usize, roots: &HashSet<usize>| {
                        (x < n_elems && restricted_data_elem[x]) || roots.contains(&x)
                    };
                    if restricted(keep, &restricted_roots) || restricted(drop_el, &restricted_roots) {
                        merged_restricted_data = true;
                        restricted_roots.insert(keep);
                    }
                    uf[drop_el] = keep;
                    let drop_c: HashSet<String> = c_overrides
                        .remove(&drop_el)
                        .unwrap_or_else(|| base_c[drop_el].clone());
                    let keep_set = c_overrides
                        .entry(keep)
                        .or_insert_with(|| base_c[keep].clone());
                    keep_set.extend(drop_c);
                    dirty_elems.insert(keep);
                    all_dirty_elems.insert(keep);
                    all_dirty_elems.insert(drop_el);
                    for &(s, _, t) in &base_adj[drop_el] {
                        all_dirty_elems.insert(s);
                        all_dirty_elems.insert(t);
                    }
                    for &(s, _, t) in &base_adj[keep] {
                        all_dirty_elems.insert(s);
                        all_dirty_elems.insert(t);
                    }
                    any_merged = true;
                }

                // Collect active edges touching dirty elements (or full e_set if RBox chain/new edges require it)
                if (need_rbox_reclose && has_trans_or_chain_rbox)
                    || (any_merged && full_e_set.is_some())
                {
                    let mut remapped: HashSet<(usize, String, usize)> =
                        HashSet::with_capacity(base_e.len() + extra_edges.len());
                    let src_iter = full_e_set.as_ref().unwrap_or(base_e);
                    for (s, r, t) in src_iter.iter().chain(extra_edges.iter()) {
                        remapped.insert((find(&mut uf, *s), r.clone(), find(&mut uf, *t)));
                    }
                    if crate::engine::close_edges_under_rbox_rows(
                        &meta.rbox,
                        n_total_elems,
                        &mut remapped,
                    )
                    .is_err()
                    {
                        return PairVerdict::Undecided;
                    }
                    full_e_set = Some(remapped);
                }

                let mut active_edges: Vec<(usize, String, usize)> = Vec::new();
                if let Some(ref fe) = full_e_set {
                    for &(s, ref r, t) in fe {
                        if all_dirty_elems.contains(&s) || all_dirty_elems.contains(&t) {
                            active_edges.push((s, r.clone(), t));
                        }
                    }
                } else {
                    let mut seen_e: HashSet<(usize, String, usize)> = HashSet::new();
                    for &d in &all_dirty_elems {
                        for &(s, ref r, t) in &base_adj[d] {
                            let edge = (find(&mut uf, s), r.clone(), find(&mut uf, t));
                            if seen_e.insert(edge.clone()) {
                                active_edges.push(edge);
                            }
                        }
                    }
                    for (s, r, t) in &extra_edges {
                        let edge = (find(&mut uf, *s), r.clone(), find(&mut uf, *t));
                        if seen_e.insert(edge.clone()) {
                            active_edges.push(edge);
                        }
                    }
                }

                let edge_exists = |s: usize, r: &str, t: usize,
                                   fe: &Option<HashSet<(usize, String, usize)>>,
                                   ae: &[(usize, String, usize)]|
                 -> bool {
                    if let Some(ref set) = fe {
                        set.contains(&(s, r.to_string(), t))
                    } else {
                        ae.iter().any(|(es, er, et)| *es == s && er == r && *et == t)
                            || base_e.contains(&(s, r.to_string(), t))
                    }
                };

                // Check negative role assertions, irreflexive/asymmetric/disjoint roles
                for &(ref r, ua, ub) in &neg_role_assertions {
                    let rua = find(&mut uf, ua);
                    let rub = find(&mut uf, ub);
                    if edge_exists(rua, r, rub, &full_e_set, &active_edges) {
                        return horn_clash!();
                    }
                }
                for &(s, ref r, t) in &active_edges {
                    if s == t && (irrefl_roles.contains(r) || asym_roles.contains(r)) {
                        return horn_clash!();
                    }
                    if s != t
                        && asym_roles.contains(r)
                        && edge_exists(t, r, s, &full_e_set, &active_edges)
                    {
                        return horn_clash!();
                    }
                }
                for grp in &disjoint_role_groups {
                    for i in 0..grp.len() {
                        for j in (i + 1)..grp.len() {
                            for &(s, ref r, t) in &active_edges {
                                if r == &grp[i]
                                    && edge_exists(s, &grp[j], t, &full_e_set, &active_edges)
                                {
                                    return horn_clash!();
                                }
                            }
                        }
                    }
                }

                let mut changed = false;
                let dirty_snap: Vec<usize> = dirty_elems
                    .drain()
                    .map(|z| find(&mut uf, z))
                    .collect();
                for z in dirty_snap {
                    if uf[z] != z {
                        continue;
                    }
                    let z_set = c_overrides
                        .entry(z)
                        .or_insert_with(|| base_c[z].clone());
                    let mut st: Vec<String> = z_set.iter().cloned().collect();
                    while let Some(c) = st.pop() {
                        if let Some(sups) = subs_map.get(&c) {
                            for sup in sups {
                                if z_set.insert(sup.clone()) {
                                    st.push(sup.clone());
                                    changed = true;
                                }
                            }
                        }
                        if let Some(indices) = concept_rules_by_trigger.get(&c) {
                            for &idx in indices {
                                let cr = &concept_rules[idx];
                                if cr.body.iter().all(|b| z_set.contains(b)) {
                                    if cr.heads.is_empty() && cr.nom_merge.is_none() {
                                        if clash_trace {
                                            let mut labels: Vec<_> = z_set.iter().collect();
                                            labels.sort();
                                            eprintln!("KM_DIFF_TRACE concept rule {:?} closes element {} {:?}", cr.body, z, labels);
                                        }
                                        return horn_clash!();
                                    }
                                    if let Some(u_o) = cr.nom_merge {
                                        let ro = find(&mut uf, u_o);
                                        if ro != z {
                                            merge_queue.push((z, ro));
                                            changed = true;
                                        }
                                    } else if cr.heads.len() == 1 {
                                        let h = &cr.heads[0];
                                        if let Some(pub_i) = h.strip_prefix("__nom__") {
                                            if let Some(&u_o) = ind_to_elem.get(pub_i) {
                                                let ro = find(&mut uf, u_o);
                                                if ro != z {
                                                    merge_queue.push((z, ro));
                                                    changed = true;
                                                }
                                            }
                                        }
                                        if z_set.insert(h.clone()) {
                                            st.push(h.clone());
                                            changed = true;
                                        }
                                    } else if !horn_only
                                        && !cr.heads.iter().any(|h| z_set.contains(h))
                                    {
                                        return PairVerdict::Undecided;
                                    }
                                }
                            }
                        }
                    }
                    if let Some(v_dt) = check_dt_val_clash(z_set, horn_only) {
                        return v_dt;
                    }
                    for orig in 0..n_elems {
                        if find(&mut uf, orig) == z {
                            for nc in &elem_neg_classes[orig] {
                                if z_set.contains(nc) {
                                    return horn_clash!();
                                }
                            }
                        }
                    }
                    let z_concepts: Vec<String> = z_set.iter().cloned().collect();
                    for c in &z_concepts {
                        if singleton_concepts.contains(c) {
                            for other in 0..n_total_elems {
                                let ro = find(&mut uf, other);
                                if ro != z {
                                    let has_c = c_overrides
                                        .get(&ro)
                                        .unwrap_or(&base_c[ro])
                                        .contains(c);
                                    if has_c {
                                        merge_queue.push((z, ro));
                                        changed = true;
                                    }
                                }
                            }
                        }
                        if let Some(indices) = hv_rules_by_trigger.get(c) {
                            let z_cur = c_overrides.get(&z).unwrap_or(&base_c[z]);
                            for &idx in indices {
                                let hv = &has_value_rules[idx];
                                if hv.target_elem < n_total_elems
                                    && hv.body.iter().all(|b| z_cur.contains(b))
                                {
                                    let rt = find(&mut uf, hv.target_elem);
                                    let edge = if hv.inv {
                                        (rt, hv.role.clone(), z)
                                    } else {
                                        (z, hv.role.clone(), rt)
                                    };
                                    if extra_edges.insert(edge.clone()) {
                                        active_edges.push(edge);
                                        all_dirty_elems.insert(rt);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }

                // Role rules over active edges
                for i_edge in 0..active_edges.len() {
                    let (u, ref r, v) = active_edges[i_edge].clone();
                    let Some(indices) = role_rules_by_role.get(r) else {
                        continue;
                    };
                    for &idx in indices {
                        let rr = &role_rules[idx];
                        if rr.self_only && u != v {
                            continue;
                        }
                        let u_has_body = {
                            let u_set = c_overrides.get(&u).unwrap_or(&base_c[u]);
                            rr.body_x.iter().all(|b| u_set.contains(b))
                        };
                        if !u_has_body {
                            continue;
                        }
                        let v_has_body = {
                            let v_set = c_overrides.get(&v).unwrap_or(&base_c[v]);
                            rr.body_y.iter().all(|b| v_set.contains(b))
                        };
                        if !v_has_body {
                            continue;
                        }
                        match &rr.action {
                            RoleHeadAction::Clash => return horn_clash!(),
                            RoleHeadAction::AddX(d) => {
                                if let Some(pub_i) = d.strip_prefix("__nom__") {
                                    if let Some(&u_o) = ind_to_elem.get(pub_i) {
                                        let ro = find(&mut uf, u_o);
                                        if ro != u {
                                            merge_queue.push((u, ro));
                                            changed = true;
                                        }
                                    }
                                }
                                let u_set = c_overrides
                                    .entry(u)
                                    .or_insert_with(|| base_c[u].clone());
                                if u_set.insert(d.clone()) {
                                    dirty_elems.insert(u);
                                    all_dirty_elems.insert(u);
                                    changed = true;
                                }
                            }
                            RoleHeadAction::AddY(d) => {
                                if let Some(pub_i) = d.strip_prefix("__nom__") {
                                    if let Some(&u_o) = ind_to_elem.get(pub_i) {
                                        let ro = find(&mut uf, u_o);
                                        if ro != v {
                                            merge_queue.push((v, ro));
                                            changed = true;
                                        }
                                    }
                                }
                                let v_set = c_overrides
                                    .entry(v)
                                    .or_insert_with(|| base_c[v].clone());
                                if v_set.insert(d.clone()) {
                                    dirty_elems.insert(v);
                                    all_dirty_elems.insert(v);
                                    changed = true;
                                }
                            }
                            RoleHeadAction::AddRole(s, inv) => {
                                let edge = if *inv {
                                    (v, s.clone(), u)
                                } else {
                                    (u, s.clone(), v)
                                };
                                if extra_edges.insert(edge) {
                                    changed = true;
                                }
                            }
                            RoleHeadAction::MergeXY => {
                                if u != v {
                                    merge_queue.push((u, v));
                                    changed = true;
                                }
                            }
                            RoleHeadAction::MergeXElem(u_o) => {
                                let ro = find(&mut uf, *u_o);
                                if u != ro {
                                    merge_queue.push((u, ro));
                                    changed = true;
                                }
                            }
                            RoleHeadAction::MergeYElem(u_o) => {
                                let ro = find(&mut uf, *u_o);
                                if v != ro {
                                    merge_queue.push((v, ro));
                                    changed = true;
                                }
                            }
                            RoleHeadAction::Disj(disj) => {
                                if !horn_only {
                                    let u_set = c_overrides.get(&u).unwrap_or(&base_c[u]);
                                    let v_set = c_overrides.get(&v).unwrap_or(&base_c[v]);
                                    if !disj.iter().any(|(is_y, c)| {
                                        if *is_y {
                                            v_set.contains(c)
                                        } else {
                                            u_set.contains(c)
                                        }
                                    }) {
                                        return PairVerdict::Undecided;
                                    }
                                }
                            }
                        }
                    }
                }

                // Functionality / InverseFunctionality / Qualified At-Most-N on active edges
                for r_func in &func_obj_roles {
                    let mut by_src: HashMap<usize, Vec<usize>> = HashMap::new();
                    for &(s, ref r, t) in &active_edges {
                        if r == r_func {
                            by_src.entry(s).or_default().push(t);
                        }
                    }
                    for tgts in by_src.values() {
                        for w in tgts.windows(2) {
                            if w[0] != w[1] {
                                merge_queue.push((w[0], w[1]));
                                changed = true;
                            }
                        }
                    }
                }
                for r_ifunc in &inv_func_obj_roles {
                    let mut by_tgt: HashMap<usize, Vec<usize>> = HashMap::new();
                    for &(s, ref r, t) in &active_edges {
                        if r == r_ifunc {
                            by_tgt.entry(t).or_default().push(s);
                        }
                    }
                    for srcs in by_tgt.values() {
                        for w in srcs.windows(2) {
                            if w[0] != w[1] {
                                merge_queue.push((w[0], w[1]));
                                changed = true;
                            }
                        }
                    }
                }
                for qf in &qual_func_rules {
                    for &z_raw in &all_dirty_elems {
                        let z = find(&mut uf, z_raw);
                        if uf[z] != z {
                            continue;
                        }
                        let z_set = c_overrides.get(&z).unwrap_or(&base_c[z]);
                        if !qf.body_x.iter().all(|b| z_set.contains(b)) {
                            continue;
                        }
                        let mut matches: Vec<usize> = active_edges
                            .iter()
                            .filter_map(|(s, r, t)| {
                                if r != &qf.role {
                                    return None;
                                }
                                let other = if qf.inv {
                                    if *t == z { Some(*s) } else { None }
                                } else if *s == z {
                                    Some(*t)
                                } else {
                                    None
                                }?;
                                let o_set = c_overrides.get(&other).unwrap_or(&base_c[other]);
                                qf.body_y.iter().all(|b| o_set.contains(b)).then_some(other)
                            })
                            .collect();
                        matches.sort_unstable();
                        matches.dedup();
                        if matches.len() > qf.max_n {
                            if qf.max_n == 1 {
                                for w in matches.windows(2) {
                                    merge_queue.push((w[0], w[1]));
                                    changed = true;
                                }
                            } else if !horn_only {
                                return PairVerdict::Undecided;
                            } else {
                                let all_pairwise_diff = (0..matches.len()).all(|i| {
                                    ((i + 1)..matches.len()).all(|j| {
                                        let a = matches[i];
                                        let b = matches[j];
                                        a < n_elems
                                            && b < n_elems
                                            && cur_diff.contains(&pair_key(a, b))
                                    })
                                });
                                if all_pairwise_diff {
                                    return horn_clash!();
                                }
                            }
                        }
                    }
                }

                // Check Skolem inequality clashes `[M(x), f1(x) = f2(x)] -> []`
                if !skolem_ineqs.is_empty() {
                    for &z_raw in &all_dirty_elems {
                        let z = find(&mut uf, z_raw);
                        let z_set = c_overrides.get(&z).unwrap_or(&base_c[z]);
                        for (b_cons, f1, f2) in &skolem_ineqs {
                            if b_cons.iter().all(|b| z_set.contains(b)) {
                                for orig in 0..n_elems {
                                    if find(&mut uf, orig) == z {
                                        if let (Some(&w1), Some(&w2)) = (
                                            skolem_witness_of.get(&(orig, f1.clone())),
                                            skolem_witness_of.get(&(orig, f2.clone())),
                                        ) {
                                            if find(&mut uf, w1) == find(&mut uf, w2) {
                                                return if horn_only {
                                                    horn_clash!()
                                                } else {
                                                    PairVerdict::Undecided
                                                };
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                if !merge_queue.is_empty() {
                    continue;
                }
                if changed && (!extra_edges.is_empty() || full_e_set.is_some()) {
                    let mut remapped: HashSet<(usize, String, usize)> =
                        HashSet::with_capacity(base_e.len() + extra_edges.len());
                    let src_iter = full_e_set.as_ref().unwrap_or(base_e);
                    for (s, r, t) in src_iter.iter().chain(extra_edges.iter()) {
                        remapped.insert((find(&mut uf, *s), r.clone(), find(&mut uf, *t)));
                    }
                    if crate::engine::close_edges_under_rbox_rows(
                        &meta.rbox,
                        n_total_elems,
                        &mut remapped,
                    )
                    .is_err()
                    {
                        return PairVerdict::Undecided;
                    }
                    full_e_set = Some(remapped);
                } else if !changed {
                    saturated = true;
                    break;
                }
            }
            if !saturated {
                return PairVerdict::Undecided;
            }

            if !horn_only {
                let touches_blocked = raw.blocked.iter().any(|&(b, blk)| {
                    (b < n_elems && all_dirty_elems.contains(&b))
                        || (blk < n_elems && all_dirty_elems.contains(&blk))
                });
                if has_unhandled_clause || touches_blocked {
                    return PairVerdict::Undecided;
                }
                let mut active_edges: Vec<(usize, String, usize)> = Vec::new();
                if let Some(ref fe) = full_e_set {
                    for &(s, ref r, t) in fe {
                        if all_dirty_elems.contains(&s) || all_dirty_elems.contains(&t) {
                            active_edges.push((s, r.clone(), t));
                        }
                    }
                } else {
                    let mut seen_e: HashSet<(usize, String, usize)> = HashSet::new();
                    for &d in &all_dirty_elems {
                        for &(s, ref r, t) in &base_adj[d] {
                            let edge = (find(&mut uf, s), r.clone(), find(&mut uf, t));
                            if seen_e.insert(edge.clone()) {
                                active_edges.push(edge);
                            }
                        }
                    }
                    for (s, r, t) in &extra_edges {
                        let edge = (find(&mut uf, *s), r.clone(), find(&mut uf, *t));
                        if seen_e.insert(edge.clone()) {
                            active_edges.push(edge);
                        }
                    }
                }

                // Check Skolem existential requirements and cardinality bounds on dirty elements
                let mut checked_z: HashSet<usize> = HashSet::new();
                for &z_raw in &all_dirty_elems {
                    let z = find(&mut uf, z_raw);
                    if !checked_z.insert(z) {
                        continue;
                    }
                    let z_set = c_overrides.get(&z).unwrap_or(&base_c[z]);
                    for c in z_set {
                        if let Some(indices) = skolem_by_trigger.get(c) {
                            for &idx in indices {
                                let grp = &skolem_vec[idx].1;
                                if grp.body.iter().all(|b| z_set.contains(b)) {
                                    let Some((ref r_short, inv)) = grp.role else {
                                        return PairVerdict::Undecided;
                                    };
                                    let witnessed = active_edges.iter().any(|(s, r, t)| {
                                        r == r_short
                                            && if inv { *t == z } else { *s == z }
                                            && grp.fillers.iter().all(|f| {
                                                let target = if inv { *s } else { *t };
                                                let t_set = c_overrides
                                                    .get(&target)
                                                    .unwrap_or(&base_c[target]);
                                                t_set.contains(f)
                                            })
                                    });
                                    if !witnessed {
                                        return PairVerdict::Undecided;
                                    }
                                }
                            }
                        }
                        if let Some(indices) = cards_by_marker.get(c) {
                            for &idx in indices {
                                let card = &f_res.cardinalities[idx];
                                let (r_short, inv) = canon_role(&card.role);
                                let f_c = canon_concept(&card.filler);
                                let mut targets: Vec<usize> = active_edges
                                    .iter()
                                    .filter_map(|(s, r, t)| {
                                        if r != &r_short {
                                            return None;
                                        }
                                        let other = if inv {
                                            if *t == z { Some(*s) } else { None }
                                        } else if *s == z {
                                            Some(*t)
                                        } else {
                                            None
                                        }?;
                                        let o_set =
                                            c_overrides.get(&other).unwrap_or(&base_c[other]);
                                        (f_c == "owl:Thing" || o_set.contains(&f_c))
                                            .then_some(other)
                                    })
                                    .collect();
                                targets.sort_unstable();
                                targets.dedup();
                                if card.min && targets.len() < card.n as usize {
                                    return PairVerdict::Undecided;
                                }
                                if !card.min && targets.len() > card.n as usize {
                                    return PairVerdict::Undecided;
                                }
                            }
                        }
                    }
                }
            }
            if merged_restricted_data {
                return PairVerdict::Undecided;
            }
            PairVerdict::NotDifferent
        };

        // Memoize pure-concept and graph pair evaluations by element signature
        let mut pure_sig_id: Vec<Option<usize>> = vec![None; n_elems];
        let mut sig_to_id: HashMap<(Vec<String>, Vec<String>, Vec<String>, Vec<String>), usize> =
            HashMap::new();
        let mut special_ind: Vec<bool> = vec![false; n_elems];
        for &(_, ua, ub) in &neg_role_assertions {
            if ua < n_elems {
                special_ind[ua] = true;
            }
            if ub < n_elems {
                special_ind[ub] = true;
            }
        }
        for hv in &has_value_rules {
            if hv.target_elem < n_elems {
                special_ind[hv.target_elem] = true;
            }
        }
        for cr in &concept_rules {
            if let Some(u_o) = cr.nom_merge {
                if u_o < n_elems {
                    special_ind[u_o] = true;
                }
            }
        }
        type GraphSigKey = (
            Option<usize>,
            Vec<String>,
            Vec<String>,
            Vec<String>,
            Vec<(String, bool, usize)>,
            Vec<(String, bool, usize)>,
            Vec<(String, bool, Vec<String>, Vec<String>)>,
            Vec<(String, bool, Vec<String>)>,
        );
        let mut graph_sig_id: Vec<Option<usize>> = vec![None; n_elems];
        let mut graph_sig_to_id: HashMap<GraphSigKey, usize> = HashMap::new();
        for u in 0..n_elems {
            if restricted_data_elem[u] {
                special_ind[u] = true;
            }
        }
        for &u in &ind_elems {
            let mut m_c: Vec<String> = elem_classes[u]
                .iter()
                .filter(|c| !c.starts_with("__nom__"))
                .cloned()
                .collect();
            m_c.sort();
            let mut h_c: Vec<String> = entailed_elem_classes[u]
                .iter()
                .filter(|c| !c.starts_with("__nom__"))
                .cloned()
                .collect();
            h_c.sort();
            let mut n_c: Vec<String> = elem_neg_classes[u].iter().cloned().collect();
            n_c.sort();
            if !has_non_refl_edge[u] && !restricted_data_elem[u] {
                let key = (m_c.clone(), h_c.clone(), n_c.clone(), Vec::new());
                let next_id = sig_to_id.len();
                let id = *sig_to_id.entry(key).or_insert(next_id);
                pure_sig_id[u] = Some(id);
            }
            if skolem_ineqs.is_empty() {
                let mut m_ind_e = Vec::new();
                let mut m_sk_e = Vec::new();
                let mut can_memo = true;
                for &(s, ref r, t) in &adj_edges_m[u] {
                    let (is_out, other) = if s == u { (true, t) } else { (false, s) };
                    if other < n_elems {
                        m_ind_e.push((
                            r.clone(),
                            is_out,
                            if other == u { usize::MAX } else { other },
                        ));
                    } else if adj_edges_m[other]
                        .iter()
                        .all(|&(es, _, et)| (es == u || es == other) && (et == u || et == other))
                    {
                        let mut oc_m: Vec<String> = elem_classes[other].iter().cloned().collect();
                        oc_m.sort();
                        let mut oc_h: Vec<String> =
                            entailed_elem_classes[other].iter().cloned().collect();
                        oc_h.sort();
                        m_sk_e.push((r.clone(), is_out, oc_m, oc_h));
                    } else {
                        can_memo = false;
                        break;
                    }
                }
                if can_memo {
                    m_ind_e.sort();
                    m_sk_e.sort();
                    let mut h_ind_e = Vec::new();
                    let mut h_sk_e = Vec::new();
                    for &(s, ref r, t) in &adj_edges_h[u] {
                        let (is_out, other) = if s == u { (true, t) } else { (false, s) };
                        if other < n_elems {
                            h_ind_e.push((
                                r.clone(),
                                is_out,
                                if other == u { usize::MAX } else { other },
                            ));
                        } else {
                            let mut oc_h: Vec<String> =
                                entailed_elem_classes[other].iter().cloned().collect();
                            oc_h.sort();
                            h_sk_e.push((r.clone(), is_out, oc_h));
                        }
                    }
                    h_ind_e.sort();
                    h_sk_e.sort();
                    let gkey = (
                        special_ind[u].then_some(u),
                        m_c,
                        h_c,
                        n_c,
                        m_ind_e,
                        h_ind_e,
                        m_sk_e,
                        h_sk_e,
                    );
                    let next_gid = graph_sig_to_id.len();
                    let gid = *graph_sig_to_id.entry(gkey).or_insert(next_gid);
                    graph_sig_id[u] = Some(gid);
                }
            }
        }
        let mut pure_memo: HashMap<(usize, usize), (PairVerdict, PairVerdict)> = HashMap::new();
        let mut graph_memo: HashMap<(usize, usize), (PairVerdict, PairVerdict)> = HashMap::new();
        let mut mixed_memo: HashMap<(usize, usize, bool), (PairVerdict, PairVerdict)> =
            HashMap::new();
        let base_diff = diff.clone();
        let diff_trace = std::env::var_os("KM_DIFF_TRACE").is_some();
        if diff_trace {
            for &u in &ind_elems {
                let mut m: Vec<&String> = elem_classes[u].iter().collect();
                m.sort();
                let mut h: Vec<&String> = entailed_elem_classes[u].iter().collect();
                h.sort();
                let mut n: Vec<&String> = elem_neg_classes[u].iter().collect();
                n.sort();
                eprintln!("KM_DIFF_TRACE elem {u} {:?}\n  model={m:?}\n  horn={h:?}\n  neg={n:?}", elem_inds[u]);
            }
            let mut es: Vec<_> = edge_set.iter().collect();
            es.sort();
            eprintln!("KM_DIFF_TRACE model edges {es:?}");
            let mut ps: Vec<_> = proved_edge_set.iter().collect();
            ps.sort();
            eprintln!("KM_DIFF_TRACE horn edges {ps:?}");
            let mut d: Vec<_> = diff.iter().collect();
            d.sort();
            eprintln!("KM_DIFF_TRACE pre-loop diff {d:?}");
            for (i, rr) in role_rules.iter().enumerate() {
                eprintln!("KM_DIFF_TRACE role_rule {i}: role={} x={:?} y={:?} self={} action={:?}", rr.role, rr.body_x, rr.body_y, rr.self_only, rr.action);
            }
            for (i, qf) in qual_func_rules.iter().enumerate() {
                eprintln!("KM_DIFF_TRACE qual_func {i}: role={} inv={} x={:?} y={:?} max={}", qf.role, qf.inv, qf.body_x, qf.body_y, qf.max_n);
            }
            eprintln!("KM_DIFF_TRACE skolem_ineqs {:?}", skolem_ineqs);
            eprintln!("KM_DIFF_TRACE skolem_witness_of {:?}", skolem_witness_of);
            eprintln!("KM_DIFF_TRACE func {:?} invfunc {:?}", func_obj_roles, inv_func_obj_roles);
            for (i, cr) in concept_rules.iter().enumerate() {
                eprintln!("KM_DIFF_TRACE concept_rule {i}: {:?} -> {:?} nom={:?}", cr.body, cr.heads, cr.nom_merge);
            }
        }
        if std::env::var_os("KM_TIMING").is_some() {
            let n_pure = ind_elems.iter().filter(|&&u| pure_sig_id[u].is_some()).count();
            let n_graph = ind_elems.iter().filter(|&&u| graph_sig_id[u].is_some()).count();
            eprintln!(
                "KM_TIMING abox_rows: ind_elems={} n_total_elems={} pure_sig={}/{} graph_sig={}/{} unhandled={} blocked={} func_data_conflicts={} skolem_ineqs={}",
                ind_elems.len(),
                n_total_elems,
                n_pure,
                sig_to_id.len(),
                n_graph,
                graph_sig_to_id.len(),
                has_unhandled_clause,
                raw.blocked.len(),
                func_data_conflict_pairs.len(),
                skolem_ineqs.len()
            );
        }

        for i in 0..ind_elems.len() {
            let u = ind_elems[i];
            for &v in &ind_elems[(i + 1)..] {
                let pk = pair_key(u, v);
                if diff.contains(&pk) {
                    continue;
                }
                if func_data_conflict_pairs.contains(&pk) {
                    for a in &elem_inds[u] {
                        for b in &elem_inds[v] {
                            if let (Some(&ai), Some(&bi)) =
                                (pub_ind_to_idx.get(a), pub_ind_to_idx.get(b))
                            {
                                if ai != bi {
                                    plan.residual_different_pairs
                                        .insert((ai.min(bi), ai.max(bi)));
                                }
                            }
                        }
                    }
                    continue;
                }
                let (model_v, horn_v) = match (pure_sig_id[u], pure_sig_id[v]) {
                    (Some(su), Some(sv)) => {
                        let sk = (su.min(sv), su.max(sv));
                        if let Some(&cached) = pure_memo.get(&sk) {
                            cached
                        } else {
                            let mv = test_pure_concept_merge(u, v, false);
                            let hv = if mv == PairVerdict::NotDifferent {
                                PairVerdict::NotDifferent
                            } else {
                                test_pure_concept_merge(u, v, true)
                            };
                            pure_memo.insert(sk, (mv, hv));
                            (mv, hv)
                        }
                    }
                    _ => {
                        let direct_link = adj_edges_m[u]
                            .iter()
                            .any(|&(s, _, t)| (s == u && t == v) || (s == v && t == u));
                        if !direct_link {
                            if let (Some(gu), Some(gv)) = (graph_sig_id[u], graph_sig_id[v]) {
                                let gk = (gu.min(gv), gu.max(gv));
                                if let Some(&cached) = graph_memo.get(&gk) {
                                    cached
                                } else {
                                    let mv = test_graph_merge(u, v, false, &base_diff);
                                    let hv = if mv == PairVerdict::NotDifferent {
                                        PairVerdict::NotDifferent
                                    } else {
                                        test_graph_merge(u, v, true, &base_diff)
                                    };
                                    graph_memo.insert(gk, (mv, hv));
                                    (mv, hv)
                                }
                            } else if skolem_ineqs.is_empty()
                                && pure_sig_id[v].is_some()
                                && !special_ind[v]
                            {
                                let mk = (u, pure_sig_id[v].unwrap(), u < v);
                                if let Some(&cached) = mixed_memo.get(&mk) {
                                    cached
                                } else {
                                    let mv = test_graph_merge(u, v, false, &base_diff);
                                    let hv = if mv == PairVerdict::NotDifferent {
                                        PairVerdict::NotDifferent
                                    } else {
                                        test_graph_merge(u, v, true, &base_diff)
                                    };
                                    mixed_memo.insert(mk, (mv, hv));
                                    (mv, hv)
                                }
                            } else if skolem_ineqs.is_empty()
                                && pure_sig_id[u].is_some()
                                && !special_ind[u]
                            {
                                let mk = (v, pure_sig_id[u].unwrap(), v < u);
                                if let Some(&cached) = mixed_memo.get(&mk) {
                                    cached
                                } else {
                                    let mv = test_graph_merge(u, v, false, &base_diff);
                                    let hv = if mv == PairVerdict::NotDifferent {
                                        PairVerdict::NotDifferent
                                    } else {
                                        test_graph_merge(u, v, true, &base_diff)
                                    };
                                    mixed_memo.insert(mk, (mv, hv));
                                    (mv, hv)
                                }
                            } else {
                                let mv = test_graph_merge(u, v, false, &diff);
                                let hv = if mv == PairVerdict::NotDifferent {
                                    PairVerdict::NotDifferent
                                } else {
                                    test_graph_merge(u, v, true, &diff)
                                };
                                (mv, hv)
                            }
                        } else {
                            let mv = test_graph_merge(u, v, false, &diff);
                            let hv = if mv == PairVerdict::NotDifferent {
                                PairVerdict::NotDifferent
                            } else {
                                test_graph_merge(u, v, true, &diff)
                            };
                            (mv, hv)
                        }
                    }
                };
                if diff_trace {
                    eprintln!(
                        "KM_DIFF_TRACE pair {:?} {:?}: model={:?} horn={:?}",
                        elem_inds[u], elem_inds[v], model_v, horn_v
                    );
                }
                match (model_v, horn_v) {
                    (PairVerdict::NotDifferent, _) => {}
                    (_, PairVerdict::HornClash) => {
                        diff.insert(pk);
                    }
                    _ => {
                        for a in &elem_inds[u] {
                            for b in &elem_inds[v] {
                                if let (Some(&ai), Some(&bi)) =
                                    (pub_ind_to_idx.get(a), pub_ind_to_idx.get(b))
                                {
                                    if ai != bi {
                                        plan.residual_different_pairs
                                            .insert((ai.min(bi), ai.max(bi)));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Propagate any newly discovered Horn clashes along functional / inverse-functional roles
        if (!func_obj_roles.is_empty() || !inv_func_obj_roles.is_empty()) && !diff.is_empty() {
            let mut func_edges: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
            let mut inv_func_edges: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
            for &(u, ref r, v) in &proved_edge_set {
                if u < n_elems && v < n_elems {
                    if func_obj_roles.contains(r.as_str()) {
                        func_edges.entry(r.as_str()).or_default().push((u, v));
                    }
                    if inv_func_obj_roles.contains(r.as_str()) {
                        inv_func_edges.entry(r.as_str()).or_default().push((u, v));
                    }
                }
            }
            loop {
                let before = diff.len();
                for list in func_edges.values() {
                    for i in 0..list.len() {
                        for j in (i + 1)..list.len() {
                            let (u1, x1) = list[i];
                            let (u2, x2) = list[j];
                            if u1 != u2 && x1 != x2 && diff.contains(&pair_key(x1, x2)) {
                                diff.insert(pair_key(u1, u2));
                            }
                        }
                    }
                }
                for list in inv_func_edges.values() {
                    for i in 0..list.len() {
                        for j in (i + 1)..list.len() {
                            let (x1, u1) = list[i];
                            let (x2, u2) = list[j];
                            if u1 != u2 && x1 != x2 && diff.contains(&pair_key(x1, x2)) {
                                diff.insert(pair_key(u1, u2));
                            }
                        }
                    }
                }
                if diff.len() == before {
                    break;
                }
            }
        }

        for (u, v) in diff {
            if u < n_elems && v < n_elems {
                for a in &elem_inds[u] {
                    for b in &elem_inds[v] {
                        if a != b {
                            let (x, y) = if a < b { (a, b) } else { (b, a) };
                            plan.proved_different.insert([x.clone(), y.clone()]);
                            if let (Some(&ai), Some(&bi)) =
                                (pub_ind_to_idx.get(a), pub_ind_to_idx.get(b))
                            {
                                plan.residual_different_pairs
                                    .remove(&(ai.min(bi), ai.max(bi)));
                            }
                        }
                    }
                }
            }
        }
    }

    Some(plan)
}

/// What the TBox lets an anonymous element do, read from the source for
/// `ExcursionBound`. Role names are the short names of `meta.rbox`; an inverse
/// role is `__inv__r`.
#[derive(Debug, Default)]
struct ExcursionSpec {
    input: crate::frontend::named_role_bound::ExcursionInput,
    /// A nominal edge or a merge into a nominal can lead from the anonymous
    /// tree of any named individual to any nominal individual: then all named
    /// individuals are one component.
    global: bool,
    /// An anonymous individual occurs in an object property assertion or an
    /// equality axiom.
    anonymous_links: bool,
}

impl ExcursionSpec {
    /// `None` when the source links anonymous individuals by assertions, or
    /// has the universal role or a fenced role chain, together with composite
    /// or merging roles: the
    /// caller then falls back to exact probes.
    fn collect(
        text: &str,
        rbox: &[Vec<String>],
        role_short: &dyn Fn(&str) -> String,
    ) -> Option<ExcursionSpec> {
        fn signed(node: &Node<'_>, role_short: &dyn Fn(&str) -> String) -> Option<String> {
            match node {
                Node::Atom(r) => Some(role_short(r)),
                Node::List("ObjectInverseOf", args) => {
                    args.first().and_then(Node::as_atom).map(|r| format!("__inv__{}", role_short(r)))
                }
                _ => None,
            }
        }
        fn walk(
            node: &Node<'_>,
            spec: &mut ExcursionSpec,
            role_short: &dyn Fn(&str) -> String,
        ) {
            let Node::List(head, args) = node else { return };
            let plain: Vec<&Node<'_>> = args.iter().filter(|a| a.head() != Some("Annotation")).collect();
            let input = &mut spec.input;
            match *head {
                "ObjectSomeValuesFrom" | "ObjectAllValuesFrom" if plain.len() >= 2 => {
                    if let Some(r) = signed(plain[0], role_short) {
                        if *head == "ObjectSomeValuesFrom" && plain[1].head() == Some("ObjectOneOf") {
                            input.nominal_roles.insert(r.clone());
                            input.named_roles.insert(r);
                            return;
                        }
                        input.gen_roles.insert(r);
                    }
                    walk(plain[1], spec, role_short);
                }
                "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality" if plain.len() >= 2 => {
                    if let Some(r) = signed(plain[1], role_short) {
                        input.gen_roles.insert(r.clone());
                        input.merging_roles.insert(r.clone());
                        if plain.get(2).and_then(|f| f.head()) == Some("ObjectOneOf") {
                            input.nominal_roles.insert(r.clone());
                            input.named_roles.insert(r);
                        }
                    }
                    for filler in plain.iter().skip(2) {
                        walk(filler, spec, role_short);
                    }
                }
                "ObjectHasValue" if plain.len() >= 2 => {
                    if let Some(r) = signed(plain[0], role_short) {
                        input.nominal_roles.insert(r.clone());
                        input.named_roles.insert(r);
                    }
                }
                "ObjectHasSelf" if !plain.is_empty() => {
                    if let Some(r) = signed(plain[0], role_short) {
                        input.self_roles.insert(r.clone());
                        input.named_roles.insert(r);
                    }
                }
                "ObjectOneOf" => {
                    input.merge_into_named = true;
                }
                "FunctionalObjectProperty" if !plain.is_empty() => {
                    if let Some(r) = signed(plain[0], role_short) {
                        input.merging_roles.insert(r);
                    }
                }
                "InverseFunctionalObjectProperty" if !plain.is_empty() => {
                    if let Some(r) = signed(plain[0], role_short) {
                        let inv = match r.strip_prefix("__inv__") {
                            Some(base) => base.to_string(),
                            None => format!("__inv__{r}"),
                        };
                        input.merging_roles.insert(inv);
                    }
                }
                "ReflexiveObjectProperty" if !plain.is_empty() => {
                    if let Some(r) = signed(plain[0], role_short) {
                        input.self_roles.insert(r.clone());
                        input.named_roles.insert(r);
                    }
                }
                "ClassAssertion" => {
                    if let Some(c) = plain.first() {
                        walk(c, spec, role_short);
                    }
                }
                "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" | "SameIndividual"
                | "DifferentIndividuals" => {
                    // An anonymous individual linked to others is part of
                    // the ABox graph, which the bound does not model; one
                    // with class assertions only is an isolated element.
                    if plain.iter().any(|a| a.as_atom().is_some_and(|t| t.starts_with("_:"))) {
                        spec.anonymous_links = true;
                    }
                }
                "Declaration" | "AnnotationAssertion" | "DataPropertyAssertion"
                | "NegativeDataPropertyAssertion" => {}
                _ => {
                    for a in plain {
                        walk(a, spec, role_short);
                    }
                }
            }
        }

        let mut composite = false;
        let mut fenced_chain = false;
        for row in rbox {
            match row.first().map(String::as_str) {
                Some("transitive" | "chain" | "chain-n") => composite = true,
                Some("fenced") if row.get(1).map(String::as_str) == Some("role-chain") => fenced_chain = true,
                _ => {}
            }
        }
        let mut spec = ExcursionSpec::default();
        let _ = crate::frontend::parse::for_each_ontology_child(text, |node| {
            walk(node, &mut spec, role_short);
            Ok(())
        });
        if !composite && spec.input.merging_roles.is_empty() && !fenced_chain {
            return Some(ExcursionSpec::default());
        }
        if fenced_chain || spec.anonymous_links || text.contains("topObjectProperty") {
            return None;
        }
        spec.global = spec.input.merge_into_named || !spec.input.nominal_roles.is_empty();
        Some(spec)
    }
}

/// Upper bound on the edges between named elements `0..n` that a model can
/// add through anonymous elements, beyond the named edges of `edge_set`: for
/// every role of `excursion_roles`, every pair of named elements in one
/// component. Components follow the named edges of `edge_set` (an anonymous
/// tree hangs under one named individual and merges only with the named
/// neighbours of its root), and are one when a nominal edge or a merge into a
/// nominal lets an anonymous tree reach any nominal individual.
struct ExcursionBound {
    /// Roles (short names) that may hold between named individuals through
    /// an anonymous element.
    roles: Vec<String>,
    /// Component of each named element.
    comp: Vec<usize>,
    /// Number of named elements per component.
    comp_size: HashMap<usize, usize>,
}

impl ExcursionBound {
    fn compute(
        spec: &ExcursionSpec,
        rbox: &[Vec<String>],
        n: usize,
        edge_set: &HashSet<(usize, String, usize)>,
    ) -> ExcursionBound {
        let mut input = spec.input.clone();
        for (u, r, v) in edge_set {
            if *u < n && *v < n {
                input.named_roles.insert(r.clone());
            }
        }
        let roles: Vec<String> =
            crate::frontend::named_role_bound::excursion_roles(rbox, &input).into_iter().collect();
        let mut uf: Vec<usize> = (0..n).collect();
        fn find(uf: &mut [usize], mut x: usize) -> usize {
            while uf[x] != x {
                uf[x] = uf[uf[x]];
                x = uf[x];
            }
            x
        }
        if !roles.is_empty() {
            if spec.global {
                for x in 1..n {
                    uf[x] = 0;
                }
            } else {
                for (u, _, v) in edge_set {
                    if *u < n && *v < n {
                        let (ru, rv) = (find(&mut uf, *u), find(&mut uf, *v));
                        if ru != rv {
                            uf[ru.max(rv)] = ru.min(rv);
                        }
                    }
                }
            }
        }
        let comp: Vec<usize> = (0..n).map(|u| find(&mut uf, u)).collect();
        let mut comp_size: HashMap<usize, usize> = HashMap::new();
        for &c in &comp {
            *comp_size.entry(c).or_default() += 1;
        }
        ExcursionBound { roles, comp, comp_size }
    }

    /// Whether every candidate edge is already in `proved` (named part).
    fn all_proved(&self, proved: &HashSet<(usize, String, usize)>) -> bool {
        if self.roles.is_empty() {
            return true;
        }
        let n = self.comp.len();
        let mut count: HashMap<(&str, usize), usize> = HashMap::new();
        for (u, r, v) in proved {
            if *u < n && *v < n && self.comp[*u] == self.comp[*v] {
                *count.entry((r.as_str(), self.comp[*u])).or_default() += 1;
            }
        }
        self.roles.iter().all(|r| {
            self.comp_size
                .iter()
                .all(|(c, size)| count.get(&(r.as_str(), *c)).copied().unwrap_or(0) == size * size)
        })
    }
}


/// Public names of the individuals that occur only in declarations,
/// annotations and `ClassAssertion(A, a)` with a named `A`, and at which every
/// logical axiom holds for a bare element: atomic classes exactly the asserted
/// `A`s, no successors, no data values. Empty when the source uses the
/// universal role, reflexive roles, or a construct `holds_at_bare` does not
/// evaluate.
fn bare_unconstrained_individuals(
    text: &str,
    ind_of: &dyn Fn(&str) -> Option<String>,
    expand: &dyn Fn(&str) -> String,
) -> HashSet<String> {
    if text.contains("topObjectProperty") || text.contains("topDataProperty") {
        return HashSet::new();
    }
    fn atoms<'a>(node: &Node<'a>, out: &mut Vec<&'a str>) {
        match node {
            Node::Atom(a) => out.push(a),
            Node::List(_, args) => {
                for a in args {
                    atoms(a, out);
                }
            }
        }
    }
    let logical = |n: &Node| !matches!(n, Node::List("Annotation", _));
    let mut asserted: HashMap<String, BTreeSet<String>> = HashMap::new();
    let mut constrained: HashSet<String> = HashSet::new();
    let mut tbox: Vec<String> = Vec::new();
    let mut ok = true;
    let parsed = crate::frontend::parse::for_each_ontology_child(text, |node| {
        let Some(head) = node.head() else { return Ok(()) };
        let args: Vec<&Node> = match node {
            Node::List(_, a) => a.iter().filter(|n| logical(n)).collect(),
            _ => Vec::new(),
        };
        match head {
            "Declaration" | "AnnotationAssertion" | "Import" | "Annotation" | "SubAnnotationPropertyOf"
            | "AnnotationPropertyDomain" | "AnnotationPropertyRange" => return Ok(()),
            "ClassAssertion" if args.len() == 2 => {
                if let (Some(c), Some(i)) = (args[0].as_atom(), args[1].as_atom()) {
                    if let Some(p) = ind_of(i) {
                        asserted.entry(p).or_default().insert(expand(c));
                        return Ok(());
                    }
                }
            }
            "ReflexiveObjectProperty" | "HasKey" | "DLSafeRule" | "DisjointUnion" => {
                ok = false;
                return Ok(());
            }
            _ => {}
        }
        let mut toks = Vec::new();
        for a in &args {
            atoms(a, &mut toks);
        }
        for t in toks {
            if let Some(p) = ind_of(t) {
                constrained.insert(p);
            }
        }
        tbox.push(head.to_string());
        Ok(())
    });
    if parsed.is_err() || !ok {
        return HashSet::new();
    }
    // Axiom kinds that hold at a bare element whatever their arguments:
    // property axioms (it has no edges) and assertions about other individuals.
    let edge_only = |h: &str| {
        matches!(
            h,
            "SubObjectPropertyOf" | "EquivalentObjectProperties" | "DisjointObjectProperties"
                | "InverseObjectProperties" | "ObjectPropertyDomain" | "ObjectPropertyRange"
                | "FunctionalObjectProperty" | "InverseFunctionalObjectProperty"
                | "SymmetricObjectProperty" | "AsymmetricObjectProperty"
                | "IrreflexiveObjectProperty" | "TransitiveObjectProperty"
                | "SubDataPropertyOf" | "EquivalentDataProperties" | "DisjointDataProperties"
                | "DataPropertyDomain" | "DataPropertyRange" | "FunctionalDataProperty"
                | "DatatypeDefinition" | "ClassAssertion" | "ObjectPropertyAssertion"
                | "DataPropertyAssertion" | "NegativeObjectPropertyAssertion"
                | "NegativeDataPropertyAssertion" | "SameIndividual" | "DifferentIndividuals"
        )
    };
    if tbox.iter().any(|h| !edge_only(h) && !matches!(h.as_str(), "SubClassOf" | "EquivalentClasses" | "DisjointClasses")) {
        return HashSet::new();
    }
    let candidates: Vec<(String, BTreeSet<String>)> = asserted
        .into_iter()
        .filter(|(p, _)| !constrained.contains(p))
        .collect();
    if candidates.is_empty() {
        return HashSet::new();
    }
    let mut verdict: HashMap<BTreeSet<String>, bool> = HashMap::new();
    let mut out = HashSet::new();
    for (p, s_a) in candidates {
        let holds = *verdict.entry(s_a.clone()).or_insert_with(|| holds_at_bare(text, &s_a, expand));
        if holds {
            out.insert(p);
        }
    }
    out
}

/// Whether every `SubClassOf`, `EquivalentClasses` and `DisjointClasses`
/// axiom of `text` holds at a bare element with atomic classes `s_a` (full
/// IRIs). `false` when some class expression cannot be evaluated.
fn holds_at_bare(text: &str, s_a: &BTreeSet<String>, expand: &dyn Fn(&str) -> String) -> bool {
    fn eval(n: &Node, s_a: &BTreeSet<String>, expand: &dyn Fn(&str) -> String) -> Option<bool> {
        match n {
            Node::Atom(t) => {
                let iri = expand(t);
                if iri.ends_with("#Thing") && iri.contains("2002/07/owl") || *t == "owl:Thing" {
                    Some(true)
                } else if iri.ends_with("#Nothing") && iri.contains("2002/07/owl") || *t == "owl:Nothing" {
                    Some(false)
                } else {
                    Some(s_a.contains(&iri))
                }
            }
            Node::List(h, args) => {
                let args: Vec<&Node> = args.iter().filter(|a| !matches!(a, Node::List("Annotation", _))).collect();
                let num = |i: usize| args.get(i).and_then(|a| a.as_atom()).and_then(|a| a.parse::<u64>().ok());
                match *h {
                    "ObjectIntersectionOf" => {
                        let mut all = true;
                        for a in &args {
                            all &= eval(a, s_a, expand)?;
                        }
                        Some(all)
                    }
                    "ObjectUnionOf" => {
                        let mut any = false;
                        for a in &args {
                            any |= eval(a, s_a, expand)?;
                        }
                        Some(any)
                    }
                    "ObjectComplementOf" if args.len() == 1 => eval(args[0], s_a, expand).map(|b| !b),
                    "ObjectSomeValuesFrom" | "DataSomeValuesFrom" | "ObjectHasValue" | "DataHasValue"
                    | "ObjectHasSelf" | "ObjectOneOf" => Some(false),
                    "ObjectAllValuesFrom" | "DataAllValuesFrom" | "ObjectMaxCardinality"
                    | "DataMaxCardinality" => Some(true),
                    "ObjectMinCardinality" | "DataMinCardinality" | "ObjectExactCardinality"
                    | "DataExactCardinality" => num(0).map(|n| n == 0),
                    _ => None,
                }
            }
        }
    }
    let mut ok = true;
    let parsed = crate::frontend::parse::for_each_ontology_child(text, |node| {
        if !ok {
            return Ok(());
        }
        let (h, args) = match node {
            Node::List(h, a) => (*h, a.iter().filter(|n| !matches!(n, Node::List("Annotation", _))).collect::<Vec<_>>()),
            _ => return Ok(()),
        };
        let vals = || -> Option<Vec<bool>> { args.iter().map(|a| eval(a, s_a, expand)).collect() };
        ok = match h {
            "SubClassOf" => match vals() {
                Some(v) if v.len() == 2 => !v[0] || v[1],
                _ => false,
            },
            "EquivalentClasses" => match vals() {
                Some(v) => v.windows(2).all(|w| w[0] == w[1]),
                None => false,
            },
            "DisjointClasses" => match vals() {
                Some(v) => v.iter().filter(|b| **b).count() <= 1,
                None => false,
            },
            _ => true,
        };
        Ok(())
    });
    parsed.is_ok() && ok
}

#[cfg(test)]
mod tests {
    use super::super::config::Config;
    use super::super::realize::{classify_extended, TypeMode};
    use super::super::tmpfile::TempPath;
    use super::*;

    fn assert_model_abox_matches_probe_oracle(name: &str, ofn: &str) {
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        let path = TempPath::new(&format!("-{name}.ofn"));
        std::fs::write(path.path(), ofn).unwrap();
        let cfg = Config::from_env();

        let model_ext = classify_extended(
            &cfg,
            path.path(),
            Some(TypeMode::All),
            false,
            false,
            false,
            true,
            true,
        )
        .unwrap();

        let probe_ext = {
            let _g = crate::routing::EnvironmentGuard::capture();
            std::env::set_var("KM_ABOX_PROBES_ONLY", "1");
            classify_extended(
                &cfg,
                path.path(),
                Some(TypeMode::All),
                false,
                false,
                false,
                true,
                true,
            )
            .unwrap()
        };

        assert_eq!(
            model_ext.abox.values, probe_ext.abox.values,
            "VALUE mismatch on {name} (auto)"
        );
        assert_eq!(
            model_ext.abox.different, probe_ext.abox.different,
            "DIFFERENT mismatch on {name} (auto)"
        );

        if !ofn.contains("HasKey(") {
            let _g = crate::routing::EnvironmentGuard::capture();
            crate::routing::Route::HtBridge.apply_environment();
            std::env::set_var("KM_ROUTE", "ht_bridge");
            std::env::set_var("KM_REALIZE_ANY_ROUTE", "1");
            std::env::set_var("KM_THREADS", "1");
            let ht_cfg = Config::from_env();
            let ht_ext = classify_extended(
                &ht_cfg,
                path.path(),
                Some(TypeMode::All),
                false,
                false,
                false,
                true,
                true,
            )
            .unwrap();
            assert_eq!(
                ht_ext.abox.values, probe_ext.abox.values,
                "VALUE mismatch on {name} (ht_bridge)"
            );
            assert_eq!(
                ht_ext.abox.different, probe_ext.abox.different,
                "DIFFERENT mismatch on {name} (ht_bridge)"
            );
        }
    }

    #[test]
    fn abox_rows_extension_retains_merged_targets_on_adv_ofn() {
        let _test_env = crate::test_env::read();
        let adv = std::fs::read_to_string(
            "/mnt/data1/leechuck/km-work/v170/scratch/review/e9/adv.ofn",
        )
        .unwrap_or_else(|_| {
            include_str!("../../src/frontend/named_role_bound.rs")
                .split("const ADV_OFN: &str = r#\"")
                .nth(1)
                .unwrap()
                .split("\"#;")
                .next()
                .unwrap()
                .to_owned()
        });
        let (canon, individuals) = super::super::realize::canonical_individuals(&adv).unwrap();
        let roles = super::super::properties::canonical_properties(&canon).unwrap();
        let (_ext, abox_probes) = extension(&canon, &roles, &individuals, true, false);
        let has_probe_for = |role_iri: &str, ind_iri: &str| -> bool {
            let r_idx = abox_probes.roles.iter().position(|r| r == role_iri).unwrap();
            let b_idx = abox_probes
                .individuals
                .iter()
                .position(|i| i == ind_iri)
                .unwrap();
            abox_probes
                .probes
                .values()
                .any(|&p| p == Probe::Value(r_idx, b_idx))
        };
        assert!(has_probe_for(":s6", ":c6"));
        assert!(has_probe_for(":s12", ":c12"));
        assert!(has_probe_for(":t14", ":b14"));
        assert!(has_probe_for(":r10", ":a10"));
        assert!(!has_probe_for(":s6", ":z0"));
    }

    #[test]
    fn abox_rows_extension_retains_targets_across_16_adversarial_cases() {
        let _test_env = crate::test_env::read();
        let mut pad = String::new();
        for i in 0..8 {
            pad.push_str(&format!("Declaration(ObjectProperty(:pad{i}))\n"));
        }
        for i in 0..40 {
            pad.push_str(&format!("Declaration(NamedIndividual(:z{i}))\n"));
        }
        let cases: &[(&str, &str, &[&str])] = &[
            (
                "functional_role_chain_merge",
                r#"Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2))
                   Declaration(ObjectProperty(:f3)) Declaration(ObjectProperty(:other))
                   FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2) FunctionalObjectProperty(:f3)
                   ObjectPropertyAssertion(:f1 :a :b1) ObjectPropertyAssertion(:f1 :a :b2)
                   ObjectPropertyAssertion(:f2 :b1 :c1) ObjectPropertyAssertion(:f2 :b2 :c2)
                   ObjectPropertyAssertion(:f3 :c1 :d1) ObjectPropertyAssertion(:f3 :c2 :d2)
                   ObjectPropertyAssertion(:other :x :d1)"#,
                &[":d1", ":d2"],
            ),
            (
                "functional_chain_with_has_value_merge",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2)) Declaration(ObjectProperty(:other))
                   FunctionalObjectProperty(:f1) FunctionalObjectProperty(:f2)
                   ObjectPropertyAssertion(:f1 :a :b1)
                   SubClassOf(:A ObjectHasValue(:f1 :b2)) ClassAssertion(:A :a)
                   ObjectPropertyAssertion(:f2 :b1 :c1) ObjectPropertyAssertion(:f2 :b2 :c2)
                   ObjectPropertyAssertion(:other :x :c1)"#,
                &[":c1", ":c2"],
            ),
            (
                "asserted_target_with_has_value_under_inverse",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                   ObjectPropertyAssertion(:s :b :a)
                   SubClassOf(:A ObjectHasValue(:r :c)) ClassAssertion(:A :a)
                   ObjectPropertyAssertion(:other :d :b)"#,
                &[":b", ":c"],
            ),
            (
                "asserted_target_with_inverse_of_has_value",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                   ObjectPropertyAssertion(:r :a :b)
                   SubClassOf(:A ObjectHasValue(ObjectInverseOf(:s) :c)) ClassAssertion(:A :a)
                   ObjectPropertyAssertion(:other :d :b)"#,
                &[":b", ":c"],
            ),
            (
                "inverse_has_value_source_merge",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:d))
                   InverseObjectProperties(:r :s) FunctionalObjectProperty(:r)
                   ObjectPropertyAssertion(:r :a :b)
                   SubClassOf(:A ObjectHasValue(:s :a)) ClassAssertion(:A :c)
                   ObjectPropertyAssertion(:other :d :b)"#,
                &[":b", ":c"],
            ),
            (
                "max_cardinality_1_on_inverse_role",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   SubClassOf(:A ObjectMaxCardinality(1 ObjectInverseOf(:r)))
                   ClassAssertion(:A :x)
                   ObjectPropertyAssertion(:r :a :x) ObjectPropertyAssertion(:r :b :x)
                   ObjectPropertyAssertion(:other :d :a)"#,
                &[":a", ":b"],
            ),
            (
                "exact_cardinality_1_on_inverse_role_with_has_value",
                r#"Declaration(Class(:A)) Declaration(Class(:B))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   Declaration(NamedIndividual(:d)) Declaration(NamedIndividual(:x))
                   SubClassOf(:A ObjectExactCardinality(1 ObjectInverseOf(:r)))
                   ClassAssertion(:A :x)
                   ObjectPropertyAssertion(:r :a :x)
                   SubClassOf(:B ObjectHasValue(:r :x)) ClassAssertion(:B :b)
                   ObjectPropertyAssertion(:other :d :a)"#,
                &[":a", ":b"],
            ),
            (
                "merge_feeding_property_chain",
                r#"Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:r1))
                   Declaration(ObjectProperty(:r2)) Declaration(ObjectProperty(:other))
                   FunctionalObjectProperty(:f)
                   ObjectPropertyAssertion(:f :x :b1) ObjectPropertyAssertion(:f :x :b2)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   ObjectPropertyAssertion(:r1 :a :b1) ObjectPropertyAssertion(:r2 :b2 :c)"#,
                &[":c"],
            ),
            (
                "two_merges_feeding_property_chain",
                r#"Declaration(ObjectProperty(:f1)) Declaration(ObjectProperty(:f2))
                   Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:other))
                   FunctionalObjectProperty(:f1) InverseFunctionalObjectProperty(:f2)
                   ObjectPropertyAssertion(:f1 :u :b1) ObjectPropertyAssertion(:f1 :u :b2)
                   ObjectPropertyAssertion(:f2 :c1 :v) ObjectPropertyAssertion(:f2 :c2 :v)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   ObjectPropertyAssertion(:r1 :a :b1)
                   ObjectPropertyAssertion(:r2 :b2 :c1)"#,
                &[":c1", ":c2"],
            ),
            (
                "reflexive_and_has_self_in_chain_and_merge",
                r#"Declaration(Class(:B))
                   Declaration(ObjectProperty(:refl)) Declaration(ObjectProperty(:s))
                   Declaration(ObjectProperty(:fself)) Declaration(ObjectProperty(:other))
                   ReflexiveObjectProperty(:refl)
                   SubObjectPropertyOf(ObjectPropertyChain(:refl :s) :other)
                   ObjectPropertyAssertion(:s :a :b)
                   FunctionalObjectProperty(:fself)
                   SubClassOf(:B ObjectHasSelf(:fself)) ClassAssertion(:B :m1)
                   ObjectPropertyAssertion(:fself :m1 :m2)
                   ObjectPropertyAssertion(:other :d :m1)"#,
                &[":b", ":m1", ":m2"],
            ),
            (
                "symmetric_and_transitive_with_merge",
                r#"Declaration(ObjectProperty(:sym)) Declaration(ObjectProperty(:other))
                   Declaration(ObjectProperty(:f))
                   SymmetricObjectProperty(:sym) TransitiveObjectProperty(:other)
                   SubObjectPropertyOf(:sym :other) FunctionalObjectProperty(:f)
                   ObjectPropertyAssertion(:sym :b1 :a)
                   ObjectPropertyAssertion(:f :x :b1) ObjectPropertyAssertion(:f :x :b2)
                   ObjectPropertyAssertion(:other :b2 :c)"#,
                &[":a", ":b1", ":b2", ":c"],
            ),
            (
                "symmetric_with_has_value",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:other))
                   Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
                   SymmetricObjectProperty(:other)
                   SubClassOf(:A ObjectHasValue(:other :b)) ClassAssertion(:A :a)"#,
                &[":a", ":b"],
            ),
            (
                "equivalent_properties_with_inverses_and_merge",
                r#"Declaration(ObjectProperty(:p1)) Declaration(ObjectProperty(:p2))
                   Declaration(ObjectProperty(:p3)) Declaration(ObjectProperty(:other))
                   EquivalentObjectProperties(:p1 :p2)
                   InverseObjectProperties(:p2 :p3)
                   FunctionalObjectProperty(:p2)
                   ObjectPropertyAssertion(:p1 :a :b1)
                   ObjectPropertyAssertion(:p3 :b2 :a)
                   ObjectPropertyAssertion(:other :d :b1)"#,
                &[":b1", ":b2"],
            ),
            (
                "role_hierarchy_with_inverses_and_has_value",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))
                   Declaration(ObjectProperty(:t)) Declaration(ObjectProperty(:other))
                   SubObjectPropertyOf(:r ObjectInverseOf(:s))
                   SubObjectPropertyOf(ObjectInverseOf(:s) :t)
                   SubClassOf(:A ObjectHasValue(:r :b)) ClassAssertion(:A :a)
                   FunctionalObjectProperty(:t)
                   ObjectPropertyAssertion(:t :a :c)
                   ObjectPropertyAssertion(:other :d :b)"#,
                &[":b", ":c"],
            ),
            (
                "same_individual_chain_of_length_4",
                r#"Declaration(ObjectProperty(:other))
                   SameIndividual(:i1 :i2)
                   SameIndividual(:i2 :i3)
                   SameIndividual(:i3 :i4)
                   SameIndividual(:i4 :i5)
                   ObjectPropertyAssertion(:other :src :i1)"#,
                &[":i1", ":i2", ":i3", ":i4", ":i5"],
            ),
            (
                "nary_chain_with_has_value_and_same_individual",
                r#"Declaration(Class(:A))
                   Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:r3)) Declaration(ObjectProperty(:f))
                   Declaration(ObjectProperty(:other))
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2 :r3) :other)
                   SubClassOf(:A ObjectHasValue(:r1 :b1)) ClassAssertion(:A :a)
                   SameIndividual(:b1 :b2)
                   ObjectPropertyAssertion(:r2 :b2 :c1)
                   FunctionalObjectProperty(:f)
                   ObjectPropertyAssertion(:f :u :c1) ObjectPropertyAssertion(:f :u :c2)
                   ObjectPropertyAssertion(:r3 :c2 :d)"#,
                &[":d"],
            ),
            (
                "subproperty_of_functional_feeding_chain",
                r#"Declaration(ObjectProperty(:subf)) Declaration(ObjectProperty(:f))
                   Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))
                   Declaration(ObjectProperty(:other))
                   SubObjectPropertyOf(:subf :f)
                   FunctionalObjectProperty(:f)
                   ObjectPropertyAssertion(:subf :u :b1) ObjectPropertyAssertion(:subf :u :b2)
                   SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :other)
                   ObjectPropertyAssertion(:r1 :a :b1) ObjectPropertyAssertion(:r2 :b2 :c)"#,
                &[":c"],
            ),
        ];

        for (name, body, expected) in cases {
            let doc = format!("Prefix(:=<http://ex.org/>)\nOntology(<http://ex.org/{name}>\n{pad}{body}\n)");
            let (canon, individuals) = super::super::realize::canonical_individuals(&doc).unwrap();
            let roles = super::super::properties::canonical_properties(&canon).unwrap();
            assert!(roles.len() * individuals.len() >= 256);
            let (_ext, abox_probes) = extension(&canon, &roles, &individuals, true, false);
            let r_idx = abox_probes.roles.iter().position(|r| r == ":other").unwrap();
            for &exp in *expected {
                let b_idx = abox_probes.individuals.iter().position(|i| i == exp).unwrap();
                assert!(
                    abox_probes.probes.values().any(|&p| p == Probe::Value(r_idx, b_idx)),
                    "case {name}: missing probe for (:other, {exp})"
                );
            }
        }
    }

    #[test]
    fn abox_rows_extension_retains_targets_on_c4_c6_and_20_anonymous_routing_cases() {
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
            let (canon, individuals) = super::super::realize::canonical_individuals(&doc).unwrap();
            let roles = super::super::properties::canonical_properties(&canon).unwrap();
            assert!(roles.len() * individuals.len() >= 256);
            let (_ext, abox_probes) = extension(&canon, &roles, &individuals, true, false);
            let r_idx = abox_probes.roles.iter().position(|r| r == role).unwrap();
            for &exp in *expected {
                let b_idx = abox_probes.individuals.iter().position(|i| i == exp).unwrap();
                assert!(
                    abox_probes.probes.values().any(|&p| p == Probe::Value(r_idx, b_idx)),
                    "case {name}: missing probe for ({role}, {exp})"
                );
            }
        }
    }

    #[test]
    fn d1_and_d2_supervisor_repros_and_adversarial_cases_match_exact_oracle() {
        let _test_env = crate::test_env::write();

        // Supervisor repro d1.ofn: merged individual triggers A ⊓ B ⊓ D ⊑ C with DisjointClasses(C, D)
        let d1 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/d1>\n\
            Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))\n\
            ClassAssertion(:A :a) ClassAssertion(:D :a) ClassAssertion(:B :b) ClassAssertion(:B :c) ClassAssertion(:A :c)\n\
            SubClassOf(ObjectIntersectionOf(:A :B :D) :C)\n\
            DisjointClasses(:C :D)\n)";
        assert_model_abox_matches_probe_oracle("d1", d1);

        // Supervisor repro d2.ofn: merged individual gets r-successor and s-successor with ∃r.⊤ ⊓ ∃s.⊤ ⊑ ⊥
        let d2 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/d2>\n\
            Declaration(Class(:A)) Declaration(Class(:B)) Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:x)) Declaration(NamedIndividual(:y))\n\
            ObjectPropertyAssertion(:r :a :x) ObjectPropertyAssertion(:s :b :y)\n\
            SubClassOf(ObjectIntersectionOf(ObjectSomeValuesFrom(:r owl:Thing) ObjectSomeValuesFrom(:s owl:Thing)) owl:Nothing)\n)";
        assert_model_abox_matches_probe_oracle("d2", d2);

        // Adversarial 1: FunctionalObjectProperty + disjoint classes on successors
        let adv1 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv1>\n\
            Declaration(Class(:C)) Declaration(Class(:D)) Declaration(ObjectProperty(:r))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:x)) Declaration(NamedIndividual(:y))\n\
            FunctionalObjectProperty(:r)\n\
            ObjectPropertyAssertion(:r :a :x) ObjectPropertyAssertion(:r :b :y)\n\
            ClassAssertion(:C :x) ClassAssertion(:D :y)\n\
            DisjointClasses(:C :D)\n)";
        assert_model_abox_matches_probe_oracle("adv1-func-role", adv1);

        // Adversarial 2: InverseFunctionalObjectProperty + DifferentIndividuals on sources
        let adv2 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv2>\n\
            Declaration(ObjectProperty(:r))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:x)) Declaration(NamedIndividual(:y))\n\
            InverseFunctionalObjectProperty(:r)\n\
            ObjectPropertyAssertion(:r :x :a) ObjectPropertyAssertion(:r :y :b)\n\
            DifferentIndividuals(:x :y)\n)";
        assert_model_abox_matches_probe_oracle("adv2-inv-func", adv2);

        // Adversarial 3: HasKey forcing individual merge + disjointness propagation
        let adv3 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv3>\n\
            Declaration(Class(:C)) Declaration(Class(:D)) Declaration(Class(:E)) Declaration(ObjectProperty(:r))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c)) Declaration(NamedIndividual(:k))\n\
            HasKey(:C (:r) ())\n\
            ClassAssertion(:C :a) ClassAssertion(:C :b)\n\
            ObjectPropertyAssertion(:r :a :k) ObjectPropertyAssertion(:r :b :k)\n\
            ClassAssertion(:D :a) ClassAssertion(:E :c)\n\
            DisjointClasses(:D :E)\n)";
        assert_model_abox_matches_probe_oracle("adv3-haskey", adv3);

        // Adversarial 4: Nominals (ObjectOneOf) + ObjectAllValuesFrom
        let adv4 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv4>\n\
            Declaration(Class(:B)) Declaration(ObjectProperty(:r))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:x)) Declaration(NamedIndividual(:y))\n\
            ObjectPropertyAssertion(:r :a :x)\n\
            ClassAssertion(:B :b)\n\
            SubClassOf(:B ObjectAllValuesFrom(:r ObjectOneOf(:y)))\n\
            DifferentIndividuals(:x :y)\n)";
        assert_model_abox_matches_probe_oracle("adv4-nominals-forall", adv4);

        // Adversarial 5: NegativeObjectPropertyAssertion + SubObjectPropertyOf
        let adv5 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv5>\n\
            Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:x))\n\
            SubObjectPropertyOf(:r1 :r2)\n\
            ObjectPropertyAssertion(:r1 :a :x)\n\
            NegativeObjectPropertyAssertion(:r2 :b :x)\n)";
        assert_model_abox_matches_probe_oracle("adv5-neg-opa-subrole", adv5);

        // Adversarial 6: FunctionalDataProperty with equal vs unequal lexical literals
        let adv6 = "Prefix(:=<http://ex.org/>)\n\
            Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
            Ontology(<http://ex.org/adv6>\n\
            Declaration(DataProperty(:dp))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))\n\
            FunctionalDataProperty(:dp)\n\
            DataPropertyAssertion(:dp :a \"1\"^^xsd:integer)\n\
            DataPropertyAssertion(:dp :b \"01\"^^xsd:int)\n\
            DataPropertyAssertion(:dp :c \"2\"^^xsd:integer)\n)";
        assert_model_abox_matches_probe_oracle("adv6-func-data", adv6);

        // Adversarial 7: Qualified ObjectMaxCardinality(1, r, C)
        let adv7 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv7>\n\
            Declaration(Class(:A)) Declaration(Class(:C)) Declaration(ObjectProperty(:r))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:x)) Declaration(NamedIndividual(:y))\n\
            SubClassOf(:A ObjectMaxCardinality(1 :r :C))\n\
            ClassAssertion(:A :a)\n\
            ObjectPropertyAssertion(:r :a :x) ObjectPropertyAssertion(:r :b :y)\n\
            ClassAssertion(:C :x) ClassAssertion(:C :y)\n\
            DifferentIndividuals(:x :y)\n)";
        assert_model_abox_matches_probe_oracle("adv7-qual-max1", adv7);

        // Adversarial 8: ObjectMaxCardinality(2, r, owl:Thing) pigeonhole clash on merge
        let adv8 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv8>\n\
            Declaration(ObjectProperty(:r))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
            Declaration(NamedIndividual(:x1)) Declaration(NamedIndividual(:x2)) Declaration(NamedIndividual(:x3))\n\
            SubClassOf(owl:Thing ObjectMaxCardinality(2 :r owl:Thing))\n\
            ObjectPropertyAssertion(:r :a :x1) ObjectPropertyAssertion(:r :a :x2)\n\
            ObjectPropertyAssertion(:r :b :x3)\n\
            DifferentIndividuals(:x1 :x2 :x3)\n)";
        assert_model_abox_matches_probe_oracle("adv8-max2-pigeonhole", adv8);

        // Adversarial 9: Asymmetric / Irreflexive simple role (merging a and b creates self-loop s(a,a))
        let adv9 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv9>\n\
            Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:r))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))\n\
            IrreflexiveObjectProperty(:s)\n\
            SubObjectPropertyOf(:s :r)\n\
            TransitiveObjectProperty(:r)\n\
            ObjectPropertyAssertion(:s :a :b)\n\
            ObjectPropertyAssertion(:r :b :c)\n)";
        assert_model_abox_matches_probe_oracle("adv9-irrefl-subrole", adv9);

        // Adversarial 10: ObjectPropertyChain + ObjectAllValuesFrom clash on merge
        let adv10 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv10>\n\
            Declaration(Class(:B)) Declaration(Class(:C))\n\
            Declaration(ObjectProperty(:r1)) Declaration(ObjectProperty(:r2)) Declaration(ObjectProperty(:r3))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:m)) Declaration(NamedIndividual(:x))\n\
            SubObjectPropertyOf(ObjectPropertyChain(:r1 :r2) :r3)\n\
            ObjectPropertyAssertion(:r1 :a :m) ObjectPropertyAssertion(:r2 :m :x)\n\
            ClassAssertion(:B :b)\n\
            SubClassOf(:B ObjectAllValuesFrom(:r3 :C))\n\
            ClassAssertion(ObjectComplementOf(:C) :x)\n)";
        assert_model_abox_matches_probe_oracle("adv10-chain-forall", adv10);

        // Adversarial 11: Disjunctive TBox where both branches are disjoint with D
        let adv11 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv11>\n\
            Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
            SubClassOf(:A ObjectUnionOf(:B :C))\n\
            DisjointClasses(:B :D)\n\
            DisjointClasses(:C :D)\n\
            ClassAssertion(:A :a) ClassAssertion(:D :b)\n)";
        assert_model_abox_matches_probe_oracle("adv11-disj-both-clash", adv11);

        // Adversarial 12: Disjunctive TBox where only one branch is disjoint with D (a and b are NOT different)
        let adv12 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv12>\n\
            Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
            SubClassOf(:A ObjectUnionOf(:B :C))\n\
            DisjointClasses(:B :D)\n\
            ClassAssertion(:A :a) ClassAssertion(:D :b)\n)";
        assert_model_abox_matches_probe_oracle("adv12-disj-one-branch-sat", adv12);

        // Adversarial 13: VALUE entailed via existential into singleton nominal class (A ⊑ ∃r.C, C ⊑ {b})
        let adv13 = "Prefix(:=<http://ex.org/>)\n\
            Ontology(<http://ex.org/adv13>\n\
            Declaration(Class(:A)) Declaration(Class(:C)) Declaration(ObjectProperty(:r))\n\
            Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
            ClassAssertion(:A :a)\n\
            SubClassOf(:A ObjectSomeValuesFrom(:r :C))\n\
            SubClassOf(:C ObjectOneOf(:b))\n)";
        assert_model_abox_matches_probe_oracle("adv13-nominal-absorption-value", adv13);
    }

    /// `--values` without `--realize` (no individual probes, so the model
    /// path reads an elided or EL-canonical model) against the exact probe
    /// oracle, plus the HermiT rows each case must contain. With `pad`, 40
    /// filler individuals and 6 filler roles switch on `NamedRoleBound`.
    fn assert_values_without_realize(name: &str, axioms: &str, expect: &[[&str; 3]], pad: bool) {
        let mut toks: BTreeSet<String> = BTreeSet::new();
        let mut cur = String::new();
        let mut in_tok = false;
        for ch in axioms.chars() {
            if ch == ':' {
                in_tok = true;
                cur.clear();
            } else if in_tok && ch.is_ascii_alphanumeric() {
                cur.push(ch);
            } else if in_tok {
                in_tok = false;
                toks.insert(cur.clone());
            }
        }
        let is_ind = |t: &str| matches!(t, "a" | "b" | "d" | "e");
        let mut decls = String::new();
        for t in &toks {
            if t == "Thing" {
                continue;
            } else if is_ind(t) {
                decls.push_str(&format!("Declaration(NamedIndividual(:{t}))\n"));
            } else if t.starts_with(|c: char| c.is_ascii_uppercase()) {
                decls.push_str(&format!("Declaration(Class(:{t}))\n"));
            } else {
                decls.push_str(&format!("Declaration(ObjectProperty(:{t}))\n"));
            }
        }
        let mut extra = String::new();
        if pad {
            for i in 0..40 {
                decls.push_str(&format!("Declaration(NamedIndividual(:z{i}))\n"));
            }
            for i in 0..6 {
                decls.push_str(&format!("Declaration(ObjectProperty(:p{i}))\n"));
            }
            extra.push_str("ObjectPropertyAssertion(:p0 :z0 :z1)\n");
        }
        let ofn = format!(
            "Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nOntology(<http://ex.org/{name}>\n{decls}{axioms}\n{extra})\n"
        );
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        let path = TempPath::new(&format!("-{name}.ofn"));
        std::fs::write(path.path(), &ofn).unwrap();
        let cfg = Config::from_env();
        let model_ext = classify_extended(&cfg, path.path(), None, false, false, false, true, false).unwrap();
        let probe_ext = {
            let _g = crate::routing::EnvironmentGuard::capture();
            std::env::set_var("KM_ABOX_PROBES_ONLY", "1");
            classify_extended(&cfg, path.path(), None, false, false, false, true, false).unwrap()
        };
        let short = |s: &str| s.rsplit([':', '/', '#']).next().unwrap_or(s).to_string();
        let rows: BTreeSet<[String; 3]> = model_ext
            .abox
            .values
            .clone()
            .unwrap_or_default()
            .into_iter()
            .map(|[r, a, b]| [short(&r), short(&a), short(&b)])
            .collect();
        for [r, a, b] in expect {
            assert!(
                rows.contains(&[r.to_string(), a.to_string(), b.to_string()]),
                "{name}: missing VALUE {r} {a} {b}; got {rows:?}"
            );
        }
        assert_eq!(model_ext.abox.values, probe_ext.abox.values, "VALUE mismatch on {name}");
    }

    /// Values between named individuals derived through an anonymous
    /// individual by a role chain or a transitive role (the `f9002_44` shape
    /// and its siblings). The expected rows are HermiT's.
    #[test]
    fn values_through_anonymous_excursions_without_realize() {
        let cases: &[(&str, &str, &[[&str; 3]])] = &[
            (
                "f9002_44_chain_anon",
                "SubObjectPropertyOf(ObjectInverseOf(:s3) :s1)\nSymmetricObjectProperty(:s1)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(ObjectInverseOf(:s3) :B))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:s1 :s3) :c1)\nClassAssertion(:B :a)",
                &[["c1", "a", "a"]],
            ),
            (
                "chain3_around_abox_edge",
                "ObjectPropertyAssertion(:r :a :b)\nClassAssertion(:B :b)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:s owl:Thing))\n\
                 SubObjectPropertyOf(ObjectInverseOf(:s) :t)\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:r :s :t) :c)",
                &[["c", "a", "b"]],
            ),
            (
                "transitive_symmetric_loop",
                "TransitiveObjectProperty(:t)\nSymmetricObjectProperty(:t)\nClassAssertion(:B :a)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:t owl:Thing))",
                &[["t", "a", "a"]],
            ),
            (
                "transitive_with_inverse_subrole",
                "TransitiveObjectProperty(:t)\nInverseObjectProperties(:t :ti)\nSubObjectPropertyOf(:ti :t)\n\
                 ClassAssertion(:B :a)\nSubClassOf(:B ObjectSomeValuesFrom(:t :B))",
                &[["t", "a", "a"], ["ti", "a", "a"]],
            ),
            (
                "chain_with_inverse_step_self_loop",
                "SubObjectPropertyOf(ObjectPropertyChain(:r ObjectInverseOf(:r)) :c)\nClassAssertion(:B :a)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:r owl:Thing))",
                &[["c", "a", "a"]],
            ),
            (
                "nested_chains",
                "SubObjectPropertyOf(ObjectPropertyChain(:p :s) :c)\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:q1 :q2) :p)\n\
                 SubObjectPropertyOf(ObjectInverseOf(:q2) :s1)\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:s1 :s2) :s)\n\
                 SubObjectPropertyOf(ObjectInverseOf(:q1) :s2)\nClassAssertion(:B :a)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:q1 ObjectSomeValuesFrom(:q2 owl:Thing)))",
                &[["c", "a", "a"]],
            ),
            (
                "transitive_composed_with_abox",
                "TransitiveObjectProperty(:t)\nSubObjectPropertyOf(ObjectInverseOf(:u) :t)\n\
                 SubObjectPropertyOf(:u :t)\nObjectPropertyAssertion(:k :a :b)\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:k :t) :c)\nClassAssertion(:B :b)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:u owl:Thing))",
                &[["c", "a", "b"], ["t", "b", "b"]],
            ),
            (
                "same_individual_with_anonymous_loop",
                "SameIndividual(:a :b)\nClassAssertion(:B :a)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:r owl:Thing))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:r ObjectInverseOf(:r)) :c)",
                &[["c", "a", "a"], ["c", "a", "b"], ["c", "b", "a"], ["c", "b", "b"]],
            ),
            (
                "functional_merge_feeding_chain",
                "FunctionalObjectProperty(:f)\nObjectPropertyAssertion(:f :a :b)\nClassAssertion(:B :a)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:f ObjectSomeValuesFrom(:s owl:Thing)))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:f :s ObjectInverseOf(:s)) :c)",
                &[["c", "a", "b"]],
            ),
            (
                "max_cardinality_merge_feeding_chain",
                "ObjectPropertyAssertion(:f :a :b)\nClassAssertion(:B :a)\n\
                 SubClassOf(:B ObjectMaxCardinality(1 :f))\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:f ObjectSomeValuesFrom(:s owl:Thing)))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:f :s ObjectInverseOf(:s)) :c)",
                &[["c", "a", "b"]],
            ),
            (
                "inverse_functional_merge_feeding_chain",
                "InverseFunctionalObjectProperty(:f)\nObjectPropertyAssertion(:f :b :a)\nClassAssertion(:B :a)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(ObjectInverseOf(:f) ObjectSomeValuesFrom(:s owl:Thing)))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:f) :s ObjectInverseOf(:s)) :c)",
                &[["c", "a", "b"]],
            ),
            (
                "chain_ending_at_nominal",
                "ClassAssertion(:B :a)\n\
                 SubClassOf(:B ObjectSomeValuesFrom(:r ObjectSomeValuesFrom(:s ObjectOneOf(:b))))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:r :s) :c)",
                &[["c", "a", "b"]],
            ),
            (
                "chain_through_three_anonymous_levels_to_has_value",
                "ClassAssertion(:B :a)\nSubClassOf(:B ObjectSomeValuesFrom(:r :D))\n\
                 SubClassOf(:D ObjectSomeValuesFrom(:r :E))\nSubClassOf(:E ObjectSomeValuesFrom(:r :F))\n\
                 SubClassOf(:F ObjectHasValue(:s :b))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:r :r :r :s) :c)",
                &[["c", "a", "b"]],
            ),
            (
                "domain_existential_before_abox_edge",
                "ObjectPropertyDomain(:k ObjectSomeValuesFrom(:r owl:Thing))\nObjectPropertyAssertion(:k :a :b)\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:r ObjectInverseOf(:r) :k) :c)",
                &[["c", "a", "b"]],
            ),
            (
                "complex_class_assertion_excursion",
                "ClassAssertion(ObjectSomeValuesFrom(:r owl:Thing) :a)\nObjectPropertyAssertion(:k :b :a)\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:k :r ObjectInverseOf(:r)) :c)",
                &[["c", "b", "a"]],
            ),
            (
                "disjunctive_excursion",
                "ClassAssertion(:B :a)\nSubClassOf(:B ObjectUnionOf(:D :E))\n\
                 SubClassOf(:D ObjectSomeValuesFrom(:r owl:Thing))\nSubClassOf(:E ObjectSomeValuesFrom(:r owl:Thing))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:r ObjectInverseOf(:r)) :c)",
                &[["c", "a", "a"]],
            ),
            (
                "inverse_pair_under_transitive_role",
                "InverseObjectProperties(:l :r)\nSubObjectPropertyOf(:l :p)\nSubObjectPropertyOf(:r :p)\n\
                 TransitiveObjectProperty(:p)\nSubClassOf(:B ObjectSomeValuesFrom(:l owl:Thing))\nClassAssertion(:B :a)\n\
                 ObjectPropertyAssertion(:k :b :b)",
                &[["p", "a", "a"]],
            ),
            (
                "fresh_individual_has_self_from_top",
                "SubClassOf(ObjectComplementOf(:E) :E)\nSubClassOf(:E ObjectHasSelf(:s))\nClassAssertion(:B :a)\n\
                 Declaration(NamedIndividual(:e))",
                &[["s", "a", "a"], ["s", "e", "e"]],
            ),
            (
                "fresh_individual_excursion_loop",
                "SubClassOf(owl:Thing ObjectSomeValuesFrom(:r owl:Thing))\n\
                 SubObjectPropertyOf(ObjectPropertyChain(:r ObjectInverseOf(:r)) :c)\nClassAssertion(:B :a)\n\
                 Declaration(NamedIndividual(:e))",
                &[["c", "a", "a"], ["c", "e", "e"]],
            ),
            (
                "fresh_individual_functional_self",
                "SubObjectPropertyOf(ObjectInverseOf(:s0) :s0)\nInverseFunctionalObjectProperty(:s0)\n\
                 SubClassOf(ObjectMaxCardinality(1 :s0) :D)\nSubClassOf(:D ObjectHasSelf(:s1))\n\
                 ObjectPropertyAssertion(:k :a :b)\nDeclaration(NamedIndividual(:e))",
                &[["s1", "a", "a"], ["s1", "e", "e"]],
            ),
        ];
        let _test_env = crate::test_env::write();
        for (name, axioms, expect) in cases {
            assert_values_without_realize(name, axioms, expect, false);
            assert_values_without_realize(&format!("{name}_pad"), axioms, expect, true);
        }
    }

    /// Regressions from the DIFFERENT soundness work (2026-11-21). The model
    /// path must equal the exact probe path, with and without `--realize`:
    /// `g7001_0022` (a reused Skolem witness gave both functions of
    /// `≥ 2 s0.D` one element, and every merge with `a2` "clashed"),
    /// `g7002_0026` (domain `{a1}` forces `a0 = a1`) and `f4104_41`
    /// (`⊤ ⊑ =1 s3` with domain `{a0}` makes every individual `a0`).
    #[test]
    fn model_plan_matches_probes_on_skolem_witness_and_nominal_merge_cases() {
        let cases: &[(&str, &str)] = &[
            ("g7001_0022", G7001_0022),
            ("g7002_0026", G7002_0026),
            ("f4104_41", F4104_41),
            ("bare_individual", BARE_INDIVIDUAL),
            ("bare_but_constrained", BARE_BUT_CONSTRAINED),
            ("g8301_366", G8301_366),
            ("nc8302_0001", NC8302_0001),
        ];
        let _test_env = crate::test_env::write();
        let _env = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "auto");
        std::env::set_var("KM_THREADS", "1");
        let cfg = Config::from_env();
        let short = |s: &str| s.rsplit([':', '/', '#']).next().unwrap_or(s).to_string();
        for (name, ofn) in cases {
            let path = TempPath::new(&format!("-{name}.ofn"));
            std::fs::write(path.path(), ofn).unwrap();
            for mode in [None, Some(TypeMode::All)] {
                let model_ext =
                    classify_extended(&cfg, path.path(), mode, false, false, false, true, true).unwrap();
                let probe_ext = {
                    let _g = crate::routing::EnvironmentGuard::capture();
                    std::env::set_var("KM_ABOX_PROBES_ONLY", "1");
                    classify_extended(&cfg, path.path(), mode, false, false, false, true, true).unwrap()
                };
                assert_eq!(model_ext.abox.values, probe_ext.abox.values, "VALUE on {name} {mode:?}");
                assert_eq!(model_ext.abox.different, probe_ext.abox.different, "DIFFERENT on {name} {mode:?}");
                let values = model_ext.abox.values.clone().unwrap_or_default();
                let different = model_ext.abox.different.clone().unwrap_or_default();
                match *name {
                    "g7001_0022" => assert!(different.is_empty(), "{name}: {different:?}"),
                    "g7002_0026" => assert!(values
                        .iter()
                        .any(|[r, a, b]| short(r) == "t0" && short(a) == "a1" && short(b) == "a0")),
                    "f4104_41" => assert_eq!(values.len(), 6480, "{name}"),
                    "g8301_366" => assert!(
                        different.iter().any(|[a, b]| short(a) == "a2" && short(b) == "a4"),
                        "{name}: {different:?}"
                    ),
                    "nc8302_0001" => assert!(
                        !different.iter().any(|[a, b]| short(a) == "a0" && short(b) == "a8"),
                        "{name}: {different:?}"
                    ),
                    "bare_individual" => {
                        assert!(values.iter().any(|[r, a, b]| short(r) == "p" && short(a) == "a" && short(b) == "a"));
                        assert!(values.iter().all(|[_, a, b]| short(a) != "x" && short(b) != "x"), "{values:?}");
                    }
                    _ => assert!(values.iter().any(|[r, a, b]| short(r) == "p" && short(a) == "x" && short(b) == "x")),
                }
            }
        }
    }

    /// `x` is bare (only `S(x)`, and `S` constrains nothing): no rows, no
    /// probes. `p(a, a)` comes from an excursion through `l` and `r = l⁻`.
    const BARE_INDIVIDUAL: &str = "Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nOntology(<http://ex.org/bare>\n\
        Declaration(Class(:B)) Declaration(Class(:S)) Declaration(ObjectProperty(:l)) Declaration(ObjectProperty(:r))\n\
        Declaration(ObjectProperty(:p)) Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:x))\n\
        InverseObjectProperties(:l :r) SubObjectPropertyOf(:l :p) SubObjectPropertyOf(:r :p) TransitiveObjectProperty(:p)\n\
        SubClassOf(:B ObjectSomeValuesFrom(:l owl:Thing)) ClassAssertion(:B :a) ClassAssertion(:S :x)\n)";
    /// Same, but `S ⊑ ∃l.⊤` makes `x` not bare, so `p(x, x)` must be found.
    const BARE_BUT_CONSTRAINED: &str = "Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nOntology(<http://ex.org/bare2>\n\
        Declaration(Class(:B)) Declaration(Class(:S)) Declaration(ObjectProperty(:l)) Declaration(ObjectProperty(:r))\n\
        Declaration(ObjectProperty(:p)) Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:x))\n\
        InverseObjectProperties(:l :r) SubObjectPropertyOf(:l :p) SubObjectPropertyOf(:r :p) TransitiveObjectProperty(:p)\n\
        SubClassOf(:B ObjectSomeValuesFrom(:l owl:Thing)) SubClassOf(:S ObjectSomeValuesFrom(:l owl:Thing))\n\
        ClassAssertion(:B :a) ClassAssertion(:S :x)\n)";
    /// `a2 = a4` forces `a7` into the class (`≤ 1 r1` at `a4`), and
    /// `a7 != a2` is asserted: `DIFFERENT a2 a4` is entailed (HermiT agrees).
    const G8301_366: &str = r#"Prefix(:=<http://ex.org/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://ex.org/f>
Declaration(ObjectProperty(:r0))
Declaration(ObjectProperty(:r1))
Declaration(ObjectProperty(:r2))
Declaration(ObjectProperty(:r3))
Declaration(NamedIndividual(:a0))
Declaration(NamedIndividual(:a1))
Declaration(NamedIndividual(:a2))
Declaration(NamedIndividual(:a3))
Declaration(NamedIndividual(:a4))
Declaration(NamedIndividual(:a5))
Declaration(NamedIndividual(:a6))
Declaration(NamedIndividual(:a7))
Declaration(NamedIndividual(:a8))
Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:D))
Declaration(Class(:E))
Declaration(Class(:F))
SubClassOf(:A :F)
ObjectPropertyDomain(:r1 ObjectIntersectionOf(:E :A))
SubClassOf(:F ObjectAllValuesFrom(:r0 :F))
SubClassOf(ObjectUnionOf(:D :F) :E)
SubObjectPropertyOf(:r1 ObjectInverseOf(:r1))
SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(:r1) :A) :F)
SubClassOf(:E ObjectMaxCardinality(1 :r1))
DifferentIndividuals(:a7 :a2)
ClassAssertion(:D :a5)
DifferentIndividuals(:a2 :a8)
ObjectPropertyAssertion(:r1 :a2 :a2)
ObjectPropertyAssertion(:r2 :a4 :a4)
ClassAssertion(:A :a0)
ObjectPropertyAssertion(:r2 :a1 :a2)
ObjectPropertyAssertion(:r1 :a7 :a4)
ObjectPropertyAssertion(:r3 :a0 :a7)
ObjectPropertyAssertion(:r1 :a8 :a1)
ClassAssertion(:D :a1)
ObjectPropertyAssertion(:r2 :a4 :a7)
ClassAssertion(ObjectSomeValuesFrom(:r2 ObjectHasValue(:r0 :a1)) :a7)
ClassAssertion(:E :a4)
)
"#;
    /// `⊤ ⊑ {a8, a9}`: the exported model puts `a0` into the element of `a9`
    /// and `a8` with `a3`; `a9 != a3` is asserted, but `a0 != a8` is not
    /// entailed (HermiT: `O + SameIndividual(a0 a8)` is consistent).
    const NC8302_0001: &str = r#"Prefix(:=<http://ex.org/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://ex.org/nc1>
Declaration(Class(:B))
Declaration(Class(:C))
Declaration(Class(:V0))
Declaration(Class(:V1))
Declaration(Class(:V2))
Declaration(Class(:V3))
Declaration(ObjectProperty(:s0))
Declaration(ObjectProperty(:s1))
Declaration(ObjectProperty(:s2))
Declaration(ObjectProperty(:s3))
Declaration(ObjectProperty(:c0))
Declaration(ObjectProperty(:c1))
Declaration(NamedIndividual(:a0))
Declaration(NamedIndividual(:a1))
Declaration(NamedIndividual(:a2))
Declaration(NamedIndividual(:a3))
Declaration(NamedIndividual(:a4))
Declaration(NamedIndividual(:a5))
Declaration(NamedIndividual(:a6))
Declaration(NamedIndividual(:a7))
Declaration(NamedIndividual(:a8))
Declaration(NamedIndividual(:a9))
EquivalentClasses(:V1 ObjectHasValue(:s1 :a9))
ClassAssertion(:C :a8)
ObjectPropertyAssertion(:s1 :a2 :a6)
ClassAssertion(ObjectHasValue(ObjectInverseOf(:s2) :a0) :a2)
ObjectPropertyAssertion(:c0 :a4 :a8)
SubClassOf(owl:Thing ObjectOneOf(:a8 :a9))
EquivalentClasses(:V0 ObjectHasValue(:s1 :a5))
DifferentIndividuals(:a9 :a3)
SubObjectPropertyOf(ObjectPropertyChain(:s1 :s1) :c0)
ObjectPropertyAssertion(:c1 :a2 :a7)
ClassAssertion(ObjectMinCardinality(1 ObjectInverseOf(:s3) ObjectMinCardinality(1 :s0)) :a0)
EquivalentClasses(:V2 ObjectHasValue(:s1 :a4))
SubClassOf(ObjectMinCardinality(3 ObjectInverseOf(:s0) ObjectAllValuesFrom(:s3 :B)) :C)
EquivalentClasses(:V3 ObjectHasValue(:s1 :a2))
)
"#;
    const G7001_0022: &str = r#"Prefix(:=<http://ex.org/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://ex.org/g>
Declaration(ObjectProperty(:s0))
Declaration(ObjectProperty(:s1))
Declaration(ObjectProperty(:s2))
Declaration(ObjectProperty(:s3))
Declaration(ObjectProperty(:t0))
Declaration(ObjectProperty(:t1))
Declaration(ObjectProperty(:ti))
Declaration(ObjectProperty(:c0))
Declaration(ObjectProperty(:c1))
Declaration(ObjectProperty(:c2))
Declaration(NamedIndividual(:a0))
Declaration(NamedIndividual(:a1))
Declaration(NamedIndividual(:a2))
Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:D))
Declaration(Class(:E))
InverseObjectProperties(:t0 :ti)
ObjectPropertyDomain(:s3 :B)
SubObjectPropertyOf(ObjectInverseOf(:s3) :c0)
SubObjectPropertyOf(:s0 :c1)
SubClassOf(:A ObjectUnionOf(ObjectComplementOf(:E) ObjectMinCardinality(2 ObjectInverseOf(:s1) :E)))
SubClassOf(:E ObjectComplementOf(:B))
ObjectPropertyAssertion(:s1 :a1 :a0)
ClassAssertion(:E :a0)
ClassAssertion(ObjectMinCardinality(2 :s0 :D) :a2)
ClassAssertion(ObjectMaxCardinality(1 :s3) :a2)
)
"#;
    const G7002_0026: &str = r#"Prefix(:=<http://ex.org/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://ex.org/g>
Declaration(ObjectProperty(:s0))
Declaration(ObjectProperty(:s1))
Declaration(ObjectProperty(:s2))
Declaration(ObjectProperty(:s3))
Declaration(ObjectProperty(:t0))
Declaration(ObjectProperty(:t1))
Declaration(ObjectProperty(:ti))
Declaration(ObjectProperty(:c0))
Declaration(ObjectProperty(:c1))
Declaration(ObjectProperty(:c2))
Declaration(NamedIndividual(:a0))
Declaration(NamedIndividual(:a1))
Declaration(NamedIndividual(:a2))
Declaration(NamedIndividual(:a3))
Declaration(NamedIndividual(:a4))
Declaration(NamedIndividual(:a5))
Declaration(NamedIndividual(:a6))
Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:D))
Declaration(Class(:E))
SymmetricObjectProperty(:s0)
ObjectPropertyDomain(:ti ObjectSomeValuesFrom(:t1 :D))
SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:s2) :s1) :c0)
ObjectPropertyDomain(:t1 ObjectOneOf(:a1))
SubClassOf(ObjectUnionOf(:A :A) :A)
SubClassOf(:A :E)
SubClassOf(:E :A)
EquivalentClasses(:E ObjectIntersectionOf(:E :A))
DifferentIndividuals(:a2 :a6)
ObjectPropertyAssertion(:s1 :a5 :a4)
ObjectPropertyAssertion(:t0 :a0 :a1)
ObjectPropertyAssertion(:s0 :a2 :a6)
ObjectPropertyAssertion(:s1 :a1 :a5)
ObjectPropertyAssertion(:t1 :a0 :a3)
)
"#;
    const F4104_41: &str = r#"Prefix(:=<http://ex.org/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://ex.org/f>
Declaration(ObjectProperty(:s0))
Declaration(ObjectProperty(:s1))
Declaration(ObjectProperty(:s2))
Declaration(ObjectProperty(:s3))
Declaration(ObjectProperty(:c0))
Declaration(ObjectProperty(:c1))
Declaration(ObjectProperty(:p0))
Declaration(ObjectProperty(:p1))
Declaration(ObjectProperty(:p2))
Declaration(ObjectProperty(:p3))
Declaration(ObjectProperty(:p4))
Declaration(ObjectProperty(:p5))
Declaration(ObjectProperty(:p6))
Declaration(ObjectProperty(:p7))
Declaration(ObjectProperty(:p8))
Declaration(ObjectProperty(:p9))
Declaration(NamedIndividual(:a0))
Declaration(NamedIndividual(:a1))
Declaration(NamedIndividual(:a2))
Declaration(NamedIndividual(:a3))
Declaration(NamedIndividual(:a4))
Declaration(NamedIndividual(:a5))
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
Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:D))
ObjectPropertyAssertion(:c0 :a5 :a1)
ObjectPropertyAssertion(:c1 :a5 :a4)
ObjectPropertyDomain(:s3 ObjectOneOf(:a0))
InverseObjectProperties(:s1 :s0)
ClassAssertion(ObjectMaxCardinality(1 :s0) :a5)
SubClassOf(owl:Thing ObjectExactCardinality(1 :s3))
TransitiveObjectProperty(:c0)
SubClassOf(:B :D)
FunctionalObjectProperty(:s2)
ClassAssertion(ObjectHasValue(:s2 :a0) :a5)
ObjectPropertyAssertion(:p0 :z0 :z1)
)
"#;
}
