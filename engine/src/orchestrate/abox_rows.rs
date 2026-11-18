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
        for (r, role) in roles.iter().enumerate() {
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

/// Compute `--values` and `--different` directly from the exported consistency
/// model (`M_0`) when the answering route's model is canonical for the query,
/// or return `None` so the caller falls back to [`extension`] probes.
///
/// # Per-Route Canonicality Argument
///
/// * `el-canonical` (`elcomplete` / `flat_nf1`) and `cb-horn` (`Reasoner` with
///   `dropped == 0` and no unsplit multi-head disjunctions): saturation builds
///   the initial (minimal) Herbrand model `M_0` of the Horn theory. For named
///   individuals `a, b` and object property `r`, `(a, r, b) ∈ M_0` iff
///   `O ⊨ r(a, b)`, and two distinct individual elements `u ≠ v` are entailed
///   different (`O ⊨ a ≠ b`) iff identifying `u` and `v` violates an explicit
///   `DifferentIndividuals`, a disjoint/complement class pair, a negative role
///   assertion or role-disjointness/irreflexivity/asymmetry axiom, a functional
///   data property, or (inductively) a functional / inverse-functional object
///   property.
/// * `ht-bridge`: `raw.base_labels` and `raw.base_edges` record the closed
///   consistency model `base_comp` of `O` alone (before adjoining per-class
///   witness components `comp_s` for unasserted TBox classes). When `O` has no
///   DL-safe rules or `HasKey` axioms (and no small-ABox upper cardinality
///   counting puzzle), `base_comp` together with the classification's entailed
///   subsumptions and realization types is canonical for `VALUE` and
///   `DIFFERENT`.
#[allow(clippy::too_many_arguments)]
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
) -> Option<AboxRows> {
    if !classification.consistent {
        return Some(AboxRows {
            values: values_requested.then(Vec::new),
            different: different_requested.then(Vec::new),
        });
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
    if different_requested
        && individuals.len() <= 32
        && (text.contains("ObjectMaxCardinality(") || text.contains("ObjectExactCardinality("))
    {
        return None;
    }
    // When an ontology uses nominals inside TBox axioms (`ObjectOneOf` outside
    // `EquivalentClasses(<http://km.invalid/...>)`) and is tiny enough that the
    // probe path is instant, prefer the exact probe reduction.
    let probe_count = if values_requested {
        roles.len() * individuals.len()
    } else {
        0
    } + if different_requested {
        individuals.len()
    } else {
        0
    };
    if probe_count <= 64 && text.len() < 16_384 && text.contains("ObjectOneOf(") {
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
    let mut pub_individuals: Vec<String> = Vec::with_capacity(individuals.len());
    for tok in individuals {
        let pub_ind = public_name(tok);
        let exp_ind = expand_tok(tok);
        ind_lookup.insert(pub_ind.clone(), pub_ind.clone());
        ind_lookup.insert(exp_ind, pub_ind.clone());
        pub_individuals.push(pub_ind);
    }
    for (short, full) in &meta.iri_map {
        if let Some(pub_ind) = ind_lookup.get(full).cloned() {
            ind_lookup.entry(short.clone()).or_insert(pub_ind);
        }
    }

    let mut role_lookup: HashMap<String, String> = HashMap::new();
    for tok in roles {
        let pub_r = public_name(tok);
        let exp_r = expand_tok(tok);
        role_lookup.insert(pub_r.clone(), pub_r.clone());
        role_lookup.insert(exp_r, pub_r);
    }
    for (short, full) in &meta.iri_map {
        if let Some(pub_r) = role_lookup.get(full).cloned() {
            role_lookup.entry(short.clone()).or_insert(pub_r);
        }
    }
    let resolve_role_short = |tok: &str| -> String {
        let pub_r = public_name(tok);
        let exp_r = expand_tok(tok);
        for (short, full) in &meta.iri_map {
            if full == &exp_r || full == &pub_r {
                return short.clone();
            }
        }
        pub_r
    };
    let resolve_class_iri = |tok: &str| -> String {
        let exp = expand_tok(tok);
        meta.iri_map.get(&exp).cloned().unwrap_or(exp)
    };

    let use_base = raw.route == "ht-bridge" && !raw.base_labels.is_empty();
    let mut labels: Vec<Vec<String>> = if use_base {
        raw.base_labels.clone()
    } else {
        raw.labels.clone()
    };
    let mut edge_set: HashSet<(usize, String, usize)> = if use_base {
        raw.base_edges.iter().cloned().collect()
    } else {
        raw.edges.iter().cloned().collect()
    };

    let mut elem_inds: Vec<Vec<String>> = vec![Vec::new(); labels.len()];
    let mut ind_to_elem: HashMap<String, usize> = HashMap::new();
    for (u, lbl) in labels.iter().enumerate() {
        for item in lbl {
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

    // Any declared individual absent from the model's labels (e.g. a bare
    // `Declaration(NamedIndividual(a))` with no assertions) gets its own
    // unconstrained element with reflexive self-loops.
    let mut one_refl: HashSet<(usize, String, usize)> = HashSet::new();
    let _ = crate::engine::close_edges_under_rbox_rows(&meta.rbox, 1, &mut one_refl);
    let refl_roles: Vec<String> = one_refl.into_iter().map(|(_, r, _)| r).collect();
    for pub_ind in &pub_individuals {
        if !ind_to_elem.contains_key(pub_ind) {
            let u_new = labels.len();
            labels.push(vec![format!("__nom__{pub_ind}")]);
            elem_inds.push(vec![pub_ind.clone()]);
            ind_to_elem.insert(pub_ind.clone(), u_new);
            for r in &refl_roles {
                edge_set.insert((u_new, r.clone(), u_new));
            }
        }
    }

    let n_elems = labels.len();
    let mut elem_classes: Vec<HashSet<String>> = vec![HashSet::new(); n_elems];
    let mut elem_dvp: Vec<HashMap<(String, String), String>> = vec![HashMap::new(); n_elems];
    for (u, lbl) in labels.iter().enumerate() {
        for item in lbl {
            if let Some(rest) = item.strip_prefix("__dvp__") {
                // `__dvp__<group>_<bit>_<0|1>`
                if let Some((prefix, val_bit)) = rest.rsplit_once('_') {
                    if let Some((grp, bit_idx)) = prefix.rsplit_once('_') {
                        elem_dvp[u].insert((grp.to_string(), bit_idx.to_string()), val_bit.to_string());
                    }
                }
                continue;
            }
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
            elem_classes[u].insert(expand_tok(class_pub));
            elem_classes[u].insert(class_pub.clone());
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

    // Parse source ABox and TBox constraints needed for `SameIndividual`,
    // `ObjectHasValue` edges, and `DIFFERENT` rules (R1)-(R5).
    let mut same_pairs: Vec<(String, String)> = Vec::new();
    for [a, b] in &realization.same {
        same_pairs.push((a.clone(), b.clone()));
    }
    let mut diff_ind_groups: Vec<Vec<String>> = Vec::new();
    let mut disjoint_class_groups: Vec<Vec<String>> = Vec::new();
    let mut class_disjoint_inds: Vec<(String, String)> = Vec::new();
    let mut class_has_value: Vec<(String, String, bool, String)> = Vec::new();
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
    ) {
        let Node::List(head, args) = node else { return };
        let plain: Vec<&Node<'a>> = args
            .iter()
            .filter(|a| a.head() != Some("Annotation"))
            .collect();
        match *head {
            "ObjectIntersectionOf" => {
                for op in plain {
                    collect_has_value_rhs(op, out);
                }
            }
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
                    collect_has_value_rhs(plain[1], &mut hvs);
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
                            collect_has_value_rhs(plain[j], &mut hvs);
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
                        if let Node::List("ObjectComplementOf", inner) = plain[0] {
                            if let Some(c) = inner.first().and_then(Node::as_atom) {
                                elem_neg_classes[u].insert(resolve_class_iri(c));
                            }
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

    // Materialize `C ⊑ ∃r.{b}` edges for elements carrying `C`, then close under
    // the RBox and propagate domain/range classes on `elem_classes`.
    if !class_has_value.is_empty() {
        let mut added = false;
        for u in 0..n_elems {
            for (c_iri, r_short, inv, target_ind) in &class_has_value {
                if elem_classes[u].contains(c_iri) {
                    if let Some(&v) = ind_to_elem.get(target_ind) {
                        let edge = if *inv {
                            (v, r_short.clone(), u)
                        } else {
                            (u, r_short.clone(), v)
                        };
                        if edge_set.insert(edge) {
                            added = true;
                        }
                    }
                }
            }
        }
        if added {
            let _ = crate::engine::close_edges_under_rbox_rows(&meta.rbox, n_elems, &mut edge_set);
        }
    }
    let mut dom_ran_added = false;
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
    for (owner_iri, prop_iri, lit) in &raw.extra_values {
        if let Some(&u) = ind_lookup
            .get(owner_iri)
            .and_then(|pub_i| ind_to_elem.get(pub_i))
        {
            source_data_assertions.push((u, expand_tok(prop_iri), lit.clone()));
        }
    }
    // Close data assertions upwards under `SubDataPropertyOf`
    let mut closed_data_assertions: Vec<(usize, String, String)> = Vec::new();
    for (u, p, lit) in source_data_assertions {
        let mut stack = vec![p];
        let mut seen = HashSet::new();
        while let Some(cur) = stack.pop() {
            if seen.insert(cur.clone()) {
                for (dp, dc) in &data_domains {
                    if &cur == dp && elem_classes[u].insert(dc.clone()) {
                        dom_ran_added = true;
                    }
                }
                closed_data_assertions.push((u, cur.clone(), lit.clone()));
                if let Some(sups) = sub_data_props.get(&cur) {
                    stack.extend(sups.iter().cloned());
                }
            }
        }
    }
    if dom_ran_added {
        close_elem_classes(&mut elem_classes);
    }

    let values_out = if values_requested {
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
        let mut v_rows: BTreeSet<[String; 3]> = BTreeSet::new();
        for (u, r, v) in &edge_set {
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
                        v_rows.insert([pub_r.clone(), a.clone(), b.clone()]);
                    }
                }
            } else {
                for a in &elem_inds[*u] {
                    for b in &elem_inds[*u] {
                        if a == b
                            || use_base
                            || same_comp.get(a.as_str()) == same_comp.get(b.as_str())
                        {
                            v_rows.insert([pub_r.clone(), a.clone(), b.clone()]);
                        }
                    }
                }
            }
        }
        Some(v_rows.into_iter().collect())
    } else {
        None
    };

    let different_out = if different_requested {
        let pair_key = |u: usize, v: usize| -> (usize, usize) { (u.min(v), u.max(v)) };
        let mut diff: HashSet<(usize, usize)> = HashSet::new();

        // (R1) Explicit `DifferentIndividuals`
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

        // (R2) Disjoint / complement classes and `__dvp__` binary projection digits
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
        let ind_elems: Vec<usize> = (0..n_elems)
            .filter(|&u| !elem_inds[u].is_empty())
            .collect();
        if !disjoint_pairs.is_empty() {
            let mut class_to_elems: HashMap<&str, Vec<usize>> = HashMap::new();
            for u in 0..n_elems {
                for c in &elem_classes[u] {
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
                for u in 0..n_elems {
                    if u != v && elem_classes[u].contains(c_iri) {
                        diff.insert(pair_key(u, v));
                    }
                }
            }
        }
        for u in 0..n_elems {
            if !elem_neg_classes[u].is_empty() {
                for neg_c in &elem_neg_classes[u] {
                    for v in 0..n_elems {
                        if u != v && elem_classes[v].contains(neg_c) {
                            diff.insert(pair_key(u, v));
                        }
                    }
                }
            }
        }
        for i in 0..ind_elems.len() {
            let u = ind_elems[i];
            if elem_dvp[u].is_empty() {
                continue;
            }
            for &v in &ind_elems[(i + 1)..] {
                if elem_dvp[u]
                    .iter()
                    .any(|(k, b1)| elem_dvp[v].get(k).is_some_and(|b2| b1 != b2))
                {
                    diff.insert(pair_key(u, v));
                }
            }
        }

        // (R3) Negative role assertions, irreflexive/asymmetric/disjoint object roles
        for &(ref r, ua, ub) in &neg_role_assertions {
            for &(u, ref er, v) in &edge_set {
                if er == r {
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
            for &(u, ref r, v) in &edge_set {
                if u != v && (irrefl_roles.contains(r) || asym_roles.contains(r)) {
                    diff.insert(pair_key(u, v));
                }
            }
        }
        if !disjoint_role_groups.is_empty() {
            let mut edges_by_role: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
            for &(u, ref r, v) in &edge_set {
                edges_by_role.entry(r.as_str()).or_default().push((u, v));
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
                        for &(u1, v1) in e1 {
                            for &(u2, v2) in e2 {
                                if u1 == u2 && v1 != v2 {
                                    diff.insert(pair_key(v1, v2));
                                }
                                if v1 == v2 && u1 != u2 {
                                    diff.insert(pair_key(u1, u2));
                                }
                                if u1 == v2 && v1 != u2 && (u1 == v1 || u2 == v2) {
                                    diff.insert(pair_key(u1, v1));
                                }
                            }
                        }
                    }
                }
            }
        }

        // (R4) Functional data properties
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
                            if crate::frontend::datatypes::bridge_exact_value_equal(&k1, &k2)
                                != Some(true)
                            {
                                diff.insert(pair_key(u1, u2));
                            }
                        }
                    }
                }
            }
        }

        // (R5) Fixpoint propagation under functional and inverse-functional object properties
        if (!func_obj_roles.is_empty() || !inv_func_obj_roles.is_empty()) && !diff.is_empty() {
            let mut func_edges: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
            let mut inv_func_edges: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
            for &(u, ref r, v) in &edge_set {
                if func_obj_roles.contains(r.as_str()) {
                    func_edges.entry(r.as_str()).or_default().push((u, v));
                }
                if inv_func_obj_roles.contains(r.as_str()) {
                    inv_func_edges.entry(r.as_str()).or_default().push((u, v));
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

        let mut d_rows: BTreeSet<[String; 2]> = BTreeSet::new();
        for (u, v) in diff {
            if u < n_elems && v < n_elems {
                for a in &elem_inds[u] {
                    for b in &elem_inds[v] {
                        if a != b {
                            let (x, y) = if a < b { (a, b) } else { (b, a) };
                            d_rows.insert([x.clone(), y.clone()]);
                        }
                    }
                }
            }
        }
        Some(d_rows.into_iter().collect())
    } else {
        None
    };

    Some(AboxRows {
        values: values_out,
        different: different_out,
    })
}
