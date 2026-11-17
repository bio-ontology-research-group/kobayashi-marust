//! `km classify --export-model FILE [--export-model-budget SECONDS]`: a model of
//! the ontology over source names, as JSON lines (`docs/MODEL-EXPORT.md`).
//!
//! When `--export-model` is active during `km classify`, the answering route
//! records its terminal saturation or completion state directly (`el-canonical`
//! from `elcomplete` or `flat_nf1`, `ht-bridge` from `konclude_ht::bridge`,
//! `cb-horn` from `Reasoner::saturate_inner`) and `finish_and_write` formats
//! that captured state without re-parsing or re-classifying the ontology.
//! When `export` is called standalone (e.g., from unit tests), it runs the
//! answering route once under `KM_EXPORT_MODEL_ACTIVE=1` and writes the model.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use super::config::Config;
use super::{cb_to_ht, frontend_run, OrchestrateError};

/// Serialized model payload written by a worker subprocess (when
/// `KM_WORKER_MODEL_OUT` is set) or held in memory by an in-process worker.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub(crate) enum WorkerModelPayload {
    El(Result<crate::elcomplete::ElModel, String>),
    Bridge(Result<crate::konclude_ht::bridge::BridgeExportModel, String>),
    Cb(Result<crate::engine::CbExportModel, String>),
    Declined(String),
}

/// A model over internal (clause-stream) names, before the source mapping.
pub(crate) struct RawModel {
    pub route: &'static str,
    /// Internal context or node name per element (for the `context` field).
    pub contexts: Vec<String>,
    pub labels: Vec<Vec<String>>,
    pub edges: Vec<(usize, String, usize)>,
    /// `(element, blocker)` for a finite representation with blocking.
    pub blocked: Vec<(usize, usize)>,
    /// Whether every satisfiable class witness satisfies only its entailed
    /// superclasses.
    pub witness_exact: bool,
    /// Per-class exactness override when individual witnesses differ.
    pub witness_exact_by_class: BTreeMap<String, bool>,
    /// Named class (internal name) to its witness element.
    pub witnesses: BTreeMap<String, usize>,
    /// Additional split-witness elements for classes whose superclasses are
    /// separated across multiple elements (covering unions).
    pub extra_witnesses: Vec<(String, usize)>,
    /// The role closure a consumer must apply to the edges.
    pub closure: &'static str,
    /// Present when `--export-model-budget` expired before all per-class
    /// witnesses were constructed (`"status": "partial"`).
    pub partial_reason: Option<String>,
    /// Projected data-property assertions `(owner_iri, prop_iri, literal)` from
    /// `data_abox_projection`.
    pub extra_values: Vec<(String, String, String)>,
}

#[derive(Default)]
struct ExportSession {
    budget_secs: Option<f64>,
    inconsistent: bool,
    declined_reason: Option<String>,
    flat_nf1_state: Option<super::flat_nf1::FlatNf1ExportState>,
    engine_meta: Option<frontend_run::Meta>,
    worker_model_path: Option<PathBuf>,
    worker_model_payload: Option<Arc<WorkerModelPayload>>,
    unsat_iris: Vec<String>,
    inproc_payload: Option<WorkerModelPayload>,
    projected_data_assertions: Vec<(String, String, String)>,
    abox_quotient_atomic: Option<Vec<(String, String)>>,
    abox_quotient_blocks: Option<Vec<(String, Vec<String>)>>,
    positive_abox_quotient_comps: Option<Vec<Vec<String>>>,
    mirror_specs: Option<Vec<(String, String, Option<String>)>>,
}

static SESSION: Mutex<ExportSession> = Mutex::new(ExportSession {
    budget_secs: None,
    inconsistent: false,
    declined_reason: None,
    flat_nf1_state: None,
    engine_meta: None,
    worker_model_path: None,
    worker_model_payload: None,
    unsat_iris: Vec::new(),
    inproc_payload: None,
    projected_data_assertions: Vec::new(),
    abox_quotient_atomic: None,
    abox_quotient_blocks: None,
    positive_abox_quotient_comps: None,
    mirror_specs: None,
});

/// Arm model export before `km classify` runs so the answering route captures
/// its live state directly.
pub fn begin_session(budget_secs: Option<f64>) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    *g = ExportSession {
        budget_secs,
        ..Default::default()
    };
    std::env::set_var("KM_EXPORT_MODEL_ACTIVE", "1");
    if let Some(b) = budget_secs {
        std::env::set_var("KM_EXPORT_MODEL_BUDGET_S", b.to_string());
    } else {
        std::env::remove_var("KM_EXPORT_MODEL_BUDGET_S");
    }
}

pub(crate) fn write_worker_model_payload_if_requested(payload: &WorkerModelPayload) {
    if let Some(path) = std::env::var_os("KM_WORKER_MODEL_OUT") {
        if let Ok(file) = std::fs::File::create(path) {
            let mut w = std::io::BufWriter::new(file);
            let _ = serde_json::to_writer(&mut w, payload);
            let _ = w.flush();
        }
    } else if std::env::var_os("KM_EXPORT_MODEL_ACTIVE").is_some() {
        let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
        g.inproc_payload = Some(payload.clone());
    }
}

pub(crate) fn take_inproc_worker_payload() -> Option<WorkerModelPayload> {
    if std::env::var_os("KM_EXPORT_MODEL_ACTIVE").is_none() {
        return None;
    }
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.inproc_payload.take()
}

pub(crate) fn worker_model_sidecar_if_exists(stdout_path: &Path) -> Option<PathBuf> {
    if std::env::var_os("KM_EXPORT_MODEL_ACTIVE").is_none() {
        return None;
    }
    let mut p = stdout_path.as_os_str().to_os_string();
    p.push(".model");
    let pb = PathBuf::from(p);
    pb.is_file().then_some(pb)
}

pub(crate) fn record_flat_nf1_state(state: super::flat_nf1::FlatNf1ExportState) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.flat_nf1_state = Some(state);
}

pub(crate) fn record_inconsistent() {
    if std::env::var_os("KM_EXPORT_MODEL_ACTIVE").is_none() {
        return;
    }
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.inconsistent = true;
}

pub(crate) fn record_declined(reason: String) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.declined_reason = Some(reason);
}

pub(crate) fn record_engine_out(
    meta: frontend_run::Meta,
    worker_model_path: Option<PathBuf>,
    worker_model_payload: Option<Arc<WorkerModelPayload>>,
    unsat_iris: &[String],
) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.inconsistent = false;
    g.declined_reason = None;
    g.engine_meta = Some(meta);
    g.worker_model_path = worker_model_path;
    g.worker_model_payload =
        worker_model_payload.or_else(|| g.inproc_payload.take().map(Arc::new));
    g.unsat_iris = unsat_iris.to_vec();
}

pub(crate) fn record_symbolic_source_export(meta: frontend_run::Meta, consistent: bool) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    if !consistent {
        g.inconsistent = true;
    } else {
        g.inconsistent = false;
        g.declined_reason = None;
        g.engine_meta = Some(meta);
        g.worker_model_payload = g.inproc_payload.take().map(Arc::new);
    }
}

pub(crate) fn record_projected_data_assertions(values: Vec<(String, String, String)>) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.projected_data_assertions = values;
}

pub(crate) fn record_abox_quotient_atomic(pairs: Vec<(String, String)>) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.abox_quotient_atomic = Some(pairs);
    g.abox_quotient_blocks = None;
}

pub(crate) fn record_abox_quotient_blocks(blocks: Vec<(String, Vec<String>)>) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.abox_quotient_blocks = Some(blocks);
    g.abox_quotient_atomic = None;
}

pub(crate) fn clear_abox_quotient() {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.abox_quotient_atomic = None;
    g.abox_quotient_blocks = None;
}

pub(crate) fn record_positive_abox_quotient_components(comps: Vec<Vec<String>>) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.positive_abox_quotient_comps = Some(comps);
}

pub(crate) fn clear_positive_abox_quotient() {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.positive_abox_quotient_comps = None;
}

pub(crate) fn record_mirror_spec(specs: Vec<(String, String, Option<String>)>) {
    let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
    g.mirror_specs = Some(specs);
}

fn line<W: Write>(w: &mut W, value: serde_json::Value) -> std::io::Result<()> {
    serde_json::to_writer(&mut *w, &value)?;
    w.write_all(b"\n")
}

fn build_raw_model_from_el(
    m: crate::elcomplete::ElModel,
    rbox: &[Vec<String>],
) -> Result<Option<RawModel>, String> {
    if m.inconsistent {
        return Ok(None);
    }
    let mut edge_set: HashSet<(usize, String, usize)> = m.edges.into_iter().collect();
    crate::engine::close_edges_under_rbox_rows(rbox, m.contexts.len(), &mut edge_set)?;
    let mut edges: Vec<(usize, String, usize)> = edge_set.into_iter().collect();
    edges.sort();
    let witnesses: BTreeMap<String, usize> = m
        .contexts
        .iter()
        .enumerate()
        .map(|(i, c)| (c.clone(), i))
        .collect();
    let witness_exact_by_class = witnesses.keys().map(|k| (k.clone(), true)).collect();
    Ok(Some(RawModel {
        route: "el-canonical",
        contexts: m.contexts,
        labels: m.labels,
        edges,
        blocked: Vec::new(),
        witness_exact: true,
        witness_exact_by_class,
        witnesses,
        extra_witnesses: Vec::new(),
        closure: "none: the edges of each role are its extension (sub-roles lifted, chains and transitivity composed)",
        partial_reason: m.partial_reason,
        extra_values: Vec::new(),
    }))
}

fn build_raw_model_from_cb(m: crate::engine::CbExportModel) -> Option<RawModel> {
    if m.inconsistent {
        return None;
    }
    let witnesses: BTreeMap<String, usize> = m
        .contexts
        .iter()
        .enumerate()
        .map(|(i, c)| (c.clone(), i))
        .collect();
    let witness_exact_by_class = witnesses.keys().map(|k| (k.clone(), true)).collect();
    Some(RawModel {
        route: "cb-horn",
        contexts: m.contexts,
        labels: m.labels,
        edges: m.edges,
        blocked: Vec::new(),
        witness_exact: true,
        witness_exact_by_class,
        witnesses,
        extra_witnesses: Vec::new(),
        closure: "none: the edges of each role are closed under the RBox (sub-roles, inverses, symmetry, reflexivity, transitivity, and role chains)",
        partial_reason: m.partial_reason,
        extra_values: Vec::new(),
    })
}

fn build_raw_model_from_bridge(
    mut bm: crate::konclude_ht::bridge::BridgeExportModel,
    rbox: &[Vec<String>],
    nominal_abox: &crate::json_io::NominalAboxMeta,
) -> Result<Option<RawModel>, String> {
    if bm.inconsistent {
        return Ok(None);
    }
    if !nominal_abox.same.is_empty() {
        let mut changed = true;
        while changed {
            changed = false;
            for (a, b) in &nominal_abox.same {
                let na = format!("__nom__{a}");
                let nb = format!("__nom__{b}");
                for lbl in &mut bm.labels {
                    let has_a = lbl.contains(&na);
                    let has_b = lbl.contains(&nb);
                    if has_a && !has_b {
                        lbl.push(nb.clone());
                        lbl.sort();
                        changed = true;
                    } else if has_b && !has_a {
                        lbl.push(na.clone());
                        lbl.sort();
                        changed = true;
                    }
                }
            }
        }
    }
    let mut edge_set: HashSet<(usize, String, usize)> = bm.edges.into_iter().collect();
    crate::engine::close_edges_under_rbox_rows(rbox, bm.contexts.len(), &mut edge_set)?;
    let mut edges: Vec<(usize, String, usize)> = edge_set.into_iter().collect();
    edges.sort();

    let mut witnesses = BTreeMap::new();
    let mut extra_witnesses = Vec::new();
    let mut witness_exact_by_class = BTreeMap::new();
    let mut all_exact = true;
    for (cname, elem_idx, exact) in bm.class_witnesses {
        if let std::collections::btree_map::Entry::Vacant(e) = witnesses.entry(cname.clone()) {
            e.insert(elem_idx);
            witness_exact_by_class.insert(cname, exact);
        } else {
            extra_witnesses.push((cname, elem_idx));
        }
        if !exact {
            all_exact = false;
        }
    }
    let closure = if bm.blocked.is_empty() {
        "none: the edges of each role are closed under the RBox (sub-roles, inverses, symmetry, reflexivity, transitivity, and role chains)"
    } else {
        "unravelling of blocked nodes along blocker edges, closed under the RBox"
    };
    Ok(Some(RawModel {
        route: "ht-bridge",
        contexts: bm.contexts,
        labels: bm.labels,
        edges,
        blocked: bm.blocked,
        witness_exact: all_exact,
        witness_exact_by_class,
        witnesses,
        extra_witnesses,
        closure,
        partial_reason: bm.partial_reason,
        extra_values: Vec::new(),
    }))
}

fn build_raw_model_from_flat_nf1(
    state: super::flat_nf1::FlatNf1ExportState,
) -> Result<(RawModel, frontend_run::Meta), String> {
    let n_classes = state.names.len();
    let is_bottom = |s: &str| {
        matches!(
            s,
            "owl:Nothing" | "Nothing" | "⊥" | "http://www.w3.org/2002/07/owl#Nothing"
        )
    };
    let is_top = |s: &str| {
        matches!(
            s,
            "owl:Thing" | "Thing" | "⊤" | "http://www.w3.org/2002/07/owl#Thing"
        )
    };
    let top_id = (0..n_classes).find(|&i| is_top(state.names[i].as_ref()));

    let mut seen = vec![0u32; n_classes];
    let mut gen = 0u32;
    let mut stack: Vec<u32> = Vec::new();
    let has_union_rules = !state.union_rules.is_empty();

    let mut close_classes = |seeds: &[u32]| -> (Vec<u32>, bool) {
        gen = gen.wrapping_add(1);
        if gen == 0 {
            seen.fill(0);
            gen = 1;
        }
        let mut reached: Vec<u32> = Vec::new();
        stack.clear();
        for &s in seeds {
            if (s as usize) < n_classes && seen[s as usize] != gen {
                seen[s as usize] = gen;
                reached.push(s);
                stack.push(s);
            }
        }
        if let Some(tid) = top_id {
            if seen[tid] != gen {
                seen[tid] = gen;
                reached.push(tid as u32);
                stack.push(tid as u32);
            }
        }
        let mut chose_disjunct = false;
        loop {
            while let Some(cur) = stack.pop() {
                if let Some(sups) = state.outgoing.get(cur as usize) {
                    for &nxt in sups {
                        if (nxt as usize) < n_classes && seen[nxt as usize] != gen {
                            seen[nxt as usize] = gen;
                            reached.push(nxt);
                            stack.push(nxt);
                        }
                    }
                }
            }
            if !has_union_rules {
                break;
            }
            let mut added_alt = false;
            for (defined, alternatives) in &state.union_rules {
                if (*defined as usize) < n_classes
                    && seen[*defined as usize] == gen
                    && !alternatives
                        .iter()
                        .any(|&alt| (alt as usize) < n_classes && seen[alt as usize] == gen)
                {
                    if let Some(&alt) = alternatives.first() {
                        if (alt as usize) < n_classes && seen[alt as usize] != gen {
                            seen[alt as usize] = gen;
                            reached.push(alt);
                            stack.push(alt);
                            added_alt = true;
                            chose_disjunct = true;
                        }
                    }
                }
            }
            if !added_alt {
                break;
            }
        }
        (reached, !chose_disjunct)
    };

    let need_elem_reached = !state.existentials.is_empty();
    let mut contexts: Vec<String> = Vec::with_capacity(n_classes + 1);
    let mut labels: Vec<Vec<String>> = Vec::with_capacity(n_classes + 1);
    let mut elem_reached: Vec<Vec<u32>> =
        Vec::with_capacity(if need_elem_reached { n_classes + 1 } else { 0 });
    let mut class_to_elem: Vec<Option<usize>> = vec![None; n_classes];
    let mut witnesses: BTreeMap<String, usize> = BTreeMap::new();
    let mut witness_exact_by_class: BTreeMap<String, bool> = BTreeMap::new();
    let mut all_exact = true;

    // Ensure element 0 is `⊤`
    let top_seeds: Vec<u32> = top_id.map(|i| vec![i as u32]).unwrap_or_default();
    let (top_reached, _) = close_classes(&top_seeds);
    contexts.push("⊤".to_string());
    labels.push(
        top_reached
            .iter()
            .map(|&id| state.names[id as usize].to_string())
            .collect(),
    );
    if need_elem_reached {
        elem_reached.push(top_reached);
    }
    if let Some(tid) = top_id {
        class_to_elem[tid] = Some(0);
    }

    for cid in 0..n_classes {
        let cname = state.names[cid].as_ref();
        if is_bottom(cname) || is_top(cname) {
            continue;
        }
        let (reached, is_exact) = close_classes(&[cid as u32]);
        if reached.iter().any(|&id| is_bottom(state.names[id as usize].as_ref())) {
            continue;
        }
        if !is_exact {
            all_exact = false;
        }
        let u = contexts.len();
        contexts.push(cname.to_string());
        labels.push(
            reached
                .iter()
                .map(|&id| state.names[id as usize].to_string())
                .collect(),
        );
        if need_elem_reached {
            elem_reached.push(reached);
        }
        class_to_elem[cid] = Some(u);
        witnesses.insert(cname.to_string(), u);
        if !is_exact {
            witness_exact_by_class.insert(cname.to_string(), false);
        }
    }

    let mut edge_set: HashSet<(usize, String, usize)> = HashSet::new();

    if !state.individuals.is_empty() {
        if state.class_assertions.is_empty() && state.existential_assertions.is_empty() {
            // `classify_reader` with positive separable ABox: 1 universal positive element
            let u_abox = contexts.len();
            contexts.push(format!("__nom__{}", state.individuals[0]));
            let mut lbl: Vec<String> = state
                .names
                .iter()
                .map(|s| s.to_string())
                .filter(|s| !is_bottom(s) && !is_top(s))
                .collect();
            for ind in &state.individuals {
                lbl.push(format!("__nom__{ind}"));
            }
            lbl.sort();
            lbl.dedup();
            labels.push(lbl);
            if need_elem_reached {
                elem_reached.push(Vec::new());
            }
            for r_name in &state.role_names {
                edge_set.insert((u_abox, r_name.to_string(), u_abox));
            }
        } else {
            let mut ind_classes: HashMap<&str, Vec<u32>> = HashMap::new();
            for (ind, cid) in &state.class_assertions {
                ind_classes.entry(ind.as_str()).or_default().push(*cid);
            }
            let mut ind_exists: HashMap<&str, Vec<(&str, u32)>> = HashMap::new();
            for (ind, r_name, fid) in &state.existential_assertions {
                ind_exists
                    .entry(ind.as_str())
                    .or_default()
                    .push((r_name.as_str(), *fid));
            }
            for ind in &state.individuals {
                let seeds = ind_classes.get(ind.as_str()).map(Vec::as_slice).unwrap_or(&[]);
                let (reached, _) = close_classes(seeds);
                let u_ind = contexts.len();
                contexts.push(format!("__nom__{ind}"));
                let mut lbl: Vec<String> = reached
                    .iter()
                    .map(|&id| state.names[id as usize].to_string())
                    .collect();
                lbl.push(format!("__nom__{ind}"));
                lbl.sort();
                lbl.dedup();
                labels.push(lbl);
                if need_elem_reached {
                    elem_reached.push(reached);
                }
                if let Some(exs) = ind_exists.get(ind.as_str()) {
                    for &(r_name, fid) in exs {
                        if let Some(Some(f_elem)) = class_to_elem.get(fid as usize) {
                            edge_set.insert((u_ind, r_name.to_string(), *f_elem));
                        }
                    }
                }
            }
        }
    }

    // Add existential edges for every element whose `reached` contains `sub_id`
    if need_elem_reached {
        let mut by_sub: HashMap<u32, Vec<(&str, u32)>> = HashMap::new();
        for (sub_id, r_name, filler_id) in &state.existentials {
            by_sub
                .entry(*sub_id)
                .or_default()
                .push((r_name.as_str(), *filler_id));
        }
        for (u, reached) in elem_reached.iter().enumerate() {
            for &cid in reached {
                if let Some(exs) = by_sub.get(&cid) {
                    for &(r_name, fid) in exs {
                        if let Some(Some(f_elem)) = class_to_elem.get(fid as usize) {
                            edge_set.insert((u, r_name.to_string(), *f_elem));
                        }
                    }
                }
            }
        }
    }

    crate::engine::close_edges_under_rbox_rows(&state.rbox_rows, contexts.len(), &mut edge_set)?;
    let mut edges: Vec<(usize, String, usize)> = edge_set.into_iter().collect();
    edges.sort();

    let mut iri_map = BTreeMap::new();
    let mut named = Vec::with_capacity(state.names.len());
    for n in &state.names {
        let s = n.to_string();
        if !is_bottom(&s) && !is_top(&s) {
            iri_map.insert(s.clone(), s.clone());
            named.push(s);
        }
    }
    for r in &state.role_names {
        let rs = r.to_string();
        iri_map.insert(rs.clone(), rs);
    }
    for ind in &state.individuals {
        iri_map.insert(ind.clone(), ind.clone());
    }
    let meta = frontend_run::Meta {
        iri_map,
        named: named.clone(),
        declared: named,
        el_rbox_safe: true,
        rbox: state.rbox_rows,
        ..Default::default()
    };
    let raw = RawModel {
        route: "el-canonical",
        contexts,
        labels,
        edges,
        blocked: Vec::new(),
        witness_exact: all_exact,
        witness_exact_by_class,
        witnesses,
        extra_witnesses: Vec::new(),
        closure: "none: the edges of each role are its extension (sub-roles lifted, chains and transitivity composed)",
        partial_reason: None,
        extra_values: Vec::new(),
    };
    Ok((raw, meta))
}

fn duplicate_elements_batch(
    raw: &mut RawModel,
    copies: Vec<(usize, String, Vec<String>)>,
) -> Vec<usize> {
    if copies.is_empty() {
        return Vec::new();
    }
    let mut src_to_new: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut base_labels: HashMap<usize, Vec<String>> = HashMap::new();
    let mut out_indices = Vec::with_capacity(copies.len());
    for (src_elem, new_context, extra_labels) in copies {
        let base = base_labels.entry(src_elem).or_insert_with(|| {
            raw.labels[src_elem]
                .iter()
                .filter(|s| !s.starts_with(NOMINAL_PREFIX))
                .cloned()
                .collect()
        });
        let u_new = raw.contexts.len();
        raw.contexts.push(new_context);
        let mut lbl = base.clone();
        lbl.extend(extra_labels);
        lbl.sort();
        lbl.dedup();
        raw.labels.push(lbl);
        src_to_new.entry(src_elem).or_default().push(u_new);
        out_indices.push(u_new);
    }
    let n_edges = raw.edges.len();
    let mut new_edges: Vec<(usize, String, usize)> = Vec::new();
    for i in 0..n_edges {
        let (f, ref r, t) = raw.edges[i];
        if f == t {
            if let Some(news) = src_to_new.get(&f) {
                for &u_new in news {
                    new_edges.push((u_new, r.clone(), u_new));
                }
            }
        } else {
            if let Some(news) = src_to_new.get(&f) {
                for &u_new in news {
                    new_edges.push((u_new, r.clone(), t));
                }
            }
            if let Some(news) = src_to_new.get(&t) {
                for &u_new in news {
                    new_edges.push((f, r.clone(), u_new));
                }
            }
        }
    }
    raw.edges.extend(new_edges);
    let n_blocked = raw.blocked.len();
    for i in 0..n_blocked {
        let (e, b) = raw.blocked[i];
        if let Some(news) = src_to_new.get(&e) {
            for &u_new in news {
                raw.blocked.push((u_new, b));
            }
        }
    }
    out_indices
}

fn apply_post_hooks(
    raw: &mut RawModel,
    meta: &mut frontend_run::Meta,
    unsat_iris: &[String],
    projected_data_assertions: &[(String, String, String)],
    abox_quotient_atomic: Option<&[(String, String)]>,
    abox_quotient_blocks: Option<&[(String, Vec<String>)]>,
    positive_abox_quotient_comps: Option<&[Vec<String>]>,
    mirror_specs: Option<&[(String, String, Option<String>)]>,
) -> Result<(), String> {
    let unsat_set: HashSet<&str> = unsat_iris.iter().map(String::as_str).collect();

    // 1. Separable ABox elided by `omit_separable_abox` in `frontend/mod.rs`
    if let Some(sep) = meta.separable_abox_export.take() {
        let mut need_rbox_close = false;
        if !sep.atomic_individual_classes.is_empty() {
            let mut label_first_elem: Option<HashMap<String, usize>> = None;
            let mut class_cache: HashMap<String, usize> = HashMap::new();
            let mut touched_elems: Vec<usize> = Vec::new();
            for (ind_short, class_short) in sep.atomic_individual_classes {
                let elem = if let Some(&cached) = class_cache.get(&class_short) {
                    cached
                } else {
                    let found = raw
                        .witnesses
                        .get(&class_short)
                        .copied()
                        .or_else(|| {
                            let idx = label_first_elem.get_or_insert_with(|| {
                                let mut m = HashMap::new();
                                for (u, lbl) in raw.labels.iter().enumerate() {
                                    for c in lbl {
                                        m.entry(c.clone()).or_insert(u);
                                    }
                                }
                                m
                            });
                            idx.get(&class_short).copied()
                        })
                        .unwrap_or(0);
                    class_cache.insert(class_short.clone(), found);
                    found
                };
                raw.labels[elem].push(format!("{NOMINAL_PREFIX}{ind_short}"));
                touched_elems.push(elem);
            }
            touched_elems.sort_unstable();
            touched_elems.dedup();
            for elem in touched_elems {
                raw.labels[elem].sort();
                raw.labels[elem].dedup();
            }
        } else if sep.top_identity_separable {
            let copies: Vec<(usize, String, Vec<String>)> = sep
                .ind_components
                .into_iter()
                .filter(|comp| !comp.is_empty())
                .map(|comp| {
                    let ctx_name = format!("{NOMINAL_PREFIX}{}", comp[0]);
                    let noms = comp.into_iter().map(|i| format!("{NOMINAL_PREFIX}{i}")).collect();
                    (0, ctx_name, noms)
                })
                .collect();
            duplicate_elements_batch(raw, copies);
        } else if sep.positive_separable && !sep.ind_components.is_empty() {
            let sat_classes: Vec<String> = meta
                .named
                .iter()
                .chain(meta.declared.iter())
                .filter(|s| {
                    !matches!(
                        s.as_str(),
                        "owl:Thing" | "Thing" | "owl:Nothing" | "Nothing" | "⊤" | "⊥"
                    ) && !meta
                        .iri_map
                        .get(*s)
                        .is_some_and(|iri| iri.starts_with("_:") || unsat_set.contains(iri.as_str()))
                })
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let start_u = raw.contexts.len();
            for comp in sep.ind_components {
                if comp.is_empty() {
                    continue;
                }
                let mut lbl = sat_classes.clone();
                for ind in &comp {
                    lbl.push(format!("{NOMINAL_PREFIX}{ind}"));
                }
                lbl.sort();
                lbl.dedup();
                raw.contexts.push(format!("{NOMINAL_PREFIX}{}", comp[0]));
                raw.labels.push(lbl);
            }
            let end_u = raw.contexts.len();
            for u1 in start_u..end_u {
                for u2 in start_u..end_u {
                    for r in &sep.object_roles {
                        raw.edges.push((u1, r.clone(), u2));
                    }
                }
            }
            need_rbox_close = true;
        } else if !sep.existential_assertions.is_empty() {
            let mut by_ind: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
            for (ind, role, filler) in sep.existential_assertions {
                by_ind.entry(ind).or_default().push((role, filler));
            }
            let mut ordered_assertions = Vec::with_capacity(by_ind.len());
            let mut copies = Vec::with_capacity(by_ind.len());
            for (ind, assertions) in by_ind {
                copies.push((
                    0,
                    format!("{NOMINAL_PREFIX}{ind}"),
                    vec![format!("{NOMINAL_PREFIX}{ind}")],
                ));
                ordered_assertions.push(assertions);
            }
            let new_elems = duplicate_elements_batch(raw, copies);
            let mut label_first_elem: Option<HashMap<String, usize>> = None;
            let mut filler_cache: HashMap<String, usize> = HashMap::new();
            for (u_ind, assertions) in new_elems.into_iter().zip(ordered_assertions) {
                for (role, filler) in assertions {
                    let w = if let Some(&cached) = filler_cache.get(&filler) {
                        cached
                    } else {
                        let found = raw
                            .witnesses
                            .get(&filler)
                            .copied()
                            .or_else(|| {
                                let idx = label_first_elem.get_or_insert_with(|| {
                                    let mut m = HashMap::new();
                                    for (u, lbl) in raw.labels.iter().enumerate() {
                                        for c in lbl {
                                            m.entry(c.clone()).or_insert(u);
                                        }
                                    }
                                    m
                                });
                                idx.get(&filler).copied()
                            })
                            .unwrap_or(0);
                        filler_cache.insert(filler.clone(), found);
                        found
                    };
                    raw.edges.push((u_ind, role, w));
                }
            }
            need_rbox_close = true;
        } else if !sep.inert_probes.is_empty() || !sep.inert_extra_individuals.is_empty() {
            let mut ind_names = Vec::with_capacity(
                sep.inert_probes.len() + sep.inert_extra_individuals.len(),
            );
            let mut copies = Vec::with_capacity(
                sep.inert_probes.len() + sep.inert_extra_individuals.len(),
            );
            let mut label_first_elem: Option<HashMap<String, usize>> = None;
            let mut probe_cache: HashMap<String, usize> = HashMap::new();
            for (ind, probe) in sep.inert_probes {
                let w = if let Some(&cached) = probe_cache.get(&probe) {
                    cached
                } else {
                    let found = raw
                        .witnesses
                        .get(&probe)
                        .copied()
                        .or_else(|| {
                            let idx = label_first_elem.get_or_insert_with(|| {
                                let mut m = HashMap::new();
                                for (u, lbl) in raw.labels.iter().enumerate() {
                                    for c in lbl {
                                        m.entry(c.clone()).or_insert(u);
                                    }
                                }
                                m
                            });
                            idx.get(&probe).copied()
                        })
                        .unwrap_or(0);
                    probe_cache.insert(probe.clone(), found);
                    found
                };
                copies.push((
                    w,
                    format!("{NOMINAL_PREFIX}{ind}"),
                    vec![format!("{NOMINAL_PREFIX}{ind}")],
                ));
                ind_names.push(ind);
            }
            for ind in sep.inert_extra_individuals {
                copies.push((
                    0,
                    format!("{NOMINAL_PREFIX}{ind}"),
                    vec![format!("{NOMINAL_PREFIX}{ind}")],
                ));
                ind_names.push(ind);
            }
            let new_elems = duplicate_elements_batch(raw, copies);
            let ind_to_elem: HashMap<String, usize> =
                ind_names.into_iter().zip(new_elems).collect();
            for (role, s, t) in sep.inert_role_assertions {
                if let (Some(&su), Some(&tu)) = (ind_to_elem.get(&s), ind_to_elem.get(&t)) {
                    raw.edges.push((su, role, tu));
                }
            }
            need_rbox_close = true;
        }
        if need_rbox_close {
            let mut edge_set: HashSet<(usize, String, usize)> = raw.edges.drain(..).collect();
            crate::engine::close_edges_under_rbox_rows(
                &meta.rbox,
                raw.contexts.len(),
                &mut edge_set,
            )?;
            raw.edges = edge_set.into_iter().collect();
            raw.edges.sort();
        }
    }

    // 2. `positive_abox_quotient`: expand `<urn:km:positive-abox-quotient>` into
    //    the source `SameIndividual` equivalence classes.
    if let Some(comps) = positive_abox_quotient_comps {
        if !comps.is_empty() {
            for list in &comps[..] {
                for iri in list {
                    meta.iri_map.entry(iri.clone()).or_insert_with(|| iri.clone());
                }
            }
            let is_merged_marker = |s: &str| {
                s.contains("positive-abox-quotient") || s.contains("__km_abox_merged")
            };
            let merged_elem = (0..raw.contexts.len())
                .find(|&u| {
                    is_merged_marker(&raw.contexts[u])
                        || raw.labels[u].iter().any(|c| is_merged_marker(c))
                })
                .unwrap_or(0);
            for u in 0..raw.contexts.len() {
                raw.labels[u].retain(|c| !is_merged_marker(c));
                if is_merged_marker(&raw.contexts[u]) && !comps[0].is_empty() {
                    raw.contexts[u] = format!("{NOMINAL_PREFIX}{}", comps[0][0]);
                }
            }
            for iri in &comps[0] {
                let nom = format!("{NOMINAL_PREFIX}{iri}");
                if !raw.labels[merged_elem].contains(&nom) {
                    raw.labels[merged_elem].push(nom);
                }
            }
            if comps.len() > 1 {
                let mut copy_elems = vec![merged_elem];
                let copies: Vec<(usize, String, Vec<String>)> = comps[1..]
                    .iter()
                    .filter(|comp| !comp.is_empty())
                    .map(|comp| {
                        (
                            merged_elem,
                            format!("{NOMINAL_PREFIX}{}", comp[0]),
                            comp.iter().map(|i| format!("{NOMINAL_PREFIX}{i}")).collect(),
                        )
                    })
                    .collect();
                copy_elems.extend(duplicate_elements_batch(raw, copies));
                let self_roles: Vec<String> = raw
                    .edges
                    .iter()
                    .filter_map(|(f, r, t)| {
                        (*f == merged_elem && *t == merged_elem).then(|| r.clone())
                    })
                    .collect();
                for &u1 in &copy_elems {
                    for &u2 in &copy_elems {
                        if u1 != u2 {
                            for r in &self_roles {
                                raw.edges.push((u1, r.clone(), u2));
                            }
                        }
                    }
                }
                raw.edges.sort();
                raw.edges.dedup();
            }
        }
    }

    // 3. `abox_quotient`: attach atomic-mode individuals or expand block representatives.
    if let Some(pairs) = abox_quotient_atomic {
        let mut full_to_short: HashMap<String, String> = HashMap::new();
        for (short, full) in &meta.iri_map {
            full_to_short.insert(full.clone(), short.clone());
        }
        let mut label_first_elem: Option<HashMap<String, usize>> = None;
        let mut class_elem_cache: HashMap<String, usize> = HashMap::new();
        let mut touched_elems: Vec<usize> = Vec::new();
        for (ind_iri, class_iri) in pairs {
            let elem = if let Some(&cached) = class_elem_cache.get(class_iri.as_str()) {
                cached
            } else {
                let short_opt = full_to_short.get(class_iri.as_str()).map(String::as_str);
                let found = short_opt
                    .and_then(|s| raw.witnesses.get(s).copied())
                    .or_else(|| raw.witnesses.get(class_iri.as_str()).copied())
                    .or_else(|| {
                        if matches!(
                            class_iri.as_str(),
                            "owl:Thing" | "Thing" | "⊤" | "http://www.w3.org/2002/07/owl#Thing"
                        ) {
                            return Some(0);
                        }
                        let idx = label_first_elem.get_or_insert_with(|| {
                            let mut m = HashMap::new();
                            for (u, lbl) in raw.labels.iter().enumerate() {
                                for c in lbl {
                                    m.entry(c.clone()).or_insert(u);
                                }
                            }
                            m
                        });
                        short_opt
                            .and_then(|s| idx.get(s).copied())
                            .or_else(|| idx.get(class_iri.as_str()).copied())
                    })
                    .unwrap_or(0);
                class_elem_cache.insert(class_iri.clone(), found);
                found
            };
            meta.iri_map
                .entry(ind_iri.clone())
                .or_insert_with(|| ind_iri.clone());
            raw.labels[elem].push(format!("{NOMINAL_PREFIX}{ind_iri}"));
            touched_elems.push(elem);
        }
        touched_elems.sort_unstable();
        touched_elems.dedup();
        for elem in touched_elems {
            raw.labels[elem].sort();
            raw.labels[elem].dedup();
        }
    } else if let Some(blocks) = abox_quotient_blocks {
        let block_map: HashMap<&str, &[String]> = blocks
            .iter()
            .map(|(rep, members)| (rep.as_str(), members.as_slice()))
            .collect();
        for (_, members) in blocks {
            for m in members {
                meta.iri_map.entry(m.clone()).or_insert_with(|| m.clone());
            }
        }
        for u in 0..raw.labels.len() {
            let mut extra: Vec<String> = Vec::new();
            for name in raw.labels[u]
                .iter()
                .chain(std::iter::once(&raw.contexts[u]))
            {
                if let Some(short) = name.strip_prefix(NOMINAL_PREFIX) {
                    let full = meta
                        .iri_map
                        .get(short)
                        .map(String::as_str)
                        .unwrap_or(short);
                    if let Some(members) = block_map.get(full) {
                        for m in *members {
                            extra.push(format!("{NOMINAL_PREFIX}{m}"));
                        }
                    }
                }
            }
            if !extra.is_empty() {
                raw.labels[u].extend(extra);
                raw.labels[u].sort();
                raw.labels[u].dedup();
            }
        }
    }

    // 4. `data_abox_projection`: attach projected data-property assertions.
    if !projected_data_assertions.is_empty() {
        raw.extra_values.extend_from_slice(projected_data_assertions);
    }

    // 5. `mirror`: reconstruct private negative-existential definitions `N_F ≡ ¬∃R.F`.
    if let Some(specs) = mirror_specs {
        let is_proxy = |s: &str| {
            s.starts_with(super::mirror::PROXY_IRI_PREFIX) || s.starts_with("km:mirror-proxy:")
        };
        meta.named.retain(|s| !is_proxy(s) && !meta.iri_map.get(s).is_some_and(|u| is_proxy(u)));
        meta.declared
            .retain(|s| !is_proxy(s) && !meta.iri_map.get(s).is_some_and(|u| is_proxy(u)));
        raw.witnesses
            .retain(|k, _| !is_proxy(k) && !meta.iri_map.get(k).is_some_and(|u| is_proxy(u)));
        raw.witness_exact_by_class
            .retain(|k, _| !is_proxy(k) && !meta.iri_map.get(k).is_some_and(|u| is_proxy(u)));
        for lbl in &mut raw.labels {
            lbl.retain(|c| !is_proxy(c) && !meta.iri_map.get(c).is_some_and(|u| is_proxy(u)));
        }

        let u_iso = raw.contexts.len();
        raw.contexts.push("__mirror_isolated".to_string());
        raw.labels.push(Vec::new());

        let n_elems = raw.contexts.len();
        let blocked_map: HashMap<usize, usize> = raw.blocked.iter().copied().collect();
        let resolve_b = |start: usize| -> usize {
            let mut cur = start;
            let mut hops = 0;
            while let Some(&nxt) = blocked_map.get(&cur) {
                if nxt == cur || hops > n_elems {
                    break;
                }
                cur = nxt;
                hops += 1;
            }
            cur
        };

        let mut full_to_short: HashMap<String, String> = HashMap::new();
        for (short, full) in &meta.iri_map {
            full_to_short.insert(full.clone(), short.clone());
        }
        let mut out_by_role: HashMap<String, Vec<Vec<usize>>> = HashMap::new();
        for (f, r, t) in &raw.edges {
            let full_r = meta.iri_map.get(r).cloned().unwrap_or_else(|| r.clone());
            out_by_role
                .entry(full_r)
                .or_insert_with(|| vec![Vec::new(); n_elems])[*f]
                .push(*t);
        }
        let label_sets: Vec<HashSet<String>> = raw
            .labels
            .iter()
            .map(|lbl| {
                lbl.iter()
                    .map(|c| meta.iri_map.get(c).cloned().unwrap_or_else(|| c.clone()))
                    .collect()
            })
            .collect();

        let exact_iso = specs.len() == 1;
        for (neg_iri, role_iri, filler_opt) in specs {
            meta.iri_map
                .entry(neg_iri.clone())
                .or_insert_with(|| neg_iri.clone());
            if !meta.named.contains(neg_iri) {
                meta.named.push(neg_iri.clone());
            }
            if !meta.declared.contains(neg_iri) {
                meta.declared.push(neg_iri.clone());
            }
            for u in 0..n_elems {
                let eff = resolve_b(u);
                let has_rf = match filler_opt {
                    None => false,
                    Some(f_iri) => {
                        let is_thing = f_iri == "http://www.w3.org/2002/07/owl#Thing"
                            || f_iri == "owl:Thing";
                        let check_src = |src: usize| -> bool {
                            out_by_role
                                .get(role_iri)
                                .and_then(|v| v.get(src))
                                .is_some_and(|succs| {
                                    succs.iter().any(|&dst| {
                                        is_thing || label_sets[dst].contains(f_iri)
                                    })
                                })
                        };
                        check_src(u) || (eff != u && check_src(eff))
                    }
                };
                if !has_rf {
                    raw.labels[u].push(neg_iri.clone());
                }
            }
            raw.witnesses.insert(neg_iri.clone(), u_iso);
            raw.witness_exact_by_class
                .insert(neg_iri.clone(), exact_iso);
        }
        for lbl in &mut raw.labels {
            lbl.sort();
            lbl.dedup();
        }
        raw.witness_exact = false;
        for (k, v) in &mut raw.witness_exact_by_class {
            if !specs.iter().any(|(neg, _, _)| neg == k) {
                *v = false;
            }
        }
    }
    Ok(())
}

/// Finish the model export session captured during `km classify` and write it
/// to `out`. Never re-parses or re-classifies the ontology when the answering
/// route recorded its state.
pub fn finish_and_write(
    _cfg: &Config,
    _ont: &Path,
    out: &Path,
) -> Result<String, OrchestrateError> {
    std::env::remove_var("KM_EXPORT_MODEL_ACTIVE");
    std::env::remove_var("KM_EXPORT_MODEL_BUDGET_S");

    let mut session = {
        let mut g = SESSION.lock().unwrap_or_else(|e| e.into_inner());
        std::mem::take(&mut *g)
    };

    let file = std::fs::File::create(out)?;
    let mut w = std::io::BufWriter::with_capacity(1 << 20, file);

    if session.inconsistent {
        line(
            &mut w,
            serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "inconsistent"}),
        )?;
        w.flush()?;
        return Ok("model export: the ontology is inconsistent, no model".to_string());
    }

    if let Some(reason) = session.declined_reason.take() {
        line(
            &mut w,
            serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "declined", "reason": reason}),
        )?;
        w.flush()?;
        return Ok(format!("model export declined: {reason}"));
    }

    let resolved: Result<Option<(RawModel, frontend_run::Meta)>, String> =
        if let Some(flat_state) = session.flat_nf1_state.take() {
            build_raw_model_from_flat_nf1(flat_state).map(Some)
        } else if let Some(meta) = session.engine_meta.take() {
            let dropped: u64 = meta.dropped_source_axioms.values().sum();
            if dropped > 0 || meta.uncarried_data_assertions > 0 {
                Err("source ontology has dropped or uncarried axioms".to_string())
            } else if meta.abox_inconsistent {
                Ok(None)
            } else {
                let payload_opt: Option<WorkerModelPayload> =
                    if let Some(p) = session.worker_model_payload.take() {
                        Some((*p).clone())
                    } else if let Some(path) = session.worker_model_path.take() {
                        std::fs::File::open(&path)
                            .ok()
                            .and_then(|f| serde_json::from_reader(std::io::BufReader::new(f)).ok())
                    } else {
                        session.inproc_payload.take()
                    };
                match payload_opt {
                    Some(WorkerModelPayload::El(res)) => res.and_then(|m| {
                        build_raw_model_from_el(m, &meta.rbox).map(|opt| opt.map(|raw| (raw, meta)))
                    }),
                    Some(WorkerModelPayload::Cb(res)) => {
                        res.map(|m| build_raw_model_from_cb(m).map(|raw| (raw, meta)))
                    }
                    Some(WorkerModelPayload::Bridge(res)) => res.and_then(|bm| {
                        build_raw_model_from_bridge(bm, &meta.rbox, &meta.nominal_abox)
                            .map(|opt| opt.map(|raw| (raw, meta)))
                    }),
                    Some(WorkerModelPayload::Declined(reason)) => Err(reason),
                    None => Err("answering route did not record a model payload".to_string()),
                }
            }
        } else {
            Err("answering route did not record a model payload".to_string())
        };

    let resolved = match resolved {
        Ok(Some((mut raw, mut meta))) => apply_post_hooks(
            &mut raw,
            &mut meta,
            &session.unsat_iris,
            &session.projected_data_assertions,
            session.abox_quotient_atomic.as_deref(),
            session.abox_quotient_blocks.as_deref(),
            session.positive_abox_quotient_comps.as_deref(),
            session.mirror_specs.as_deref(),
        )
        .map(|()| Some((raw, meta))),
        other => other,
    };

    let status = match resolved {
        Ok(Some((raw, meta))) => {
            let data_roles = meta.data_roles.clone();
            write_model(&mut w, &raw, &meta, &data_roles)?;
            format!(
                "model export: route {}{}, {} elements, {} edges",
                raw.route,
                if raw.partial_reason.is_some() {
                    " (partial)"
                } else {
                    ""
                },
                raw.contexts.len(),
                raw.edges.len()
            )
        }
        Ok(None) => {
            line(
                &mut w,
                serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "inconsistent"}),
            )?;
            "model export: the ontology is inconsistent, no model".to_string()
        }
        Err(reason) => {
            line(
                &mut w,
                serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "declined", "reason": reason}),
            )?;
            format!("model export declined: {reason}")
        }
    };
    w.flush()?;
    Ok(status)
}

fn parse_for_export(
    text: &str,
) -> Result<(frontend_run::Meta, crate::json_io::JInput), OrchestrateError> {
    if std::env::var_os("KM_ROUTE").is_none() {
        std::env::set_var("KM_ROUTE", crate::routing::Route::Auto.as_str());
    }
    let result = match crate::frontend::ofn_to_clauses_for_classifier(text) {
        Ok(r) => r,
        Err(e) => return Err(OrchestrateError::OutOfFragment(e.0)),
    };
    let meta = frontend_run::Meta {
        iri_map: result.iri_map,
        named: result.named,
        declared: result.declared,
        el_rbox_safe: result.el_rbox_safe,
        abox_inconsistent: result.abox_inconsistent,
        asserted_classes: result.asserted_classes,
        profile: result.profile,
        route: result.route,
        uncarried_data_assertions: result.uncarried_data_assertions,
        dropped_source_axioms: result.dropped_source_axioms,
        route_approximations: result.route_approximations,
        one_sorted_data_successors: result.one_sorted_data_successors,
        rbox: result.rbox.clone(),
        data_roles: result.data_roles.clone(),
        nominal_abox: result.nominal_abox.clone(),
        separable_abox_export: result.separable_abox_export,
    };
    let input = crate::json_io::JInput {
        clauses: result.clauses,
        cb_typed_source: None,
        rbox: result.rbox,
        cardinalities: result.cardinalities,
        definers: result.definers,
        source_axioms: result.source_axioms,
        nominal_abox: result.nominal_abox,
        rules: result.rules,
        data_roles: result.data_roles,
    };
    Ok((meta, input))
}

/// Write the export of `ont` to `out` standalone (used by unit tests or direct
/// library callers that did not call `begin_session` before `classify`).
pub fn export(cfg: &Config, ont: &Path, out: &Path) -> Result<String, OrchestrateError> {
    if std::env::var_os("KM_EXPORT_MODEL_ROUTE").is_none() {
        let _guard = crate::routing::EnvironmentGuard::capture();
        begin_session(None);
        let _ = super::classify_with_evidence_mode(cfg, ont, true)?;
        return finish_and_write(cfg, ont, out);
    }

    let _env_guard = crate::routing::EnvironmentGuard::capture();
    std::env::set_var("KM_NO_SEPARABLE_ABOX_ELISION", "1");
    std::env::set_var("KM_NO_FAST_SEPARABLE_ABOX_PARSE", "1");
    std::env::set_var("KM_DATA_ASSERTION_AS_CLASS", "1");
    std::env::set_var("KM_KEEP_BLANK_NAMES", "1");

    let file = std::fs::File::create(out)?;
    let mut w = std::io::BufWriter::new(file);
    let text = std::fs::read_to_string(ont)?;
    let (meta, input) = parse_for_export(&text)?;
    let status = match raw_model(cfg, &text, &meta, &input) {
        Ok(Some(raw)) => {
            write_model(&mut w, &raw, &meta, &input.data_roles)?;
            format!(
                "model export: route {}, {} elements, {} edges",
                raw.route,
                raw.contexts.len(),
                raw.edges.len()
            )
        }
        Ok(None) => {
            line(
                &mut w,
                serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "inconsistent"}),
            )?;
            "model export: the ontology is inconsistent, no model".to_string()
        }
        Err(reason) => {
            line(
                &mut w,
                serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "declined", "reason": reason}),
            )?;
            format!("model export declined: {reason}")
        }
    };
    w.flush()?;
    Ok(status)
}

fn try_el_raw_model(
    text: &str,
    meta: &frontend_run::Meta,
    input: &crate::json_io::JInput,
) -> Option<Result<Option<RawModel>, String>> {
    let owned;
    let (el_meta, el_input) = if std::env::var_os("KM_NOMINALS").is_some() {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::remove_var("KM_NOMINALS");
        std::env::set_var("KM_ROUTE", "elc");
        owned = parse_for_export(text).ok()?;
        (&owned.0, &owned.1)
    } else {
        (meta, input)
    };
    let m =
        crate::elcomplete::el_model(el_input, el_meta.el_rbox_safe, el_meta.abox_inconsistent)?;
    let raw = match build_raw_model_from_el(m, &el_input.rbox) {
        Ok(r) => r,
        Err(e) => return Some(Err(e)),
    };
    if let Some(ref rm) = raw {
        if el_meta
            .asserted_classes
            .iter()
            .any(|c| !rm.witnesses.contains_key(c))
        {
            return Some(Ok(None));
        }
    }
    Some(Ok(raw))
}

fn try_cb_raw_model(
    text: &str,
    meta: &frontend_run::Meta,
    input: &crate::json_io::JInput,
) -> Result<Option<RawModel>, String> {
    let owned;
    let (cb_meta, cb_input) = if std::env::var_os("KM_NOMINALS").is_some() {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::remove_var("KM_NOMINALS");
        std::env::set_var("KM_ROUTE", "cb_plain16");
        owned = parse_for_export(text).map_err(|e| e.to_string())?;
        (&owned.0, &owned.1)
    } else {
        (meta, input)
    };
    let m = crate::engine::cb_model(cb_input, cb_meta.abox_inconsistent)?;
    let raw = build_raw_model_from_cb(m);
    if let Some(ref rm) = raw {
        if cb_meta
            .asserted_classes
            .iter()
            .any(|c| !rm.witnesses.contains_key(c))
        {
            return Ok(None);
        }
    }
    Ok(raw)
}

fn try_bridge_raw_model(
    text: &str,
    meta: &frontend_run::Meta,
    input: &crate::json_io::JInput,
) -> Result<Option<RawModel>, String> {
    let _guard = crate::routing::EnvironmentGuard::capture();
    let owned;
    let (ht_meta, ht_input) =
        if input.source_axioms.is_empty() || std::env::var_os("KM_NOMINALS").is_some() {
            std::env::remove_var("KM_NOMINALS");
            std::env::set_var("KM_ROUTE", "ht_bridge");
            std::env::set_var("KM_TRIGGER_ABSORB", "1");
            owned = parse_for_export(text).map_err(|e| e.to_string())?;
            (&owned.0, &owned.1)
        } else {
            std::env::set_var("KM_TRIGGER_ABSORB", "1");
            (meta, input)
        };
    if ht_meta.abox_inconsistent {
        return Ok(None);
    }
    if !ht_input.rules.is_empty() {
        return Err("ht-bridge model export declines SWRL rules".to_string());
    }
    let has_cards = !ht_input.cardinalities.is_empty();
    let named_set: HashSet<String> = ht_meta.named.iter().cloned().collect();
    let bridge_clauses = super::race::native_nominal_bridge_clauses(
        &ht_input.clauses,
        &ht_input.nominal_abox,
        &ht_input.definers,
        true,
        !ht_input.rules.is_empty(),
    );
    let mut tin = cb_to_ht::convert(
        &bridge_clauses,
        Some(&ht_input.rbox),
        &named_set,
        &ht_input.cardinalities,
        &ht_input.definers,
        &ht_input.source_axioms,
        has_cards,
        &ht_input.rules,
        false,
    );
    if !ht_input.nominal_abox.is_empty()
        && !cb_to_ht::install_nominal_abox_with_same(&mut tin, &ht_input.nominal_abox, true)
    {
        return Err("ht-bridge failed to install nominal ABox".to_string());
    }
    if tin.dropped > 0 {
        return Err(format!(
            "ht-bridge input has {} dropped clause(s)",
            tin.dropped
        ));
    }
    let bm = crate::konclude_ht::bridge::bridge_model(&tin, &ht_input.rbox)?;
    build_raw_model_from_bridge(
        bm,
        &ht_input.rbox,
        &ht_input.nominal_abox,
    )
}

/// `Ok(None)` for an inconsistent clause stream, `Err(reason)` when no
/// exporter covers it.
fn raw_model(
    cfg: &Config,
    text: &str,
    meta: &frontend_run::Meta,
    input: &crate::json_io::JInput,
) -> Result<Option<RawModel>, String> {
    let dropped: u64 = meta.dropped_source_axioms.values().sum();
    if dropped > 0 || meta.uncarried_data_assertions > 0 {
        return Err("source ontology has dropped or uncarried axioms".to_string());
    }
    if meta.abox_inconsistent {
        return Ok(None);
    }

    let forced_route = std::env::var("KM_EXPORT_MODEL_ROUTE").ok();
    if let Some(ref forced) = forced_route {
        return match forced.as_str() {
            "el" | "elc" | "el-canonical" => try_el_raw_model(text, meta, input)
                .unwrap_or_else(|| Err("el-canonical declined non-EL or uncertified input".into())),
            "cb" | "cb-horn" => try_cb_raw_model(text, meta, input),
            "ht" | "bridge" | "ht-bridge" => try_bridge_raw_model(text, meta, input),
            other => Err(format!("unknown KM_EXPORT_MODEL_ROUTE={other}")),
        };
    }

    let force_cb = cfg.mechanism == super::config::Mechanism::Cb && !cfg.elc;
    if !force_cb && (meta.route == "elc" || meta.el_rbox_safe) {
        if let Some(res) = try_el_raw_model(text, meta, input) {
            return res;
        }
    }
    if force_cb
        || meta.route.starts_with("cb_")
        || meta.route == "nominals"
        || meta.route == "manual"
    {
        if !force_cb {
            if let Some(res) = try_el_raw_model(text, meta, input) {
                return res;
            }
            return try_cb_raw_model(text, meta, input)
                .or_else(|_| try_bridge_raw_model(text, meta, input));
        }
        return try_cb_raw_model(text, meta, input);
    }

    if let Some(res) = try_el_raw_model(text, meta, input) {
        return res;
    }

    if meta.route.starts_with("ht_")
        || meta.route == "nominal_ni_abox"
        || meta.route == "production_all"
        || meta.route == "certified_el_production"
    {
        return try_bridge_raw_model(text, meta, input);
    }

    try_cb_raw_model(text, meta, input).or_else(|_| try_bridge_raw_model(text, meta, input))
}

const NOMINAL_PREFIX: &str = "__nom__";

fn write_model<W: Write>(
    w: &mut W,
    raw: &RawModel,
    meta: &frontend_run::Meta,
    data_roles: &[String],
) -> std::io::Result<()> {
    #[derive(serde::Serialize)]
    struct ElementLine<'a> {
        classes: &'a [String],
        context: &'a str,
        id: &'a str,
        #[serde(skip_serializing_if = "slice_is_empty")]
        individuals: &'a [String],
        kind: &'static str,
    }
    #[derive(serde::Serialize)]
    struct EdgeLine<'a> {
        from: &'a str,
        kind: &'static str,
        role: &'a str,
        to: &'a str,
    }
    #[derive(serde::Serialize)]
    struct WitnessLine<'a> {
        class: &'a str,
        element: &'a str,
        exact: bool,
        kind: &'static str,
    }
    fn slice_is_empty(s: &&[String]) -> bool {
        s.is_empty()
    }

    macro_rules! iri_ref {
        ($short:expr) => {{
            let s: &str = $short;
            meta.iri_map.get(s).map(String::as_str).unwrap_or(s)
        }};
    }
    let iri = |short: &str| -> String { iri_ref!(short).to_string() };
    // Source classes: the frontend's named (non-fresh) classes.
    let source: HashSet<&str> = meta
        .named
        .iter()
        .chain(meta.declared.iter())
        .map(String::as_str)
        .filter(|&s| {
            !matches!(
                s,
                "owl:Thing" | "Thing" | "owl:Nothing" | "Nothing" | "⊤" | "⊥"
            ) && !meta.iri_map.get(s).is_some_and(|u| u.starts_with("_:"))
        })
        .collect();
    let data: HashSet<&str> = data_roles.iter().map(String::as_str).collect();
    let is_source_role =
        |r: &str| !r.starts_with("__") && !r.starts_with("Q_") && meta.iri_map.contains_key(r);

    // Precompute data-cell membership in O(V + E).
    let mut is_cell_vec = vec![false; raw.contexts.len()];
    for i in 0..raw.contexts.len() {
        if raw.contexts[i].starts_with("__dt__")
            || raw.labels[i]
                .iter()
                .any(|c| c.starts_with("__dt__") || c == "__sort__data")
        {
            is_cell_vec[i] = true;
        }
    }
    for (_, r, t) in &raw.edges {
        if data.contains(r.as_str()) {
            is_cell_vec[*t] = true;
        }
    }
    let is_cell = |i: usize| is_cell_vec[i];

    let ids: Vec<String> = (0..raw.contexts.len()).map(|i| format!("e{i}")).collect();
    let mut individuals: Vec<Vec<String>> = vec![Vec::new(); raw.contexts.len()];
    let mut ind_to_eid: HashMap<String, String> = HashMap::new();
    let need_ind_to_eid = !raw.extra_values.is_empty();
    for (i, label) in raw.labels.iter().enumerate() {
        for name in label.iter().chain(std::iter::once(&raw.contexts[i])) {
            if let Some(a) = name.strip_prefix(NOMINAL_PREFIX) {
                let a = iri(a);
                if need_ind_to_eid && !is_cell(i) {
                    ind_to_eid.insert(a.clone(), ids[i].clone());
                }
                individuals[i].push(a);
            }
        }
        if !individuals[i].is_empty() {
            individuals[i].sort();
            individuals[i].dedup();
        }
    }
    let elements = (0..raw.contexts.len()).filter(|&i| !is_cell(i)).count();
    let object_edges: Vec<&(usize, String, usize)> = raw
        .edges
        .iter()
        .filter(|(f, r, t)| {
            !is_cell(*f) && !is_cell(*t) && is_source_role(r) && !data.contains(r.as_str())
        })
        .collect();
    let mut header = serde_json::json!({
        "kind": "model",
        "format": "km-model-v1",
        "status": if raw.partial_reason.is_some() { "partial" } else { "ok" },
        "route": raw.route,
        "elements": elements,
        "edges": object_edges.len(),
        "closure": raw.closure,
        "witness_exact": raw.witness_exact,
        "blocked": raw.blocked.len(),
    });
    if let Some(ref reason) = raw.partial_reason {
        header["reason"] = serde_json::json!(reason);
    }
    line(w, header)?;
    for (i, label) in raw.labels.iter().enumerate() {
        if is_cell(i) {
            continue;
        }
        let mut classes: Vec<String> = label
            .iter()
            .filter(|c| source.contains(c.as_str()))
            .map(|c| iri(c))
            .collect();
        classes.sort();
        classes.dedup();
        let context = &raw.contexts[i];
        let context_str = if source.contains(context.as_str()) {
            iri_ref!(context)
        } else {
            context.as_str()
        };
        serde_json::to_writer(
            &mut *w,
            &ElementLine {
                classes: &classes,
                context: context_str,
                id: &ids[i],
                individuals: &individuals[i],
                kind: "element",
            },
        )?;
        w.write_all(b"\n")?;
    }
    for (f, r, t) in &object_edges {
        serde_json::to_writer(
            &mut *w,
            &EdgeLine {
                from: &ids[*f],
                kind: "edge",
                role: iri_ref!(r),
                to: &ids[*t],
            },
        )?;
        w.write_all(b"\n")?;
    }
    let mut seen_values: HashSet<(String, String, String)> = HashSet::new();
    for (f, r, t) in &raw.edges {
        if !is_cell(*f) && is_cell(*t) && (data.contains(r.as_str()) || is_source_role(r)) {
            let mut dts: Vec<String> = raw.labels[*t]
                .iter()
                .chain(std::iter::once(&raw.contexts[*t]))
                .filter(|c| c.starts_with("__dt__"))
                .cloned()
                .collect();
            dts.sort();
            dts.dedup();
            let cell = if let Some(val_dt) = dts.iter().find(|c| c.starts_with("__dt__val__")) {
                val_dt.clone()
            } else if raw.contexts[*t].starts_with("__dt__") {
                raw.contexts[*t].clone()
            } else {
                dts.iter()
                    .filter(|d| {
                        !dts.iter().any(|o| {
                            *o != **d
                                && crate::frontend::datatypes::bridge_exact_atomic_subsumed(o, d)
                                    == Some(true)
                                && crate::frontend::datatypes::bridge_exact_atomic_subsumed(d, o)
                                    != Some(true)
                        })
                    })
                    .max_by_key(|d| {
                        (
                            d.starts_with("__dt__c__"),
                            d.contains("min") && d.contains("max"),
                            d.len(),
                        )
                    })
                    .or_else(|| dts.first())
                    .cloned()
                    .unwrap_or_else(|| raw.contexts[*t].clone())
            };
            let prop_full = iri(r);
            let literal = dts
                .iter()
                .find_map(|c| c.strip_prefix("__dt__val__").map(str::to_string));
            let dedup_key = if let Some(ref lit) = literal {
                format!("{cell}::{lit}::{}", dts.join("|"))
            } else {
                format!("{cell}::{}", dts.join("|"))
            };
            if !seen_values.insert((ids[*f].clone(), prop_full.clone(), dedup_key)) {
                continue;
            }
            let mut obj = serde_json::json!({
                "kind": "value",
                "element": ids[*f],
                "property": prop_full,
                "cell": cell,
                "datatypes": dts,
            });
            if let Some(lit) = literal {
                obj["literal"] = serde_json::json!(lit);
            }
            line(w, obj)?;
        }
    }
    for (owner_iri, prop_iri, literal) in &raw.extra_values {
        if let Some(eid) = ind_to_eid.get(owner_iri) {
            let cell = format!("__dt__val__{literal}");
            if !seen_values.insert((eid.clone(), prop_iri.clone(), cell.clone())) {
                continue;
            }
            line(
                w,
                serde_json::json!({
                    "kind": "value",
                    "element": eid,
                    "property": prop_iri,
                    "cell": cell,
                    "datatypes": [cell],
                    "literal": literal,
                }),
            )?;
        }
    }
    for (i, group) in individuals.iter().enumerate() {
        if group.len() > 1 && !is_cell(i) {
            line(
                w,
                serde_json::json!({"kind": "same", "individuals": group, "element": ids[i]}),
            )?;
        }
    }
    for (e, b) in &raw.blocked {
        line(
            w,
            serde_json::json!({"kind": "blocked", "element": ids[*e], "blocker": ids[*b]}),
        )?;
    }
    for (class, &e) in &raw.witnesses {
        if source.contains(class.as_str()) && !is_cell(e) {
            let exact = raw
                .witness_exact_by_class
                .get(class)
                .copied()
                .unwrap_or(raw.witness_exact);
            serde_json::to_writer(
                &mut *w,
                &WitnessLine {
                    class: iri_ref!(class),
                    element: &ids[e],
                    exact,
                    kind: "witness",
                },
            )?;
            w.write_all(b"\n")?;
        }
    }
    for (class, e) in &raw.extra_witnesses {
        if source.contains(class.as_str()) && !is_cell(*e) {
            serde_json::to_writer(
                &mut *w,
                &WitnessLine {
                    class: iri_ref!(class),
                    element: &ids[*e],
                    exact: false,
                    kind: "witness",
                },
            )?;
            w.write_all(b"\n")?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn render_jsonl(text: &str, route: Option<&str>) -> Vec<serde_json::Value> {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_NO_SEPARABLE_ABOX_ELISION", "1");
        std::env::set_var("KM_NO_FAST_SEPARABLE_ABOX_PARSE", "1");
        std::env::set_var("KM_DATA_ASSERTION_AS_CLASS", "1");
        std::env::set_var("KM_KEEP_BLANK_NAMES", "1");
        match route {
            Some(r) => std::env::set_var("KM_EXPORT_MODEL_ROUTE", r),
            None => std::env::remove_var("KM_EXPORT_MODEL_ROUTE"),
        }
        let cfg = Config::from_env();
        let (meta, input) = parse_for_export(text).expect("parse_for_export");
        let mut buf = Vec::new();
        match raw_model(&cfg, text, &meta, &input) {
            Ok(Some(raw)) => {
                write_model(&mut buf, &raw, &meta, &input.data_roles).expect("write_model");
            }
            Ok(None) => {
                line(
                    &mut buf,
                    serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "inconsistent"}),
                )
                .unwrap();
            }
            Err(reason) => {
                line(
                    &mut buf,
                    serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "declined", "reason": reason}),
                )
                .unwrap();
            }
        }
        String::from_utf8(buf)
            .unwrap()
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect()
    }

    #[test]
    fn model_export_all_routes_and_inconsistent() {
        let _test_env = crate::test_env::write();
        let ofn_el = r#"
            Ontology(
                Declaration(Class(<http://ex.org/A>))
                Declaration(Class(<http://ex.org/B>))
                Declaration(Class(<http://ex.org/C>))
                Declaration(ObjectProperty(<http://ex.org/r>))
                Declaration(NamedIndividual(<http://ex.org/ind1>))
                SubClassOf(<http://ex.org/A> ObjectSomeValuesFrom(<http://ex.org/r> <http://ex.org/B>))
                SubClassOf(ObjectSomeValuesFrom(<http://ex.org/r> <http://ex.org/B>) <http://ex.org/C>)
                ClassAssertion(<http://ex.org/A> <http://ex.org/ind1>)
            )
        "#;
        let rows = render_jsonl(ofn_el, Some("el-canonical"));
        assert_eq!(rows[0]["status"], "ok", "el rows: {:?}", rows);
        assert_eq!(rows[0]["route"], "el-canonical");
        let witnesses: BTreeMap<String, String> = rows
            .iter()
            .filter(|r| r["kind"] == "witness")
            .map(|r| {
                (
                    r["class"].as_str().unwrap().to_string(),
                    r["element"].as_str().unwrap().to_string(),
                )
            })
            .collect();
        assert!(
            witnesses.contains_key("http://ex.org/A"),
            "witnesses: {:?}",
            witnesses
        );
        assert!(witnesses.contains_key("http://ex.org/B"));
        assert!(witnesses.contains_key("http://ex.org/C"));
        let elems: BTreeMap<String, Vec<String>> = rows
            .iter()
            .filter(|r| r["kind"] == "element")
            .map(|r| {
                let classes = r["classes"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|v| v.as_str().unwrap().to_string())
                    .collect();
                (r["id"].as_str().unwrap().to_string(), classes)
            })
            .collect();
        let wa = &witnesses["http://ex.org/A"];
        assert!(elems[wa].contains(&"http://ex.org/A".to_string()));
        assert!(elems[wa].contains(&"http://ex.org/C".to_string()));
        assert!(!elems[wa].contains(&"http://ex.org/B".to_string()));

        let ofn_ht = r#"
            Ontology(
                Declaration(Class(<http://ex.org/A>))
                Declaration(Class(<http://ex.org/B>))
                Declaration(Class(<http://ex.org/C>))
                Declaration(Class(<http://ex.org/D>))
                SubClassOf(<http://ex.org/A> ObjectUnionOf(<http://ex.org/B> <http://ex.org/C>))
                SubClassOf(<http://ex.org/B> <http://ex.org/D>)
                SubClassOf(<http://ex.org/C> <http://ex.org/D>)
            )
        "#;
        let rows_ht = render_jsonl(ofn_ht, Some("ht-bridge"));
        assert_eq!(rows_ht[0]["status"], "ok", "ht rows: {:?}", rows_ht);
        assert_eq!(rows_ht[0]["route"], "ht-bridge");
        let witnesses_ht: BTreeMap<String, (String, bool)> = rows_ht
            .iter()
            .filter(|r| r["kind"] == "witness")
            .map(|r| {
                (
                    r["class"].as_str().unwrap().to_string(),
                    (
                        r["element"].as_str().unwrap().to_string(),
                        r["exact"].as_bool().unwrap(),
                    ),
                )
            })
            .collect();
        assert_eq!(witnesses_ht.len(), 4);

        let horn_ofn = r#"
            Ontology(
                Declaration(Class(<http://ex.org/A>))
                Declaration(Class(<http://ex.org/B>))
                Declaration(Class(<http://ex.org/C>))
                Declaration(ObjectProperty(<http://ex.org/r>))
                SubClassOf(<http://ex.org/A> ObjectSomeValuesFrom(<http://ex.org/r> <http://ex.org/B>))
                SubClassOf(<http://ex.org/A> ObjectAllValuesFrom(<http://ex.org/r> <http://ex.org/C>))
            )
        "#;
        let rows_cb = render_jsonl(horn_ofn, Some("cb-horn"));
        assert_eq!(rows_cb[0]["status"], "ok", "cb rows: {:?}", rows_cb);
        assert_eq!(rows_cb[0]["route"], "cb-horn");

        let declined_rows = render_jsonl(ofn_ht, Some("cb-horn"));
        assert_eq!(declined_rows[0]["status"], "declined");

        let inc_ofn = r#"
            Ontology(
                Declaration(Class(<http://ex.org/A>))
                Declaration(NamedIndividual(<http://ex.org/a>))
                SubClassOf(<http://ex.org/A> owl:Nothing)
                ClassAssertion(<http://ex.org/A> <http://ex.org/a>)
            )
        "#;
        let rows_inc = render_jsonl(inc_ofn, None);
        assert_eq!(rows_inc[0]["status"], "inconsistent");
    }
}
