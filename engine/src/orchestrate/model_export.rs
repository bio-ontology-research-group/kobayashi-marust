//! `km classify --export-model FILE`: a model of the ontology over source
//! names, as JSON lines (`docs/MODEL-EXPORT.md`).
//!
//! The export is computed after the answer is published, from the same
//! frontend clause stream, so it never changes the answer and costs nothing
//! when it is not asked for. Routes:
//!
//! * `el-canonical`: the clause stream is EL (no residual for the EL
//!   completion). The canonical model of the completion ([`el_model`]) is a
//!   model of the clause stream, and the stream is a conservative extension
//!   of the source (fresh names only), so restricting the labels to source
//!   names gives a model of the source. The element of a satisfiable class
//!   `A` satisfies exactly the classes the ontology entails for `A`, so every
//!   witness is exact.
//!
//! Every other input gets one `{"kind":"model","status":"declined",...}`
//! line with the reason.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::Path;

use super::config::Config;
use super::{frontend_run, OrchestrateError};

/// A model over internal (clause-stream) names, before the source mapping.
pub(crate) struct RawModel {
    pub route: &'static str,
    /// Internal context or node name per element (for the `context` field).
    pub contexts: Vec<String>,
    pub labels: Vec<Vec<String>>,
    pub edges: Vec<(usize, String, usize)>,
    /// `(element, blocker)` for a finite representation with blocking.
    pub blocked: Vec<(usize, usize)>,
    /// Whether the element of a satisfiable class satisfies only its entailed
    /// superclasses (true for the EL canonical model).
    pub witness_exact: bool,
    /// Named class (internal name) to its witness element, when the route
    /// chose them; otherwise the element whose context is the class.
    pub witnesses: BTreeMap<String, usize>,
    /// The role closure a consumer must apply to the edges.
    pub closure: &'static str,
}

fn line<W: Write>(w: &mut W, value: serde_json::Value) -> std::io::Result<()> {
    serde_json::to_writer(&mut *w, &value)?;
    w.write_all(b"\n")
}

/// Write the export of `ont` to `out`. Returns a one-line status for stderr.
pub fn export(cfg: &Config, ont: &Path, out: &Path) -> Result<String, OrchestrateError> {
    let file = std::fs::File::create(out)?;
    let mut w = std::io::BufWriter::new(file);
    let (clauses_path, meta) = frontend_run::run_ofn_split(cfg, ont)?;
    let input: crate::json_io::JInput = serde_json::from_slice(&std::fs::read(clauses_path.path())?)?;
    let status = match raw_model(&input) {
        Ok(Some(raw)) => {
            write_model(&mut w, &raw, &meta, &input.data_roles)?;
            format!("model export: route {}, {} elements, {} edges", raw.route, raw.contexts.len(), raw.edges.len())
        }
        Ok(None) => {
            line(&mut w, serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "inconsistent"}))?;
            "model export: the ontology is inconsistent, no model".to_string()
        }
        Err(reason) => {
            line(&mut w, serde_json::json!({"kind": "model", "format": "km-model-v1", "status": "declined", "reason": reason}))?;
            format!("model export declined: {reason}")
        }
    };
    w.flush()?;
    Ok(status)
}

/// `Ok(None)` for an inconsistent clause stream, `Err(reason)` when no
/// exporter covers it.
fn raw_model(input: &crate::json_io::JInput) -> Result<Option<RawModel>, String> {
    if let Some(m) = crate::elcomplete::el_model(&input.clauses) {
        if m.inconsistent {
            return Ok(None);
        }
        let witnesses = m.contexts.iter().enumerate().map(|(i, c)| (c.clone(), i)).collect();
        return Ok(Some(RawModel {
            route: "el-canonical",
            contexts: m.contexts,
            labels: m.labels,
            edges: m.edges,
            blocked: Vec::new(),
            witness_exact: true,
            witnesses,
            closure: "none: the edges of each role are its extension (sub-roles lifted, chains and transitivity composed by the completion)",
        }));
    }
    Err("the clause stream is not EL and no other exporter applies (the CB route holds saturated contexts, not a model)".into())
}

const NOMINAL_PREFIX: &str = "__nom__";

fn write_model<W: Write>(
    w: &mut W,
    raw: &RawModel,
    meta: &frontend_run::Meta,
    data_roles: &[String],
) -> std::io::Result<()> {
    let iri = |short: &str| -> String { meta.iri_map.get(short).cloned().unwrap_or_else(|| short.to_string()) };
    // Source classes: the frontend's named (non-fresh) classes.
    let source: BTreeSet<&str> = meta.named.iter().chain(meta.declared.iter()).map(String::as_str).collect();
    let data: BTreeSet<&str> = data_roles.iter().map(String::as_str).collect();
    let is_source_role = |r: &str| !r.starts_with("__") && !r.starts_with("Q_") && meta.iri_map.contains_key(r);
    // Data cells: contexts of datatype abstractions.
    let is_cell = |i: usize| raw.contexts[i].starts_with("__dt__");
    let ids: Vec<String> = (0..raw.contexts.len()).map(|i| format!("e{i}")).collect();
    let mut individuals: Vec<Vec<String>> = vec![Vec::new(); raw.contexts.len()];
    for (i, label) in raw.labels.iter().enumerate() {
        for name in label.iter().chain(std::iter::once(&raw.contexts[i])) {
            if let Some(a) = name.strip_prefix(NOMINAL_PREFIX) {
                let a = iri(a);
                if !individuals[i].contains(&a) {
                    individuals[i].push(a);
                }
            }
        }
        individuals[i].sort();
    }
    let elements = (0..raw.contexts.len()).filter(|&i| !is_cell(i)).count();
    let object_edges: Vec<&(usize, String, usize)> =
        raw.edges.iter().filter(|(f, r, t)| !is_cell(*f) && !is_cell(*t) && is_source_role(r) && !data.contains(r.as_str())).collect();
    line(
        w,
        serde_json::json!({
            "kind": "model",
            "format": "km-model-v1",
            "status": "ok",
            "route": raw.route,
            "elements": elements,
            "edges": object_edges.len(),
            "closure": raw.closure,
            "witness_exact": raw.witness_exact,
            "blocked": raw.blocked.len(),
        }),
    )?;
    for (i, label) in raw.labels.iter().enumerate() {
        if is_cell(i) {
            continue;
        }
        let classes: Vec<String> = label.iter().filter(|c| source.contains(c.as_str())).map(|c| iri(c)).collect();
        let context = &raw.contexts[i];
        let context = if source.contains(context.as_str()) { iri(context) } else { context.clone() };
        let mut obj = serde_json::json!({"kind": "element", "id": ids[i], "context": context, "classes": classes});
        if !individuals[i].is_empty() {
            obj["individuals"] = serde_json::json!(individuals[i]);
        }
        line(w, obj)?;
    }
    for (f, r, t) in &object_edges {
        line(w, serde_json::json!({"kind": "edge", "role": iri(r), "from": ids[*f], "to": ids[*t]}))?;
    }
    for (f, r, t) in &raw.edges {
        if !is_cell(*f) && is_cell(*t) && data.contains(r.as_str()) {
            line(w, serde_json::json!({"kind": "value", "element": ids[*f], "property": iri(r), "cell": raw.contexts[*t]}))?;
        }
    }
    for (i, group) in individuals.iter().enumerate() {
        if group.len() > 1 && !is_cell(i) {
            line(w, serde_json::json!({"kind": "same", "individuals": group, "element": ids[i]}))?;
        }
    }
    for (e, b) in &raw.blocked {
        line(w, serde_json::json!({"kind": "blocked", "element": ids[*e], "blocker": ids[*b]}))?;
    }
    for (class, &e) in &raw.witnesses {
        if source.contains(class.as_str()) && !is_cell(e) {
            line(w, serde_json::json!({"kind": "witness", "class": iri(class), "element": ids[e], "exact": raw.witness_exact}))?;
        }
    }
    Ok(())
}
