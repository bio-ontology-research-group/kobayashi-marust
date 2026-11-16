//! `km classify --export-model FILE`: a model of the ontology over source
//! names, as JSON lines (`docs/MODEL-EXPORT.md`).
//!
//! The export is computed after the answer is published, from the same
//! frontend clause stream, so it never changes the answer and costs nothing
//! when it is not asked for. Routes:
//!
//! * `el-canonical`: the clause stream is EL++ (with optional positive ABox
//!   and residual clauses certified by [`crate::elcomplete::check_certificate`]).
//!   The canonical model of the completion ([`crate::elcomplete::el_model`]) is
//!   a model of the clause stream, and restricting labels to source names gives
//!   a model of the source ontology. Every satisfiable class witness is exact.
//! * `ht-bridge`: the native Konclude hypertableau bridge completion graph
//!   ([`crate::konclude_ht::bridge::bridge_model`]), combining the ontology
//!   consistency completion graph with per-class satisfiability completion
//!   graphs. May include `blocked` pairs representing finite unravellings.
//! * `cb-horn`: the CB engine's unit-fact context graph
//!   ([`crate::engine::cb_model`]), where each satisfiable context is an
//!   element, unit concept facts `⊤ → C(x)` form its label, and unit role facts
//!   `⊤ → r(x, f(x))` / `⊤ → r(f(x), x)` across `ctx.successors[f]` form its
//!   edges. Verified against all normalized clauses; declines when non-Horn
//!   disjunctions or equalities are not satisfied by the unit-fact graph.
//!
//! Every other input gets one `{"kind":"model","status":"declined",...}`
//! line with the reason.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::Write;
use std::path::Path;

use super::config::Config;
use super::{cb_to_ht, frontend_run, OrchestrateError};

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
    /// The role closure a consumer must apply to the edges.
    pub closure: &'static str,
}

fn line<W: Write>(w: &mut W, value: serde_json::Value) -> std::io::Result<()> {
    serde_json::to_writer(&mut *w, &value)?;
    w.write_all(b"\n")
}

fn parse_for_export(
    text: &str,
) -> Result<(frontend_run::Meta, crate::json_io::JInput), OrchestrateError> {
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

/// Write the export of `ont` to `out`. Returns a one-line status for stderr.
pub fn export(cfg: &Config, ont: &Path, out: &Path) -> Result<String, OrchestrateError> {
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
    let m = crate::elcomplete::el_model(el_input, el_meta.el_rbox_safe, el_meta.abox_inconsistent)?;
    if m.inconsistent {
        return Some(Ok(None));
    }
    let mut edge_set: HashSet<(usize, String, usize)> = m.edges.into_iter().collect();
    crate::engine::close_edges_under_rbox_rows(&el_input.rbox, m.contexts.len(), &mut edge_set);
    let mut edges: Vec<(usize, String, usize)> = edge_set.into_iter().collect();
    edges.sort();
    let witnesses: BTreeMap<String, usize> = m
        .contexts
        .iter()
        .enumerate()
        .map(|(i, c)| (c.clone(), i))
        .collect();
    let witness_exact_by_class = witnesses.keys().map(|k| (k.clone(), true)).collect();
    Some(Ok(Some(RawModel {
        route: "el-canonical",
        contexts: m.contexts,
        labels: m.labels,
        edges,
        blocked: Vec::new(),
        witness_exact: true,
        witness_exact_by_class,
        witnesses,
        closure: "none: the edges of each role are its extension (sub-roles lifted, chains and transitivity composed)",
    })))
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
    if m.inconsistent {
        return Ok(None);
    }
    let witnesses: BTreeMap<String, usize> = m
        .contexts
        .iter()
        .enumerate()
        .map(|(i, c)| (c.clone(), i))
        .collect();
    let witness_exact_by_class = witnesses.keys().map(|k| (k.clone(), true)).collect();
    Ok(Some(RawModel {
        route: "cb-horn",
        contexts: m.contexts,
        labels: m.labels,
        edges: m.edges,
        blocked: Vec::new(),
        witness_exact: true,
        witness_exact_by_class,
        witnesses,
        closure: "none: the edges of each role are closed under the RBox (sub-roles, inverses, symmetry, reflexivity, transitivity, and role chains)",
    }))
}

fn try_bridge_raw_model(
    text: &str,
    meta: &frontend_run::Meta,
    input: &crate::json_io::JInput,
) -> Result<Option<RawModel>, String> {
    let owned;
    let (ht_meta, ht_input) = if input.source_axioms.is_empty()
        || std::env::var_os("KM_NOMINALS").is_some()
    {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::remove_var("KM_NOMINALS");
        std::env::set_var("KM_ROUTE", "ht_bridge");
        std::env::set_var("KM_TRIGGER_ABSORB", "1");
        owned = parse_for_export(text).map_err(|e| e.to_string())?;
        (&owned.0, &owned.1)
    } else {
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
    let mut tin = cb_to_ht::convert(
        &ht_input.clauses,
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
    let mut bm = crate::konclude_ht::bridge::bridge_model(&tin, &ht_input.rbox)?;
    if bm.inconsistent {
        return Ok(None);
    }
    if !ht_input.nominal_abox.same.is_empty() {
        let mut changed = true;
        while changed {
            changed = false;
            for (a, b) in &ht_input.nominal_abox.same {
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
    crate::engine::close_edges_under_rbox_rows(&ht_input.rbox, bm.contexts.len(), &mut edge_set);
    let mut edges: Vec<(usize, String, usize)> = edge_set.into_iter().collect();
    edges.sort();

    let mut witnesses = BTreeMap::new();
    let mut witness_exact_by_class = BTreeMap::new();
    let mut all_exact = true;
    for (cname, elem_idx, exact) in bm.class_witnesses {
        witnesses.insert(cname.clone(), elem_idx);
        witness_exact_by_class.insert(cname, exact);
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
        closure,
    }))
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
    if force_cb
        || meta.route.starts_with("cb_")
        || meta.route == "nominals"
        || meta.route == "manual"
    {
        if !force_cb {
            if let Some(res) = try_el_raw_model(text, meta, input) {
                return res;
            }
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
    let iri = |short: &str| -> String {
        meta.iri_map
            .get(short)
            .cloned()
            .unwrap_or_else(|| short.to_string())
    };
    // Source classes: the frontend's named (non-fresh) classes.
    let source: BTreeSet<&str> = meta
        .named
        .iter()
        .chain(meta.declared.iter())
        .map(String::as_str)
        .filter(|&s| {
            !matches!(s, "owl:Thing" | "Thing" | "owl:Nothing" | "Nothing" | "⊤" | "⊥")
                && !meta.iri_map.get(s).is_some_and(|u| u.starts_with("_:"))
        })
        .collect();
    let data: BTreeSet<&str> = data_roles.iter().map(String::as_str).collect();
    let is_source_role =
        |r: &str| !r.starts_with("__") && !r.starts_with("Q_") && meta.iri_map.contains_key(r);
    // Data cells: contexts of datatype abstractions.
    let is_cell = |i: usize| {
        raw.contexts[i].starts_with("__dt__")
            || raw.labels[i]
                .iter()
                .any(|c| c.starts_with("__dt__") || c == "__sort__data")
            || raw
                .edges
                .iter()
                .any(|(_, r, t)| *t == i && data.contains(r.as_str()))
    };
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
    let object_edges: Vec<&(usize, String, usize)> = raw
        .edges
        .iter()
        .filter(|(f, r, t)| {
            !is_cell(*f) && !is_cell(*t) && is_source_role(r) && !data.contains(r.as_str())
        })
        .collect();
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
        let mut classes: Vec<String> = label
            .iter()
            .filter(|c| source.contains(c.as_str()))
            .map(|c| iri(c))
            .collect();
        classes.sort();
        classes.dedup();
        let context = &raw.contexts[i];
        let context = if source.contains(context.as_str()) {
            iri(context)
        } else {
            context.clone()
        };
        let mut obj = serde_json::json!({
            "kind": "element",
            "id": ids[i],
            "context": context,
            "classes": classes,
        });
        if !individuals[i].is_empty() {
            obj["individuals"] = serde_json::json!(individuals[i]);
        }
        line(w, obj)?;
    }
    for (f, r, t) in &object_edges {
        line(
            w,
            serde_json::json!({"kind": "edge", "role": iri(r), "from": ids[*f], "to": ids[*t]}),
        )?;
    }
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
            let cell = if raw.contexts[*t].starts_with("__dt__") {
                raw.contexts[*t].clone()
            } else {
                dts.first()
                    .cloned()
                    .unwrap_or_else(|| raw.contexts[*t].clone())
            };
            let literal = dts
                .iter()
                .find_map(|c| c.strip_prefix("__dt__val__").map(str::to_string));
            let mut obj = serde_json::json!({
                "kind": "value",
                "element": ids[*f],
                "property": iri(r),
                "cell": cell,
                "datatypes": dts,
            });
            if let Some(lit) = literal {
                obj["literal"] = serde_json::json!(lit);
            }
            line(w, obj)?;
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
            line(
                w,
                serde_json::json!({"kind": "witness", "class": iri(class), "element": ids[e], "exact": exact}),
            )?;
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
        let (meta, input) = parse_for_export(text).expect("parse_for_export");
        let cfg = Config::from_env();
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
        assert!(witnesses.contains_key("http://ex.org/A"), "witnesses: {:?}", witnesses);
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
