//! Producer mode starting from a `km classify --export-model` JSONL file
//! (`docs/MODEL-EXPORT.md`).
//!
//! Maps exported source-level elements, individuals, edges, witnesses, and
//! blocked nodes to the Lean checker's normal-form indices (`base.idx` /
//! `base.cl`), deterministically closes each element's label under the
//! normal form's fresh `urn:km:` names (forward Horn/universal/unit closure
//! paired with backward refutation from missing edges and source-label
//! exactness), runs the independent self-check (`check::verify`), and emits
//! `model0.hint` + `model0.wit`.

use crate::build::Config;
use crate::check;
use crate::emit;
use crate::engine::{CloseRes, Elem, Engine, Id, Model, Opts, NONE};
use crate::km::{Km, NOTHING, THING};
use crate::nf::Nf;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::time::Instant;

#[allow(dead_code)]
#[derive(Clone, Debug)]
enum JVal {
    Null,
    Bool(bool),
    Num(i64),
    Str(String),
    Arr(Vec<JVal>),
    Obj(BTreeMap<String, JVal>),
}

impl JVal {
    fn as_str(&self) -> Option<&str> {
        match self {
            JVal::Str(s) => Some(s.as_str()),
            _ => None,
        }
    }
    fn as_bool(&self) -> Option<bool> {
        match self {
            JVal::Bool(b) => Some(*b),
            _ => None,
        }
    }
    fn as_obj(&self) -> Option<&BTreeMap<String, JVal>> {
        match self {
            JVal::Obj(m) => Some(m),
            _ => None,
        }
    }
    fn str_field<'a>(&'a self, k: &str) -> Option<&'a str> {
        self.as_obj()?.get(k)?.as_str()
    }
    fn str_list(&self, k: &str) -> Vec<String> {
        let Some(m) = self.as_obj() else { return Vec::new() };
        let Some(JVal::Arr(a)) = m.get(k) else { return Vec::new() };
        a.iter().filter_map(|v| v.as_str().map(str::to_string)).collect()
    }
}

struct JParser<'a> {
    s: &'a str,
    b: &'a [u8],
    i: usize,
}

impl<'a> JParser<'a> {
    fn new(s: &'a str) -> Self {
        Self { s, b: s.as_bytes(), i: 0 }
    }
    fn skip_ws(&mut self) {
        while self.i < self.b.len() && matches!(self.b[self.i], b' ' | b'\t' | b'\r' | b'\n') {
            self.i += 1;
        }
    }
    fn parse_val(&mut self) -> Result<JVal, String> {
        self.skip_ws();
        if self.i >= self.b.len() {
            return Err("unexpected EOF".into());
        }
        match self.b[self.i] {
            b'"' => self.parse_str().map(JVal::Str),
            b'{' => self.parse_obj(),
            b'[' => self.parse_arr(),
            b't' => {
                if self.b[self.i..].starts_with(b"true") {
                    self.i += 4;
                    Ok(JVal::Bool(true))
                } else {
                    Err("bad literal".into())
                }
            }
            b'f' => {
                if self.b[self.i..].starts_with(b"false") {
                    self.i += 5;
                    Ok(JVal::Bool(false))
                } else {
                    Err("bad literal".into())
                }
            }
            b'n' => {
                if self.b[self.i..].starts_with(b"null") {
                    self.i += 4;
                    Ok(JVal::Null)
                } else {
                    Err("bad literal".into())
                }
            }
            c if c == b'-' || c.is_ascii_digit() => self.parse_num(),
            c => Err(format!("unexpected char '{}'", c as char)),
        }
    }
    fn parse_str(&mut self) -> Result<String, String> {
        self.i += 1; // skip '"'
        let start = self.i;
        while self.i < self.b.len() {
            let c = self.b[self.i];
            if c == b'"' {
                let slice = &self.s[start..self.i];
                self.i += 1;
                return Ok(slice.to_string());
            }
            if c == b'\\' {
                break;
            }
            self.i += 1;
        }
        let mut out = String::from(&self.s[start..self.i]);
        while self.i < self.b.len() {
            let c = self.b[self.i];
            if c == b'"' {
                self.i += 1;
                return Ok(out);
            }
            if c == b'\\' {
                self.i += 1;
                if self.i >= self.b.len() {
                    return Err("unterminated escape".into());
                }
                let e = self.b[self.i];
                self.i += 1;
                match e {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'n' => out.push('\n'),
                    b'r' => out.push('\r'),
                    b't' => out.push('\t'),
                    b'b' => out.push('\x08'),
                    b'f' => out.push('\x0c'),
                    b'u' => {
                        if self.i + 4 > self.b.len() {
                            return Err("short \\u escape".into());
                        }
                        let hex = &self.s[self.i..self.i + 4];
                        let code = u32::from_str_radix(hex, 16).map_err(|e| e.to_string())?;
                        if let Some(ch) = char::from_u32(code) {
                            out.push(ch);
                        }
                        self.i += 4;
                    }
                    other => out.push(other as char),
                }
            } else {
                let seg_start = self.i;
                self.i += 1;
                while self.i < self.b.len() && self.b[self.i] != b'"' && self.b[self.i] != b'\\' {
                    self.i += 1;
                }
                out.push_str(&self.s[seg_start..self.i]);
            }
        }
        Err("unterminated string".into())
    }
    fn parse_num(&mut self) -> Result<JVal, String> {
        let start = self.i;
        if self.b[self.i] == b'-' {
            self.i += 1;
        }
        while self.i < self.b.len() && (self.b[self.i].is_ascii_digit() || matches!(self.b[self.i], b'.' | b'e' | b'E' | b'+' | b'-')) {
            self.i += 1;
        }
        let s = std::str::from_utf8(&self.b[start..self.i]).map_err(|e| e.to_string())?;
        Ok(JVal::Num(s.parse::<i64>().unwrap_or(0)))
    }
    fn parse_arr(&mut self) -> Result<JVal, String> {
        self.i += 1; // '['
        let mut v = Vec::new();
        loop {
            self.skip_ws();
            if self.i < self.b.len() && self.b[self.i] == b']' {
                self.i += 1;
                return Ok(JVal::Arr(v));
            }
            v.push(self.parse_val()?);
            self.skip_ws();
            if self.i < self.b.len() && self.b[self.i] == b',' {
                self.i += 1;
            }
        }
    }
    fn parse_obj(&mut self) -> Result<JVal, String> {
        self.i += 1; // '{'
        let mut m = BTreeMap::new();
        loop {
            self.skip_ws();
            if self.i < self.b.len() && self.b[self.i] == b'}' {
                self.i += 1;
                return Ok(JVal::Obj(m));
            }
            let k = self.parse_str()?;
            self.skip_ws();
            if self.i >= self.b.len() || self.b[self.i] != b':' {
                return Err("expected ':'".into());
            }
            self.i += 1;
            let v = self.parse_val()?;
            m.insert(k, v);
            self.skip_ws();
            if self.i < self.b.len() && self.b[self.i] == b',' {
                self.i += 1;
            }
        }
    }
}

fn json_str(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            c if (c as u32) < 0x20 => {
                let _ = write!(o, "\\u{:04x}", c as u32);
            }
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

#[allow(dead_code)]
#[derive(Default)]
struct ExportElem {
    id: String,
    classes: Vec<String>,
    individuals: Vec<String>,
}

pub fn from_export(nf: &Nf, km: Option<&Km>, cfg: &Config, export_text: &str, outdir: &str) -> String {
    let mut dirty0: HashMap<u32, Vec<u32>> = HashMap::new();
    let res0 = from_export_slot(nf, km, cfg, export_text, outdir, 0, None, &mut dirty0);
    if !dirty0.is_empty() && export_text.contains("\"aux_element\"") {
        let mut aux_buf = String::from("{\"kind\":\"model\",\"status\":\"ok\",\"route\":\"ht-bridge\"}\n");
        for raw_line in export_text.lines() {
            let line = raw_line.trim();
            if line.contains("\"aux_element\"") {
                aux_buf.push_str(&line.replace("\"aux_element\"", "\"element\""));
                aux_buf.push('\n');
            } else if line.contains("\"aux_edge\"") {
                aux_buf.push_str(&line.replace("\"aux_edge\"", "\"edge\""));
                aux_buf.push('\n');
            } else if line.contains("\"aux_same\"") {
                aux_buf.push_str(&line.replace("\"aux_same\"", "\"same\""));
                aux_buf.push('\n');
            } else if line.contains("\"aux_witness\"") {
                aux_buf.push_str(&line.replace("\"aux_witness\"", "\"witness\""));
                aux_buf.push('\n');
            }
        }
        let target_classes: BTreeSet<u32> = dirty0.keys().copied().collect();
        let mut dirty1: HashMap<u32, Vec<u32>> = HashMap::new();
        let res1 = from_export_slot(
            nf,
            km,
            cfg,
            &aux_buf,
            outdir,
            1,
            Some((&target_classes, &dirty0)),
            &mut dirty1,
        );
        if res1.contains("\"ok\":true") && dirty1.is_empty() {
            return res0
                .replace("\"export_only_full\":false", "\"export_only_full\":true")
                .replace("\"plus_search_full\":false", "\"plus_search_full\":true");
        }
    }
    res0
}

#[allow(clippy::too_many_arguments)]
fn from_export_slot(
    nf: &Nf,
    km: Option<&Km>,
    cfg: &Config,
    export_text: &str,
    outdir: &str,
    slot_idx: usize,
    aux_targets: Option<(&BTreeSet<u32>, &HashMap<u32, Vec<u32>>)>,
    dirty_out: &mut HashMap<u32, Vec<u32>>,
) -> String {
    let t0 = Instant::now();
    let deadline = t0 + std::time::Duration::from_secs_f64(cfg.time_limit);
    let node_budget = 100_000 + 40 * (nf.n + nf.noms.len());
    let opt = Opts { loops: cfg.loops, deadline: Some(deadline), node_budget, ..Opts::default() };
    let mut en = Engine::new(nf, opt);
    if let Some(d) = cfg.data.as_ref().filter(|d| !d.is_empty()) {
        let v = crate::data::Values::new(d);
        if v.complete() {
            en.set_data(d.clone(), v);
        }
    }

    let mut anon_to_iri: HashMap<&str, &str> = HashMap::new();
    for (iri, _) in &nf.nominal {
        if let Some(rest) = iri.strip_prefix("urn:km:owl-anon:") {
            let trimmed = rest.trim_start_matches('#');
            if !trimmed.is_empty() {
                anon_to_iri.insert(trimmed, iri.as_str());
            }
            anon_to_iri.insert(rest, iri.as_str());
        }
    }
    let map_ind = |raw: &str| -> String {
        if let Some(x) = raw.strip_prefix("_:") {
            if let Some(&mapped) = anon_to_iri.get(x) {
                return mapped.to_string();
            }
            let x_trim = x.trim_start_matches('#');
            if let Some(&mapped) = anon_to_iri.get(x_trim) {
                return mapped.to_string();
            }
            return format!("urn:km:owl-anon:#{}", x);
        }
        if let Some(rest) = raw.strip_prefix("urn:km:owl-anon:") {
            let x_trim = rest.trim_start_matches('#');
            if let Some(&mapped) = anon_to_iri.get(x_trim) {
                return mapped.to_string();
            }
        }
        if let Some(x) = raw.strip_prefix('#') {
            if let Some(&mapped) = anon_to_iri.get(x) {
                return mapped.to_string();
            }
        }
        raw.to_string()
    };

    let mut route = String::from("export");
    let mut exp_status = String::from("ok");
    let mut exp_elems: Vec<ExportElem> = Vec::new();
    let mut id_to_idx: HashMap<String, usize> = HashMap::new();
    let mut exp_edges: Vec<(String, String, String)> = Vec::new();
    let mut exp_sames: Vec<(Vec<String>, Option<String>)> = Vec::new();
    let mut exp_blocked: Vec<(String, String)> = Vec::new();
    let mut exp_witnesses: Vec<(String, String, bool)> = Vec::new();

    for (lno, raw_line) in export_text.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let val = match JParser::new(line).parse_val() {
            Ok(v) => v,
            Err(e) => {
                let msg = format!("line {}: {}", lno + 1, e);
                return format!(
                    "{{\"ok\":false,\"status\":\"bad-export\",\"why\":{},\"reason\":{}}}",
                    json_str(&msg),
                    json_str(&msg)
                );
            }
        };
        let kind = val.str_field("kind").unwrap_or("");
        match kind {
            "model" => {
                if let Some(r) = val.str_field("route") {
                    route = r.to_string();
                }
                if let Some(st) = val.str_field("status") {
                    exp_status = st.to_string();
                    if st != "ok" && st != "partial" {
                        let why = val.str_field("reason").unwrap_or(st);
                        return format!(
                            "{{\"ok\":false,\"status\":{},\"route\":{},\"why\":{},\"reason\":{}}}",
                            json_str(st),
                            json_str(&route),
                            json_str(why),
                            json_str(why)
                        );
                    }
                }
            }
            "element" => {
                let id = val.str_field("id").unwrap_or("").to_string();
                let classes = val.str_list("classes");
                let individuals: Vec<String> = val.str_list("individuals").into_iter().map(|s| map_ind(&s)).collect();
                if let Some(&idx) = id_to_idx.get(&id) {
                    exp_elems[idx].classes.extend(classes);
                    exp_elems[idx].individuals.extend(individuals);
                } else {
                    let idx = exp_elems.len();
                    id_to_idx.insert(id.clone(), idx);
                    exp_elems.push(ExportElem { id, classes, individuals });
                }
            }
            "edge" => {
                let from = val.str_field("from").unwrap_or("").to_string();
                let role = val.str_field("role").unwrap_or("").to_string();
                let to = val.str_field("to").unwrap_or("").to_string();
                if !from.is_empty() && !role.is_empty() && !to.is_empty() {
                    for ep in [&from, &to] {
                        if !id_to_idx.contains_key(ep) {
                            let idx = exp_elems.len();
                            id_to_idx.insert((*ep).clone(), idx);
                            exp_elems.push(ExportElem { id: (*ep).clone(), ..ExportElem::default() });
                        }
                    }
                    exp_edges.push((from, role, to));
                }
            }
            "same" => {
                let inds: Vec<String> = val.str_list("individuals").into_iter().map(|s| map_ind(&s)).collect();
                let el = val.str_field("element").map(str::to_string);
                if !inds.is_empty() {
                    exp_sames.push((inds, el));
                }
            }
            "blocked" => {
                let el = val.str_field("element").unwrap_or("").to_string();
                let blk = val.str_field("blocker").unwrap_or("").to_string();
                if !el.is_empty() && !blk.is_empty() {
                    exp_blocked.push((el, blk));
                }
            }
            "witness" => {
                let cls = val.str_field("class").unwrap_or("").to_string();
                let el = val.str_field("element").unwrap_or("").to_string();
                let exact = val.as_obj().and_then(|o| o.get("exact")).and_then(|v| v.as_bool()).unwrap_or(true);
                if !cls.is_empty() && !el.is_empty() {
                    exp_witnesses.push((cls, el, exact));
                }
            }
            _ => {}
        }
    }

    // Ensure at least one element exists for consistent empty ontologies
    if exp_elems.is_empty() {
        id_to_idx.insert("e0".into(), 0);
        exp_elems.push(ExportElem { id: "e0".into(), ..ExportElem::default() });
    }

    // Apply `same` groups and ensure every ontology nominal is placed on exactly one element
    let mut ind_elem: HashMap<String, usize> = HashMap::new();
    for (idx, e) in exp_elems.iter_mut().enumerate() {
        for ind in e.individuals.drain(..) {
            ind_elem.entry(ind).or_insert(idx);
        }
    }
    for (grp, el_opt) in &exp_sames {
        let target_idx = el_opt
            .as_ref()
            .and_then(|id| id_to_idx.get(id).copied())
            .or_else(|| grp.iter().find_map(|ind| ind_elem.get(ind).copied()))
            .unwrap_or(0);
        for ind in grp {
            ind_elem.insert(ind.clone(), target_idx);
        }
    }
    let mut inds_by_elem: Vec<Vec<String>> = vec![Vec::new(); exp_elems.len()];
    for (ind, &idx) in &ind_elem {
        if idx < inds_by_elem.len() {
            inds_by_elem[idx].push(ind.clone());
        }
    }
    let nom_lookup: HashMap<&str, u32> = nf.nominal.iter().map(|(i, c)| (i.as_str(), *c)).collect();
    let mut placed_noms: BTreeSet<u32> = BTreeSet::new();
    for (idx, e) in exp_elems.iter_mut().enumerate() {
        let mut inds = std::mem::take(&mut inds_by_elem[idx]);
        inds.sort_unstable();
        let mut kept = Vec::with_capacity(inds.len());
        for ind in inds {
            if let Some(&c) = nom_lookup.get(ind.as_str()) {
                if placed_noms.insert(c) {
                    kept.push(ind);
                }
            } else {
                kept.push(ind);
            }
        }
        e.individuals = kept;
    }
    for (iri, c) in &nf.nominal {
        if nf.is_nom[*c as usize] && !placed_noms.contains(c) {
            placed_noms.insert(*c);
            let idx = exp_elems.len();
            let id = format!("__ind_{}", idx);
            id_to_idx.insert(id.clone(), idx);
            exp_elems.push(ExportElem { id, classes: Vec::new(), individuals: vec![iri.clone()] });
            ind_elem.insert(iri.clone(), idx);
        }
    }
    let has_unnamed_self_nom = nf.noms.iter().any(|&c| nf.cname[c as usize].is_none());
    if has_unnamed_self_nom {
        en.opt.loops = false;
    }
    let mut unnamed_nom_map: Vec<(String, u32)> = Vec::new();
    for &c in &nf.noms {
        if !placed_noms.contains(&c) {
            placed_noms.insert(c);
            let idx = exp_elems.len();
            let id = format!("__ind_{}", idx);
            let syn_iri = format!("__unnamed_nom_{}", c);
            id_to_idx.insert(id.clone(), idx);
            exp_elems.push(ExportElem {
                id,
                classes: Vec::new(),
                individuals: vec![syn_iri.clone()],
            });
            ind_elem.insert(syn_iri.clone(), idx);
            unnamed_nom_map.push((syn_iri, c));
        }
    }

    // Resolve `blocked` pairs by copying blocker classes and outgoing edges to the blocked element
    for e in &mut exp_elems {
        e.classes.sort_unstable();
        e.classes.dedup();
    }
    if !exp_blocked.is_empty() {
        let mut edge_set: std::collections::HashSet<(usize, String, usize)> =
            std::collections::HashSet::with_capacity(exp_edges.len() * 2);
        let mut out_by_elem: Vec<Vec<(String, usize)>> = vec![Vec::new(); exp_elems.len()];
        for (f, r, t) in &exp_edges {
            if let (Some(&fi), Some(&ti)) = (id_to_idx.get(f), id_to_idx.get(t)) {
                if edge_set.insert((fi, r.clone(), ti)) {
                    out_by_elem[fi].push((r.clone(), ti));
                }
            }
        }
        for _pass in 0..4 {
            for (el_id, blk_id) in &exp_blocked {
                let (Some(&ei), Some(&bi)) = (id_to_idx.get(el_id), id_to_idx.get(blk_id)) else { continue };
                let blk_classes = exp_elems[bi].classes.clone();
                exp_elems[ei].classes.extend(blk_classes);
                exp_elems[ei].classes.sort_unstable();
                exp_elems[ei].classes.dedup();
                let blk_out: Vec<(String, usize)> = out_by_elem[bi]
                    .iter()
                    .filter(|(r, ti)| {
                        if *ti < bi && exp_elems[*ti].individuals.is_empty() {
                            let ti_classes = &exp_elems[*ti].classes;
                            let covered = out_by_elem[ei].iter().any(|(r2, ey)| {
                                r2 == r
                                    && ti_classes
                                        .iter()
                                        .all(|c| exp_elems[*ey].classes.binary_search(c).is_ok())
                            });
                            if covered {
                                return false;
                            }
                        }
                        true
                    })
                    .cloned()
                    .collect();
                for (r, ti) in blk_out {
                    let target_i = if ti == ei && ei != bi { bi } else { ti };
                    if edge_set.insert((ei, r.clone(), target_i)) {
                        out_by_elem[ei].push((r.clone(), target_i));
                        exp_edges.push((el_id.clone(), r, exp_elems[target_i].id.clone()));
                    }
                }
            }
        }
    }

    let n = nf.n;
    let thing_c = nf.cidx.get(THING).copied();
    let mut rowclass = vec![false; n];
    let mut classes: Vec<u32> = Vec::new();
    for c in 0..n as u32 {
        if nf.named[c as usize] {
            let iri = nf.cname_of(c);
            if iri != THING && iri != NOTHING {
                rowclass[c as usize] = true;
                classes.push(c);
            }
        }
    }
    en.rowclasses = en.sets.intern(classes.clone());
    en.is_rowclass = rowclass.clone();
    let mut nom_map: HashMap<&str, u32> = nf.nominal.iter().map(|(i, c)| (i.as_str(), *c)).collect();
    for (syn_iri, c) in &unnamed_nom_map {
        nom_map.insert(syn_iri.as_str(), *c);
    }

    let mut m = Model::new();
    let k_elems = exp_elems.len();
    struct BitMatrix {
        words_per_row: usize,
        data: Vec<u64>,
    }
    impl BitMatrix {
        fn new(rows: usize, cols: usize) -> Self {
            let words_per_row = (cols + 63) / 64;
            Self {
                words_per_row,
                data: vec![0u64; rows * words_per_row],
            }
        }
        #[inline]
        fn get(&self, r: usize, c: usize) -> bool {
            let idx = r * self.words_per_row + (c >> 6);
            (self.data[idx] >> (c & 63)) & 1 != 0
        }
        #[inline]
        fn set(&mut self, r: usize, c: usize, val: bool) {
            let idx = r * self.words_per_row + (c >> 6);
            let mask = 1u64 << (c & 63);
            if val {
                self.data[idx] |= mask;
            } else {
                self.data[idx] &= !mask;
            }
        }
    }
    let mut pos = BitMatrix::new(k_elems, n);
    let mut pos_list: Vec<Vec<u32>> = vec![Vec::new(); k_elems];

    for (idx, ee) in exp_elems.iter().enumerate() {
        if let Some(tc) = thing_c {
            if !pos.get(idx, tc as usize) {
                pos.set(idx, tc as usize, true);
                pos_list[idx].push(tc);
            }
        }
        for c_iri in &ee.classes {
            if let Some(&c) = nf.cidx.get(c_iri.as_str()) {
                if !pos.get(idx, c as usize) {
                    pos.set(idx, c as usize, true);
                    pos_list[idx].push(c);
                }
            }
        }
        let mut has_nom = false;
        for i_iri in &ee.individuals {
            let o_opt = nom_map
                .get(i_iri.as_str())
                .copied()
                .or_else(|| i_iri.strip_prefix("__nom_c_").and_then(|s| s.parse::<u32>().ok()));
            if let Some(o) = o_opt {
                if !pos.get(idx, o as usize) {
                    pos.set(idx, o as usize, true);
                    pos_list[idx].push(o);
                }
                has_nom = true;
            }
        }
        let mut seed_vec = pos_list[idx].clone();
        seed_vec.sort_unstable();
        let seed_id = en.sets.intern(seed_vec);
        let el_id = m.push_elem(Elem {
            ty: seed_id,
            forced: seed_id,
            forbid: 0,
            target: seed_id,
            edges: Vec::new(),
            pending: Vec::new(),
            nom: has_nom,
            pinned: true,
            owner: NONE,
            alive: true,
        });
        debug_assert_eq!(el_id as usize, idx);
        for i_iri in &ee.individuals {
            let o_opt = nom_map
                .get(i_iri.as_str())
                .copied()
                .or_else(|| i_iri.strip_prefix("__nom_c_").and_then(|s| s.parse::<u32>().ok()));
            if let Some(o) = o_opt {
                m.set_nom(o, el_id);
            }
        }
    }

    let allow_loops = cfg.loops && !has_unnamed_self_nom;
    // Add exported edges
    for (from_id, role_iri, to_id) in &exp_edges {
        let (Some(&u), Some(&v)) = (id_to_idx.get(from_id), id_to_idx.get(to_id)) else { continue };
        if u == v && !allow_loops && !m.elems[u].nom {
            continue;
        }
        let r_opt = if let Some(stripped) = role_iri.strip_prefix('^') {
            nf.ridx.get(stripped).map(|&r| 2 * r + 1)
        } else {
            nf.ridx.get(role_iri.as_str()).map(|&r| 2 * r)
        };
        if let Some(r) = r_opt {
            let l = en.lab_of_role(r);
            en.add_edge(&mut m, u as Id, v as Id, l);
        }
    }

    // Close role chains `r1 o r2 -> s` over the fixed graph `m` so universal/existential
    // restrictions on composite roles see the composed edges
    if !nf.chains.is_empty() {
        loop {
            let mut new_edges: Vec<(Id, Id, u32)> = Vec::new();
            for (body, s) in &nf.chains {
                if body.len() < 2 {
                    continue;
                }
                let ls = en.lab_of_role(*s);
                for u in 0..k_elems as Id {
                    let mut reach: Vec<Id> = vec![u];
                    for &r_step in body {
                        let mut next_reach: Vec<Id> = Vec::new();
                        for &curr in &reach {
                            for &(nxt, l) in &m.elems[curr as usize].edges {
                                if en.labs.has(l, r_step) {
                                    next_reach.push(nxt);
                                }
                            }
                        }
                        next_reach.sort_unstable();
                        next_reach.dedup();
                        reach = next_reach;
                        if reach.is_empty() {
                            break;
                        }
                    }
                    for v in reach {
                        if u == v && !allow_loops && !m.elems[u as usize].nom {
                            continue;
                        }
                        let already = m.edge_label(u, v).map(|l0| en.labs.has(l0, *s)).unwrap_or(false);
                        if !already {
                            new_edges.push((u, v, ls));
                        }
                    }
                }
            }
            if new_edges.is_empty() {
                break;
            }
            for (u, v, ls) in new_edges {
                en.add_edge(&mut m, u, v, ls);
            }
        }
    }

    // Step 1: Worklist forward pure-Horn + universal closure on `pos` so implied source
    // superclasses and positive definers are present before initializing `neg` on complement source names
    let mut q_pos: Vec<(usize, u32)> = Vec::new();
    for x in 0..k_elems {
        for &g in &nf.gci_empty {
            let h = &nf.gci[g as usize].1;
            if h.len() == 1 {
                let h0 = h[0];
                if !pos.get(x, h0 as usize) {
                    pos.set(x, h0 as usize, true);
                    pos_list[x].push(h0);
                }
            }
        }
        for &a in &pos_list[x] {
            q_pos.push((x, a));
        }
    }
    while let Some((x, a)) = q_pos.pop() {
        for &g in nf.gci_by_body.get(a) {
            let (body, head) = &nf.gci[g as usize];
            if head.len() == 1 && !pos.get(x, head[0] as usize) && body.iter().all(|&b| pos.get(x, b as usize)) {
                let h0 = head[0];
                pos.set(x, h0 as usize, true);
                pos_list[x].push(h0);
                q_pos.push((x, h0));
            }
        }
        for &(s, c) in nf.all_by.get(a) {
            for &(y, l) in &m.elems[x].edges {
                if en.labs.has(l, s) && !pos.get(y as usize, c as usize) {
                    pos.set(y as usize, c as usize, true);
                    pos_list[y as usize].push(c);
                    q_pos.push((y as usize, c));
                }
            }
        }
        for &(r, b) in nf.ex_by.get(a) {
            if nf.named[b as usize] || nf.is_nom[b as usize] {
                continue;
            }
            let mut already = false;
            let mut only_y = 0usize;
            let mut cnt = 0usize;
            for &(y, l) in &m.elems[x].edges {
                if en.labs.has(l, r) {
                    if pos.get(y as usize, b as usize) {
                        already = true;
                        break;
                    }
                    only_y = y as usize;
                    cnt += 1;
                }
            }
            if !already && cnt == 1 && !pos.get(only_y, b as usize) {
                pos.set(only_y, b as usize, true);
                pos_list[only_y].push(b);
                q_pos.push((only_y, b));
            }
        }
        for &(k, r, b) in nf.ge_by.get(a) {
            if nf.named[b as usize] || nf.is_nom[b as usize] {
                continue;
            }
            let cands: Vec<usize> = m.elems[x]
                .edges
                .iter()
                .filter_map(|&(y, l)| en.labs.has(l, r).then_some(y as usize))
                .collect();
            if cands.len() == k as usize {
                for y0 in cands {
                    if !pos.get(y0, b as usize) {
                        pos.set(y0, b as usize, true);
                        pos_list[y0].push(b);
                        q_pos.push((y0, b));
                    }
                }
            }
        }
    }

    // Step 1b: Filter multi-target existentials by required source superclasses and outgoing roles
    fn can_satisfy_filler_rec(
        y: usize,
        b: u32,
        depth: usize,
        nf: &Nf,
        pos: &BitMatrix,
        pos_list: &[Vec<u32>],
        m: &Model,
        en: &Engine,
    ) -> bool {
        let bi = b as usize;
        if pos.get(y, bi) {
            return true;
        }
        if (nf.named[bi] || nf.is_nom[bi]) && !pos.get(y, bi) {
            return false;
        }
        if en.has_data[bi] {
            if en.dreq.get(bi).copied().unwrap_or(0) > 0 {
                return false;
            }
            if pos_list[y].iter().any(|&p| en.has_conflict_peer(b, p)) {
                return false;
            }
        }
        let mut local_added: Vec<u32> = vec![b];
        let mut idx = 0usize;
        while idx < local_added.len() && local_added.len() <= 32 {
            let cur = local_added[idx];
            idx += 1;
            for &(s, c) in nf.ex_by.get(cur) {
                let has_s = m.elems[y].edges.iter().any(|&(z, l)| {
                    en.labs.has(l, s)
                        && (pos.get(z as usize, c as usize)
                            || (depth < 4
                                && can_satisfy_filler_rec(
                                    z as usize,
                                    c,
                                    depth + 1,
                                    nf,
                                    pos,
                                    pos_list,
                                    m,
                                    en,
                                )))
                });
                if !has_s {
                    return false;
                }
            }
            for &(k, s, c) in nf.ge_by.get(cur) {
                let cnt_s = m.elems[y]
                    .edges
                    .iter()
                    .filter(|&&(z, l)| {
                        en.labs.has(l, s)
                            && (pos.get(z as usize, c as usize)
                                || (depth < 4
                                    && can_satisfy_filler_rec(
                                        z as usize,
                                        c,
                                        depth + 1,
                                        nf,
                                        pos,
                                        pos_list,
                                        m,
                                        en,
                                    )))
                    })
                    .count();
                if cnt_s < k as usize {
                    return false;
                }
            }
            if nf.has_le[cur as usize] {
                for &(k, s, c) in nf.le_by.get(cur) {
                    let cnt_s = m.elems[y]
                        .edges
                        .iter()
                        .filter(|&&(z, l)| en.labs.has(l, s) && pos.get(z as usize, c as usize))
                        .count();
                    if cnt_s > k as usize {
                        return false;
                    }
                }
            }
            for &(s, c) in nf.all_by.get(cur) {
                for &(z, l) in &m.elems[y].edges {
                    if en.labs.has(l, s)
                        && !pos.get(z as usize, c as usize)
                        && (depth >= 4
                            || !can_satisfy_filler_rec(
                                z as usize,
                                c,
                                depth + 1,
                                nf,
                                pos,
                                pos_list,
                                m,
                                en,
                            ))
                    {
                        return false;
                    }
                }
            }
            for &gi in nf.gci_by_body.get(cur) {
                let (body_g, head_g) = &nf.gci[gi as usize];
                if body_g
                    .iter()
                    .all(|&x_b| pos.get(y, x_b as usize) || local_added.contains(&x_b))
                {
                    if head_g.is_empty() {
                        return false;
                    }
                    if head_g.len() == 1 {
                        let h0 = head_g[0];
                        let h0i = h0 as usize;
                        if (nf.named[h0i] || nf.is_nom[h0i]) && !pos.get(y, h0i) {
                            return false;
                        }
                        if !pos.get(y, h0i) && !local_added.contains(&h0) {
                            if en.has_data[h0i]
                                && (en.dreq.get(h0i).copied().unwrap_or(0) > 0
                                    || pos_list[y].iter().any(|&p| en.has_conflict_peer(h0, p)))
                            {
                                return false;
                            }
                            local_added.push(h0);
                        }
                    } else {
                        let mut sat_h: Option<u32> = None;
                        let mut sat_cnt = 0usize;
                        for &h in head_g {
                            let hi = h as usize;
                            let ok = if pos.get(y, hi) || local_added.contains(&h) {
                                true
                            } else if nf.named[hi] || nf.is_nom[hi] {
                                false
                            } else if depth < 4 {
                                can_satisfy_filler_rec(y, h, depth + 1, nf, pos, pos_list, m, en)
                            } else {
                                true
                            };
                            if ok {
                                sat_h = Some(h);
                                sat_cnt += 1;
                                if sat_cnt > 1 {
                                    break;
                                }
                            }
                        }
                        if sat_cnt == 0 {
                            return false;
                        }
                        if sat_cnt == 1 {
                            let h0 = sat_h.unwrap();
                            let h0i = h0 as usize;
                            if !pos.get(y, h0i) && !local_added.contains(&h0) {
                                if en.has_data[h0i]
                                    && (en.dreq.get(h0i).copied().unwrap_or(0) > 0
                                        || pos_list[y].iter().any(|&p| en.has_conflict_peer(h0, p)))
                                {
                                    return false;
                                }
                                local_added.push(h0);
                            }
                        }
                    }
                }
            }
        }
        true
    }
    let can_satisfy_filler =
        |y: usize, b: u32, pos: &BitMatrix, pos_list: &[Vec<u32>], m: &Model, en: &Engine| -> bool {
            can_satisfy_filler_rec(y, b, 0, nf, pos, pos_list, m, en)
        };
    for x in 0..k_elems {
        let pos_x = pos_list[x].clone();
        for a in pos_x {
            for &(r, b) in nf.ex_by.get(a) {
                let already = m.elems[x]
                    .edges
                    .iter()
                    .any(|&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize));
                if !already {
                    let mut first_y: Option<usize> = None;
                    let mut cnt = 0usize;
                    for &(y, l) in &m.elems[x].edges {
                        if en.labs.has(l, r) && can_satisfy_filler(y as usize, b, &pos, &pos_list, &m, &en) {
                            if first_y.is_none() {
                                first_y = Some(y as usize);
                            }
                            cnt += 1;
                            if cnt > 1 {
                                break;
                            }
                        }
                    }
                    if let Some(only_y) = first_y {
                        if (cnt == 1 || !(nf.named[b as usize] || nf.is_nom[b as usize]))
                            && !pos.get(only_y, b as usize)
                        {
                            pos.set(only_y, b as usize, true);
                            pos_list[only_y].push(b);
                            q_pos.push((only_y, b));
                        }
                    }
                }
            }
        }
    }
    while let Some((x, a)) = q_pos.pop() {
        for &g in nf.gci_by_body.get(a) {
            let (body, head) = &nf.gci[g as usize];
            if head.len() == 1 && !pos.get(x, head[0] as usize) && body.iter().all(|&b| pos.get(x, b as usize)) {
                let h0 = head[0];
                pos.set(x, h0 as usize, true);
                pos_list[x].push(h0);
                q_pos.push((x, h0));
            }
        }
        for &(s, c) in nf.all_by.get(a) {
            for &(y, l) in &m.elems[x].edges {
                if en.labs.has(l, s) && !pos.get(y as usize, c as usize) {
                    pos.set(y as usize, c as usize, true);
                    pos_list[y as usize].push(c);
                    q_pos.push((y as usize, c));
                }
            }
        }
        for &(r, b) in nf.ex_by.get(a) {
            let already = m.elems[x]
                .edges
                .iter()
                .any(|&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize));
            if !already {
                let mut first_y: Option<usize> = None;
                let mut cnt = 0usize;
                for &(y, l) in &m.elems[x].edges {
                    if en.labs.has(l, r) && can_satisfy_filler(y as usize, b, &pos, &pos_list, &m, &en) {
                        if first_y.is_none() {
                            first_y = Some(y as usize);
                        }
                        cnt += 1;
                        if cnt > 1 {
                            break;
                        }
                    }
                }
                if let Some(only_y) = first_y {
                    if (cnt == 1 || !(nf.named[b as usize] || nf.is_nom[b as usize]))
                        && !pos.get(only_y, b as usize)
                    {
                        pos.set(only_y, b as usize, true);
                        pos_list[only_y].push(b);
                        q_pos.push((only_y, b));
                    }
                }
            }
        }
    }

    let named_or_nom: Vec<u32> = (0..n as u32)
        .filter(|&c| nf.named[c as usize] || nf.is_nom[c as usize])
        .collect();
    let data_rel_concepts: Vec<u32> = if en.data.is_some() {
        (0..n as u32).filter(|&a| en.has_data[a as usize]).collect()
    } else {
        Vec::new()
    };

    let mut any_modal_filler = vec![false; n];
    for &(_, _, b) in &nf.ex {
        if (b as usize) < n {
            any_modal_filler[b as usize] = true;
        }
    }
    for &(_, _, _, b) in &nf.ge {
        if (b as usize) < n {
            any_modal_filler[b as usize] = true;
        }
    }
    for &(_, _, _, b) in &nf.le {
        if (b as usize) < n {
            any_modal_filler[b as usize] = true;
        }
    }
    for &(_, _, b) in &nf.all {
        if (b as usize) < n {
            any_modal_filler[b as usize] = true;
        }
    }

    let is_simple_inert_on = |y: usize, c: u32, pos: &BitMatrix, pos_list: &[Vec<u32>], en: &Engine| -> bool {
        let ci = c as usize;
        if ci >= n
            || nf.named[ci]
            || nf.is_nom[ci]
            || (en.has_data[ci]
                && (en.dreq.get(ci).copied().unwrap_or(0) > 0
                    || pos_list[y].iter().any(|&p| en.has_conflict_peer(c, p))))
            || !nf.ex_by.get(c).is_empty()
            || !nf.ge_by.get(c).is_empty()
            || !nf.all_by.get(c).is_empty()
            || nf.has_le[ci]
        {
            return false;
        }
        for &gi2 in nf.gci_by_body.get(c) {
            let b_g = &nf.gci[gi2 as usize].0;
            if !b_g
                .iter()
                .any(|&b| b != c && (nf.named[b as usize] || nf.is_nom[b as usize]) && !pos.get(y, b as usize))
            {
                return false;
            }
        }
        true
    };

    let is_locally_inert_disjunct = |x: usize, h: u32, pos: &BitMatrix, pos_list: &[Vec<u32>], m: &Model, en: &Engine| -> bool {
        let hi = h as usize;
        if hi >= n
            || nf.named[hi]
            || nf.is_nom[hi]
            || (en.has_data[hi]
                && (en.dreq.get(hi).copied().unwrap_or(0) > 0
                    || pos_list[x].iter().any(|&p| en.has_conflict_peer(h, p))))
            || any_modal_filler[hi]
        {
            return false;
        }
        for &(r, b) in nf.ex_by.get(h) {
            if !m.elems[x]
                .edges
                .iter()
                .any(|&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize))
            {
                return false;
            }
        }
        for &(k, r, b) in nf.ge_by.get(h) {
            if m.elems[x]
                .edges
                .iter()
                .filter(|&&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize))
                .count()
                < k as usize
            {
                return false;
            }
        }
        if nf.has_le[hi] {
            for &(k, r, _) in nf.le_by.get(h) {
                if m.elems[x]
                    .edges
                    .iter()
                    .filter(|&&(_, l)| en.labs.has(l, r))
                    .count()
                    > k as usize
                {
                    return false;
                }
            }
        }
        for &(s, c) in nf.all_by.get(h) {
            for &(y, l) in &m.elems[x].edges {
                if en.labs.has(l, s)
                    && !pos.get(y as usize, c as usize)
                    && !is_simple_inert_on(y as usize, c, pos, pos_list, en)
                {
                    return false;
                }
            }
        }
        for &gi2 in nf.gci_by_body.get(h) {
            let b_g = &nf.gci[gi2 as usize].0;
            if !b_g
                .iter()
                .any(|&b| b != h && (nf.named[b as usize] || nf.is_nom[b as usize]) && !pos.get(x, b as usize))
            {
                return false;
            }
        }
        true
    };

    let is_giant = k_elems.saturating_mul(n) > 50_000_000;
    let empty_disj_gis: Vec<u32> = nf
        .gci_empty
        .iter()
        .copied()
        .filter(|&gi| nf.gci[gi as usize].1.len() >= 2)
        .collect();
    if is_giant {
    for x in 0..k_elems {
        for &gi in &empty_disj_gis {
            let head = &nf.gci[gi as usize].1;
            if head.iter().any(|&h| pos.get(x, h as usize)) {
                continue;
            }
            if let Some(&h) = head
                .iter()
                .find(|&&h| is_locally_inert_disjunct(x, h, &pos, &pos_list, &m, &en))
            {
                pos.set(x, h as usize, true);
                pos_list[x].push(h);
                for &(s, c) in nf.all_by.get(h) {
                    for &(y, l) in &m.elems[x].edges {
                        if en.labs.has(l, s) && !pos.get(y as usize, c as usize) {
                            pos.set(y as usize, c as usize, true);
                            pos_list[y as usize].push(c);
                        }
                    }
                }
            }
        }
        let pos_x = pos_list[x].clone();
        for a in pos_x {
            for &gi in nf.gci_by_body.get(a) {
                let (body, head) = &nf.gci[gi as usize];
                if head.len() >= 2
                    && body.iter().all(|&b| pos.get(x, b as usize))
                    && !head.iter().any(|&h| pos.get(x, h as usize))
                {
                    if let Some(&h) = head
                        .iter()
                        .find(|&&h| is_locally_inert_disjunct(x, h, &pos, &pos_list, &m, &en))
                    {
                        pos.set(x, h as usize, true);
                        pos_list[x].push(h);
                        for &(s, c) in nf.all_by.get(h) {
                            for &(y, l) in &m.elems[x].edges {
                                if en.labs.has(l, s) && !pos.get(y as usize, c as usize) {
                                    pos.set(y as usize, c as usize, true);
                                    pos_list[y as usize].push(c);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    }

    // Find concepts and elements that can participate in any remaining open disjunctive GCI or unmet existential
    let mut can_affect_pos = vec![!is_giant; n];
    let mut seed_q: Vec<u32> = Vec::new();
    let mut active_elem = vec![!is_giant; k_elems];
    let mut x_open_vec = vec![!is_giant; k_elems];
    let mut elem_q: Vec<usize> = if is_giant { Vec::new() } else { (0..k_elems).collect() };
    if is_giant {
    for &a in &data_rel_concepts {
        if !can_affect_pos[a as usize] {
            can_affect_pos[a as usize] = true;
            seed_q.push(a);
        }
    }
    for x in 0..k_elems {
        let mut x_open = false;
        for &gi in &empty_disj_gis {
            let head = &nf.gci[gi as usize].1;
            if !head.iter().any(|&h| pos.get(x, h as usize)) {
                x_open = true;
                for &h in head {
                    if !can_affect_pos[h as usize] {
                        can_affect_pos[h as usize] = true;
                        seed_q.push(h);
                    }
                }
            }
        }
        for &a in &pos_list[x] {
            if nf.has_le[a as usize] {
                for &(k, r, b) in nf.le_by.get(a) {
                    let pos_cnt = m.elems[x]
                        .edges
                        .iter()
                        .filter(|&&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize))
                        .count();
                    let tot_cnt = m.elems[x]
                        .edges
                        .iter()
                        .filter(|&&(_, l)| en.labs.has(l, r))
                        .count();
                    if pos_cnt >= k as usize && tot_cnt > k as usize {
                        x_open = true;
                        if !can_affect_pos[b as usize] {
                            can_affect_pos[b as usize] = true;
                            seed_q.push(b);
                        }
                    }
                }
            }
            for &gi in nf.gci_by_body.get(a) {
                let (body, head) = &nf.gci[gi as usize];
                if !head.is_empty()
                    && body.iter().all(|&b| pos.get(x, b as usize))
                    && !head.iter().any(|&h| pos.get(x, h as usize))
                {
                    x_open = true;
                    for &h in head {
                        if !can_affect_pos[h as usize] {
                            can_affect_pos[h as usize] = true;
                            seed_q.push(h);
                        }
                    }
                }
            }
            for &(r, b) in nf.ex_by.get(a) {
                let met = m.elems[x]
                    .edges
                    .iter()
                    .any(|&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize));
                if !met {
                    x_open = true;
                    if !can_affect_pos[b as usize] {
                        can_affect_pos[b as usize] = true;
                        seed_q.push(b);
                    }
                }
            }
            for &(k, r, b) in nf.ge_by.get(a) {
                let cnt = m.elems[x]
                    .edges
                    .iter()
                    .filter(|&&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize))
                    .count();
                if cnt < k as usize {
                    x_open = true;
                    if !can_affect_pos[b as usize] {
                        can_affect_pos[b as usize] = true;
                        seed_q.push(b);
                    }
                }
            }
        }
        if x_open {
            x_open_vec[x] = true;
            active_elem[x] = true;
            elem_q.push(x);
        }
    }
    }
    let has_open_work = !elem_q.is_empty();
    let mut ever_pos = vec![!is_giant; n];
    if is_giant {
    for x in 0..k_elems {
        for &a in &pos_list[x] {
            ever_pos[a as usize] = true;
        }
    }
    }
    let mut fwd_idx = 0usize;
    while fwd_idx < seed_q.len() {
        let a = seed_q[fwd_idx];
        fwd_idx += 1;
        for &gi in nf.gci_by_body.get(a) {
            let (body, head) = &nf.gci[gi as usize];
            if body
                .iter()
                .all(|&b| ever_pos[b as usize] || can_affect_pos[b as usize])
            {
                for &h in head {
                    if !can_affect_pos[h as usize] {
                        can_affect_pos[h as usize] = true;
                        seed_q.push(h);
                    }
                }
            }
        }
        for &(_, c) in nf.all_by.get(a) {
            if !can_affect_pos[c as usize] {
                can_affect_pos[c as usize] = true;
                seed_q.push(c);
            }
        }
        for &(_, b) in nf.ex_by.get(a) {
            if !can_affect_pos[b as usize] {
                can_affect_pos[b as usize] = true;
                seed_q.push(b);
            }
        }
        for &(_, _, b) in nf.ge_by.get(a) {
            if !can_affect_pos[b as usize] {
                can_affect_pos[b as usize] = true;
                seed_q.push(b);
            }
        }
    }
    let mut bwd_idx = 0usize;
    while bwd_idx < seed_q.len() {
        let a = seed_q[bwd_idx];
        bwd_idx += 1;
        if !nf.named[a as usize] && !nf.is_nom[a as usize] {
            for &gi in nf.gci_by_body.get(a) {
                let (body, head) = &nf.gci[gi as usize];
                if body
                    .iter()
                    .all(|&b| b == a || ever_pos[b as usize] || can_affect_pos[b as usize])
                {
                    for &h in head {
                        if !can_affect_pos[h as usize] {
                            can_affect_pos[h as usize] = true;
                            seed_q.push(h);
                        }
                    }
                }
            }
            for &(_, b) in nf.ex_by.get(a) {
                if !can_affect_pos[b as usize] {
                    can_affect_pos[b as usize] = true;
                    seed_q.push(b);
                }
            }
            for &(_, _, b) in nf.ge_by.get(a) {
                if !can_affect_pos[b as usize] {
                    can_affect_pos[b as usize] = true;
                    seed_q.push(b);
                }
            }
            for &(_, c) in nf.all_by.get(a) {
                if !can_affect_pos[c as usize] {
                    can_affect_pos[c as usize] = true;
                    seed_q.push(c);
                }
            }
        }
    }

    if has_open_work {
    let mut in_edges: Vec<Vec<(usize, u32)>> = vec![Vec::new(); k_elems];
    for x in 0..k_elems {
        for &(y, l) in &m.elems[x].edges {
            if (y as usize) < k_elems {
                in_edges[y as usize].push((x, l));
            }
        }
    }
    let mut eq_idx = 0usize;
    while eq_idx < elem_q.len() {
        let u = elem_q[eq_idx];
        eq_idx += 1;
        if (!m.elems[u].nom && in_edges[u].len() <= 8) || x_open_vec[u] {
            for &(v, _) in &m.elems[u].edges {
                let vi = v as usize;
                if vi < k_elems && !active_elem[vi] {
                    active_elem[vi] = true;
                    elem_q.push(vi);
                }
            }
            for &(p, _) in &in_edges[u] {
                if !active_elem[p] {
                    active_elem[p] = true;
                    elem_q.push(p);
                }
            }
        }
    }
    elem_q.sort_unstable();
    let active_elems = elem_q;

    let mut neg = BitMatrix::new(k_elems, n);
    let relevant_named_or_nom: Vec<u32> = named_or_nom
        .iter()
        .copied()
        .filter(|&c| can_affect_pos[c as usize])
        .collect();
    // Initialize `neg[x]` for relevant source concepts (`named` or `is_nom`) not in `pos[x]`
    for &x in &active_elems {
        for &c in &relevant_named_or_nom {
            if !pos.get(x, c as usize) {
                neg.set(x, c as usize, true);
            }
        }
    }

    // Precompute reverse index `head_by[h]` (which GCIs have `h` in `head`),
    // `modal_concepts` (concepts with existential/universal/cardinality restrictions),
    // `is_modal_filler` (concepts appearing as the target of a modal clause),
    // and incoming element neighbours `in_elems[y]`
    let mut head_by: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (gi, (body, head)) in nf.gci.iter().enumerate() {
        if !is_giant {
            for &h in head {
                head_by[h as usize].push(gi as u32);
            }
            continue;
        }
        let can_bwd = body.iter().any(|&b| {
            let open_b = b as usize;
            !nf.named[open_b] && !nf.is_nom[open_b] && can_affect_pos[open_b]
        }) && body
            .iter()
            .all(|&b| ever_pos[b as usize] || can_affect_pos[b as usize]);
        let can_fwd_disj = head.len() >= 2
            && head.iter().any(|&h| can_affect_pos[h as usize])
            && body
                .iter()
                .all(|&b| ever_pos[b as usize] || can_affect_pos[b as usize]);
        if can_bwd || can_fwd_disj {
            for &h in head {
                head_by[h as usize].push(gi as u32);
            }
        }
    }
    let mut is_modal_filler = vec![false; n];
    for &(a, _, b) in &nf.ex {
        if (b as usize) < n && can_affect_pos[a as usize] {
            is_modal_filler[b as usize] = true;
        }
    }
    for &(a, _, _, b) in &nf.ge {
        if (b as usize) < n && can_affect_pos[a as usize] {
            is_modal_filler[b as usize] = true;
        }
    }
    for &(a, _, _, b) in &nf.le {
        if (b as usize) < n && can_affect_pos[a as usize] {
            is_modal_filler[b as usize] = true;
        }
    }
    for &(a, _, b) in &nf.all {
        if (b as usize) < n && can_affect_pos[a as usize] {
            is_modal_filler[b as usize] = true;
        }
    }
    let mut gci_neg_init_cands: Vec<u32> = Vec::new();
    for (gi, (body, head)) in nf.gci.iter().enumerate() {
        if body.len() == 1 {
            let b0 = body[0] as usize;
            if b0 < n
                && can_affect_pos[b0]
                && !nf.named[b0]
                && !nf.is_nom[b0]
                && (!head_by[b0].is_empty() || is_modal_filler[b0])
                && head.iter().all(|&h| (h as usize) < n && can_affect_pos[h as usize] && (nf.named[h as usize] || nf.is_nom[h as usize]))
            {
                gci_neg_init_cands.push(gi as u32);
            }
        }
    }
    let modal_concepts: Vec<u32> = (0..n as u32)
        .filter(|&a| {
            !nf.ex_by.get(a).is_empty()
                || !nf.ge_by.get(a).is_empty()
                || nf.has_le[a as usize]
                || !nf.all_by.get(a).is_empty()
        })
        .collect();
    let refutable_modal_concepts: Vec<u32> = modal_concepts
        .iter()
        .copied()
        .filter(|&a| can_affect_pos[a as usize] && (!head_by[a as usize].is_empty() || is_modal_filler[a as usize]))
        .collect();
    let ex_ge_refutable_concepts: Vec<u32> = refutable_modal_concepts
        .iter()
        .copied()
        .filter(|&a| {
            !nf.ex_by.get(a).is_empty() || nf.ge_by.get(a).iter().any(|&(k, _, _)| k > 0)
        })
        .collect();
    let num_dir_roles = nf.m * 2;
    let mut ex_ge_by_first_role: Vec<Vec<u32>> = vec![Vec::new(); num_dir_roles];
    for &a in &ex_ge_refutable_concepts {
        let first_r = nf
            .ex_by
            .get(a)
            .first()
            .map(|&(r, _)| r)
            .or_else(|| {
                nf.ge_by
                    .get(a)
                    .iter()
                    .find(|&&(k, _, _)| k > 0)
                    .map(|&(_, r, _)| r)
            });
        if let Some(r0) = first_r {
            if (r0 as usize) < num_dir_roles {
                ex_ge_by_first_role[r0 as usize].push(a);
            }
        }
    }
    let mut all_le_by_role: Vec<Vec<u32>> = vec![Vec::new(); num_dir_roles];
    for &a in &refutable_modal_concepts {
        for &(s, _) in nf.all_by.get(a) {
            if (s as usize) < num_dir_roles {
                all_le_by_role[s as usize].push(a);
            }
        }
        if nf.has_le[a as usize] {
            for &(_, r, _) in nf.le_by.get(a) {
                if (r as usize) < num_dir_roles {
                    all_le_by_role[r as usize].push(a);
                }
            }
        }
    }
    for v in &mut all_le_by_role {
        v.sort_unstable();
        v.dedup();
    }
    let mut is_refutable_modal = vec![false; n];
    for &a in &refutable_modal_concepts {
        is_refutable_modal[a as usize] = true;
    }
    let mut modal_parents_by_filler: Vec<Vec<(u32, u32)>> = vec![Vec::new(); n];
    for &(a, r, b) in &nf.ex {
        if (b as usize) < n {
            modal_parents_by_filler[b as usize].push((r, a));
        }
    }
    for &(a, _, r, b) in &nf.ge {
        if (b as usize) < n {
            modal_parents_by_filler[b as usize].push((r, a));
        }
    }
    for &(a, _, r, b) in &nf.le {
        if (b as usize) < n {
            modal_parents_by_filler[b as usize].push((r, a));
        }
    }
    for &(a, s, b) in &nf.all {
        if (b as usize) < n {
            modal_parents_by_filler[b as usize].push((s, a));
        }
    }
    for v in &mut modal_parents_by_filler {
        v.sort_unstable();
        v.dedup();
    }

    let mut is_modal_concept = vec![false; n];
    for &a in &modal_concepts {
        is_modal_concept[a as usize] = true;
    }

    let check_gci_unit = |gi: u32,
                          x: usize,
                          pos: &mut BitMatrix,
                          pos_list: &mut [Vec<u32>],
                          neg: &mut BitMatrix,
                          q_lit: &mut Vec<(usize, u32, bool)>| {
        let (body, head) = &nf.gci[gi as usize];
        if body.len() == 2 && !pos.get(x, body[0] as usize) && !pos.get(x, body[1] as usize) {
            return;
        }
        let body_true = body.iter().all(|&b| pos.get(x, b as usize));
        if body_true {
            if head.iter().any(|&h| pos.get(x, h as usize)) {
                return;
            }
            let mut open_h = NONE;
            let mut cnt_h = 0usize;
            for &h in head {
                if !neg.get(x, h as usize) {
                    open_h = h;
                    cnt_h += 1;
                    if cnt_h > 1 {
                        break;
                    }
                }
            }
            if cnt_h == 1 && !pos.get(x, open_h as usize) {
                pos.set(x, open_h as usize, true);
                pos_list[x].push(open_h);
                q_lit.push((x, open_h, true));
            }
        } else if head.iter().all(|&h| neg.get(x, h as usize)) {
            if body.iter().any(|&b| neg.get(x, b as usize)) {
                return;
            }
            let mut open_b = NONE;
            let mut cnt_b = 0usize;
            for &b in body {
                if !pos.get(x, b as usize) {
                    open_b = b;
                    cnt_b += 1;
                    if cnt_b > 1 {
                        break;
                    }
                }
            }
            if cnt_b == 1 && !neg.get(x, open_b as usize) {
                neg.set(x, open_b as usize, true);
                q_lit.push((x, open_b, false));
            }
        }
    };

    let check_one_modal_refuted = |x: usize,
                                   a: u32,
                                   pos: &BitMatrix,
                                   neg: &BitMatrix,
                                   m: &Model,
                                   en: &Engine|
     -> bool {
        for &(r, b) in nf.ex_by.get(a) {
            let has_poss = m.elems[x]
                .edges
                .iter()
                .any(|&(y, l)| en.labs.has(l, r) && !neg.get(y as usize, b as usize));
            if !has_poss {
                return true;
            }
        }
        for &(k, r, b) in nf.ge_by.get(a) {
            let poss_cnt = m.elems[x]
                .edges
                .iter()
                .filter(|&&(y, l)| en.labs.has(l, r) && !neg.get(y as usize, b as usize))
                .count();
            if poss_cnt < k as usize {
                return true;
            }
        }
        if nf.has_le[a as usize] {
            for &(k, r, b) in nf.le_by.get(a) {
                let forced_cnt = m.elems[x]
                    .edges
                    .iter()
                    .filter(|&&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize))
                    .count();
                if forced_cnt > k as usize {
                    return true;
                }
            }
        }
        for &(s, c) in nf.all_by.get(a) {
            let bad_all = m.elems[x]
                .edges
                .iter()
                .any(|&(y, l)| en.labs.has(l, s) && neg.get(y as usize, c as usize));
            if bad_all {
                return true;
            }
        }
        false
    };

    let propagate_one_pos_modal = |x: usize,
                                   a: u32,
                                   pos: &mut BitMatrix,
                                   pos_list: &mut [Vec<u32>],
                                   neg: &mut BitMatrix,
                                   q_lit: &mut Vec<(usize, u32, bool)>,
                                   m: &Model,
                                   en: &Engine| {
        for &(s, c) in nf.all_by.get(a) {
            for &(y, l) in &m.elems[x].edges {
                if en.labs.has(l, s) && !pos.get(y as usize, c as usize) && !neg.get(y as usize, c as usize) {
                    pos.set(y as usize, c as usize, true);
                    pos_list[y as usize].push(c);
                    q_lit.push((y as usize, c, true));
                }
            }
        }
        for &(r, b) in nf.ex_by.get(a) {
            let already = m.elems[x]
                .edges
                .iter()
                .any(|&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize));
            if !already {
                let mut only_y: Option<usize> = None;
                let mut cnt = 0usize;
                for &(y, l) in &m.elems[x].edges {
                    if en.labs.has(l, r) && !neg.get(y as usize, b as usize) {
                        only_y = Some(y as usize);
                        cnt += 1;
                        if cnt > 1 {
                            break;
                        }
                    }
                }
                if cnt == 1 {
                    let y0 = only_y.unwrap();
                    if !pos.get(y0, b as usize) {
                        pos.set(y0, b as usize, true);
                        pos_list[y0].push(b);
                        q_lit.push((y0, b, true));
                    }
                }
            }
        }
        for &(k, r, b) in nf.ge_by.get(a) {
            let cands: Vec<Id> = m.elems[x]
                .edges
                .iter()
                .filter(|&&(y, l)| en.labs.has(l, r) && !neg.get(y as usize, b as usize))
                .map(|e| e.0)
                .collect();
            if cands.len() == k as usize {
                for y0 in cands {
                    if !pos.get(y0 as usize, b as usize) {
                        pos.set(y0 as usize, b as usize, true);
                        pos_list[y0 as usize].push(b);
                        q_lit.push((y0 as usize, b, true));
                    }
                }
            }
        }
        if nf.has_le[a as usize] {
            for &(k, r, b) in nf.le_by.get(a) {
                let pos_cnt = m.elems[x]
                    .edges
                    .iter()
                    .filter(|&&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize))
                    .count();
                if pos_cnt == k as usize {
                    for &(y, l) in &m.elems[x].edges {
                        if en.labs.has(l, r) && !pos.get(y as usize, b as usize) && !neg.get(y as usize, b as usize) {
                            neg.set(y as usize, b as usize, true);
                            q_lit.push((y as usize, b, false));
                        }
                    }
                }
            }
        }
    };

    let mut is_pure_oneof_dall_vec = vec![false; n];
    if let Some((d, _)) = en.data.as_ref() {
        for &a in &data_rel_concepts {
            if en.dreq.get(a as usize).copied().unwrap_or(0) == 0
                && !d.datmost_by.contains_key(&a)
                && d.dall_by.get(&a).map_or(false, |ixs| {
                    ixs.len() == 1 && {
                        let lits = &d.dall[ixs[0]].2;
                        lits.len() == 1
                            && matches!(lits[0], crate::data::Lit::Neg(j) if d.is_oneof_atom.get(&j).copied().unwrap_or(false))
                    }
                })
            {
                is_pure_oneof_dall_vec[a as usize] = true;
            }
        }
    }

    // Incremental forward (`pos`) + backward (`neg`) fixpoint starting from dirty elements / literals
    let propagate_incremental = |dirty_seed: &[usize],
                                 seed_lits: &[(usize, u32, bool)],
                                 full_gci_scan: bool,
                                 pos: &mut BitMatrix,
                                 pos_list: &mut [Vec<u32>],
                                 neg: &mut BitMatrix,
                                 m: &Model,
                                 en: &Engine| {
        let mut q_lit: Vec<(usize, u32, bool)> = seed_lits.to_vec();
        let mut sat_ex_ge_mark = vec![false; n];
        for &x in dirty_seed {
            if m.elems[x].edges.is_empty() {
                for &a in &ex_ge_refutable_concepts {
                    if !pos.get(x, a as usize) && !neg.get(x, a as usize) {
                        neg.set(x, a as usize, true);
                        if !head_by[a as usize].is_empty() || is_modal_filler[a as usize] {
                            q_lit.push((x, a, false));
                        }
                    }
                }
            } else {
                let mut active_roles: Vec<u32> = Vec::new();
                for &(_, l) in &m.elems[x].edges {
                    for &r in en.labs.get(l).iter() {
                        if (r as usize) < num_dir_roles && !active_roles.contains(&r) {
                            active_roles.push(r);
                        }
                    }
                }
                let mut sat_list: Vec<u32> = Vec::new();
                for &r_act in &active_roles {
                    for &a in &ex_ge_by_first_role[r_act as usize] {
                        if pos.get(x, a as usize) || neg.get(x, a as usize) {
                            continue;
                        }
                        if !check_one_modal_refuted(x, a, pos, neg, m, en) {
                            sat_ex_ge_mark[a as usize] = true;
                            sat_list.push(a);
                        }
                    }
                }
                for &a in &ex_ge_refutable_concepts {
                    if !pos.get(x, a as usize) && !neg.get(x, a as usize) && !sat_ex_ge_mark[a as usize] {
                        neg.set(x, a as usize, true);
                        if !head_by[a as usize].is_empty() || is_modal_filler[a as usize] {
                            q_lit.push((x, a, false));
                        }
                    }
                }
                for a in sat_list {
                    sat_ex_ge_mark[a as usize] = false;
                }
                for r_act in active_roles {
                    for &a in &all_le_by_role[r_act as usize] {
                        if !pos.get(x, a as usize)
                            && !neg.get(x, a as usize)
                            && check_one_modal_refuted(x, a, pos, neg, m, en)
                        {
                            neg.set(x, a as usize, true);
                            if !head_by[a as usize].is_empty() || is_modal_filler[a as usize] {
                                q_lit.push((x, a, false));
                            }
                        }
                    }
                }
                let pos_x = pos_list[x].clone();
                for a in pos_x {
                    if is_modal_concept[a as usize] {
                        propagate_one_pos_modal(x, a, pos, pos_list, neg, &mut q_lit, m, en);
                    }
                }
            }
            if full_gci_scan {
                if !is_giant {
                    for gi in 0..nf.gci.len() as u32 {
                        check_gci_unit(gi, x, pos, pos_list, neg, &mut q_lit);
                    }
                } else {
                    for &gi in &nf.gci_empty {
                        check_gci_unit(gi, x, pos, pos_list, neg, &mut q_lit);
                    }
                    for &gi in &gci_neg_init_cands {
                        check_gci_unit(gi, x, pos, pos_list, neg, &mut q_lit);
                    }
                    let pos_x = pos_list[x].clone();
                    for a in pos_x {
                        for &gi in nf.gci_by_body.get(a) {
                            check_gci_unit(gi, x, pos, pos_list, neg, &mut q_lit);
                        }
                    }
                }
            }
        }
        let mut steps = 0usize;
        for _wave in 0..2 {
            while let Some((x, a, is_pos)) = q_lit.pop() {
                steps += 1;
                if steps & 4095 == 0 && Instant::now() > deadline {
                    return;
                }
                if is_pos {
                    if !data_rel_concepts.is_empty() && data_rel_concepts.binary_search(&a).is_ok() {
                        for &peer in &data_rel_concepts {
                            if peer != a
                                && !neg.get(x, peer as usize)
                                && !pos.get(x, peer as usize)
                                && en.has_conflict_peer(a, peer)
                            {
                                neg.set(x, peer as usize, true);
                                q_lit.push((x, peer, false));
                            }
                        }
                    }
                    for &gi in nf.gci_by_body.get(a) {
                        check_gci_unit(gi, x, pos, pos_list, neg, &mut q_lit);
                    }
                    if is_modal_concept[a as usize] && !m.elems[x].edges.is_empty() {
                        propagate_one_pos_modal(x, a, pos, pos_list, neg, &mut q_lit, m, en);
                    }
                } else {
                    for &gi in &head_by[a as usize] {
                        check_gci_unit(gi, x, pos, pos_list, neg, &mut q_lit);
                    }
                }
                if !in_edges[x].is_empty() && !modal_parents_by_filler[a as usize].is_empty() {
                    for &(r, parent_a) in &modal_parents_by_filler[a as usize] {
                        for &(pred, l) in &in_edges[x] {
                            if !active_elem[pred] || !en.labs.has(l, r) {
                                continue;
                            }
                            if is_refutable_modal[parent_a as usize]
                                && !pos.get(pred, parent_a as usize)
                                && !neg.get(pred, parent_a as usize)
                                && check_one_modal_refuted(pred, parent_a, pos, neg, m, en)
                            {
                                neg.set(pred, parent_a as usize, true);
                                q_lit.push((pred, parent_a, false));
                            } else if pos.get(pred, parent_a as usize) {
                                propagate_one_pos_modal(
                                    pred,
                                    parent_a,
                                    pos,
                                    pos_list,
                                    neg,
                                    &mut q_lit,
                                    m,
                                    en,
                                );
                            }
                        }
                    }
                }
            }
            if !full_gci_scan {
                break;
            }
            for &x in dirty_seed {
                let pos_x = pos_list[x].clone();
                for a in pos_x {
                    for &gi in nf.gci_by_body.get(a) {
                        check_gci_unit(gi, x, pos, pos_list, neg, &mut q_lit);
                    }
                }
            }
            if q_lit.is_empty() {
                break;
            }
        }
    };

    propagate_incremental(&active_elems, &[], true, &mut pos, &mut pos_list, &mut neg, &m, &en);

    // Step 3: Close any remaining open disjunctive GCIs or existentials on each element
    // avoiding `neg[x]` (and preferring 0-requirement fresh concepts such as `dall`)
    let test_candidate_on_elem = |x: usize,
                                  cand_lit: u32,
                                  pos: &mut BitMatrix,
                                  neg: &mut BitMatrix,
                                  en: &mut Engine|
     -> bool {
        if neg.get(x, cand_lit as usize) {
            return false;
        }
        let mut undo_p: Vec<u32> = Vec::new();
        let mut undo_n: Vec<u32> = Vec::new();
        if !pos.get(x, cand_lit as usize) {
            pos.set(x, cand_lit as usize, true);
            undo_p.push(cand_lit);
        }
        let mut q: Vec<(u32, bool)> = vec![(cand_lit, true)];
        let mut ok = true;
        'bfs: while let Some((a, is_p)) = q.pop() {
            if is_p {
                if !data_rel_concepts.is_empty() && data_rel_concepts.binary_search(&a).is_ok() {
                    for &peer in &data_rel_concepts {
                        if peer != a && en.has_conflict_peer(a, peer) {
                            if pos.get(x, peer as usize) {
                                ok = false;
                                break 'bfs;
                            }
                            if !neg.get(x, peer as usize) {
                                neg.set(x, peer as usize, true);
                                undo_n.push(peer);
                                q.push((peer, false));
                            }
                        }
                    }
                }
                for &g in nf.gci_by_body.get(a) {
                    let (b_g, h_g) = &nf.gci[g as usize];
                    if b_g.iter().all(|&b| pos.get(x, b as usize)) {
                        if h_g.iter().any(|&h| pos.get(x, h as usize)) {
                            continue;
                        }
                        let mut open_h = NONE;
                        let mut cnt = 0usize;
                        for &h in h_g {
                            if !neg.get(x, h as usize) {
                                open_h = h;
                                cnt += 1;
                                if cnt > 1 {
                                    break;
                                }
                            }
                        }
                        if cnt == 0 {
                            ok = false;
                            break 'bfs;
                        }
                        if cnt == 1 && !pos.get(x, open_h as usize) {
                            pos.set(x, open_h as usize, true);
                            undo_p.push(open_h);
                            q.push((open_h, true));
                        }
                    }
                }
            } else {
                for &g in &head_by[a as usize] {
                    let (b_g, h_g) = &nf.gci[g as usize];
                    if b_g.iter().all(|&b| pos.get(x, b as usize)) {
                        if h_g.iter().any(|&h| pos.get(x, h as usize)) {
                            continue;
                        }
                        let mut open_h = NONE;
                        let mut cnt = 0usize;
                        for &h in h_g {
                            if !neg.get(x, h as usize) {
                                open_h = h;
                                cnt += 1;
                                if cnt > 1 {
                                    break;
                                }
                            }
                        }
                        if cnt == 0 {
                            ok = false;
                            break 'bfs;
                        }
                        if cnt == 1 && !pos.get(x, open_h as usize) {
                            pos.set(x, open_h as usize, true);
                            undo_p.push(open_h);
                            q.push((open_h, true));
                        }
                    } else if h_g.iter().all(|&h| neg.get(x, h as usize)) {
                        if b_g.iter().any(|&b| neg.get(x, b as usize)) {
                            continue;
                        }
                        let mut open_b = NONE;
                        let mut cnt = 0usize;
                        for &b in b_g {
                            if !pos.get(x, b as usize) {
                                open_b = b;
                                cnt += 1;
                                if cnt > 1 {
                                    break;
                                }
                            }
                        }
                        if cnt == 0 {
                            ok = false;
                            break 'bfs;
                        }
                        if cnt == 1 && !neg.get(x, open_b as usize) {
                            neg.set(x, open_b as usize, true);
                            undo_n.push(open_b);
                            q.push((open_b, false));
                        }
                    }
                }
            }
        }
        if ok && !data_rel_concepts.is_empty() {
            let active_d: Vec<u32> = data_rel_concepts
                .iter()
                .copied()
                .filter(|&a| pos.get(x, a as usize))
                .collect();
            'dchk: for i in 0..active_d.len() {
                for j in (i + 1)..active_d.len() {
                    if en.has_conflict_peer(active_d[i], active_d[j]) {
                        ok = false;
                        break 'dchk;
                    }
                }
            }
            if ok {
                let star_d: Vec<u32> = active_d
                    .into_iter()
                    .filter(|&a| !is_pure_oneof_dall_vec[a as usize])
                    .collect();
                if !star_d.is_empty() && !en.has_data_star(star_d) {
                    ok = false;
                }
            }
        }
        for a in undo_p {
            pos.set(x, a as usize, false);
        }
        for a in undo_n {
            neg.set(x, a as usize, false);
        }
        ok
    };
    for &x in &active_elems {
        if Instant::now() > deadline || en.mem_exceeded() {
            let why = if en.mem_hit { "memory cap (8 GB) exceeded" } else { "from-export time budget exceeded" };
            return format!(
                "{{\"ok\":false,\"status\":\"timeout\",\"route\":{},\"why\":{},\"reason\":{}}}",
                json_str(&route),
                json_str(why),
                json_str(why)
            );
        }
        if !data_rel_concepts.is_empty() {
            let mut cur_d: Vec<u32> = data_rel_concepts
                .iter()
                .copied()
                .filter(|&a| pos.get(x, a as usize))
                .collect();
            let filt_cur: Vec<u32> = cur_d
                .iter()
                .copied()
                .filter(|&a| !is_pure_oneof_dall_vec[a as usize])
                .collect();
            let filt_cur = en.filter_active_data(&filt_cur);
            if !filt_cur.is_empty() && !en.has_data_star(filt_cur) {
                cur_d.sort_by_key(|&a| (!nf.named[a as usize], a));
                let mut kept: Vec<u32> = Vec::new();
                for a in cur_d {
                    let mut try_k = kept.clone();
                    try_k.push(a);
                    try_k.sort_unstable();
                    let filt_try: Vec<u32> = try_k
                        .iter()
                        .copied()
                        .filter(|&b| !is_pure_oneof_dall_vec[b as usize])
                        .collect();
                    let filt_try = en.filter_active_data(&filt_try);
                    if !kept.iter().any(|&b| en.has_conflict_peer(a, b))
                        && (filt_try.is_empty() || en.has_data_star(filt_try))
                    {
                        kept = try_k;
                    } else {
                        pos.set(x, a as usize, false);
                        pos_list[x].retain(|&p| p != a);
                        neg.set(x, a as usize, true);
                    }
                }
            }
        }
        for _pass in 0..3 {
            let mut any_change = false;
            let mut cand_gis: Vec<usize> = nf.gci_empty.iter().map(|&g| g as usize).collect();
            for &a in &pos_list[x] {
                for &gi in nf.gci_by_body.get(a) {
                    cand_gis.push(gi as usize);
                }
            }
            cand_gis.sort_unstable();
            cand_gis.dedup();
            for gi in cand_gis {
                let (body, head) = &nf.gci[gi];
                if !body.iter().all(|&b| pos.get(x, b as usize)) || head.iter().any(|&h| pos.get(x, h as usize)) {
                    continue;
                }
                let mut open_heads: Vec<((bool, usize, u32), u32)> = head
                    .iter()
                    .copied()
                    .filter(|&h| !neg.get(x, h as usize))
                    .map(|h| {
                        let is_src = nf.named[h as usize] || nf.is_nom[h as usize];
                        let reqs = nf.ex_by.get(h).len()
                            + nf.ge_by.get(h).len()
                            + en.dreq.get(h as usize).copied().unwrap_or(0) as usize;
                        ((is_src, reqs, h), h)
                    })
                    .collect();
                open_heads.sort_unstable_by_key(|k| k.0);
                let mut best_h: Option<((bool, usize, u32), u32)> = None;
                let mut newly_neg: Vec<(usize, u32, bool)> = Vec::new();
                for (key, h) in open_heads {
                    if !test_candidate_on_elem(x, h, &mut pos, &mut neg, &mut en) {
                        neg.set(x, h as usize, true);
                        newly_neg.push((x, h, false));
                        continue;
                    }
                    if best_h.is_none() {
                        best_h = Some((key, h));
                        if is_giant {
                            break;
                        }
                    }
                }
                if !newly_neg.is_empty() {
                    propagate_incremental(&[], &newly_neg, false, &mut pos, &mut pos_list, &mut neg, &m, &en);
                    any_change = true;
                }
                if head.iter().any(|&h| pos.get(x, h as usize)) {
                    continue;
                }
                if let Some((_, h)) = best_h {
                    if !neg.get(x, h as usize) {
                        if !pos.get(x, h as usize) {
                            pos.set(x, h as usize, true);
                            pos_list[x].push(h);
                        }
                        any_change = true;
                        let is_inert = nf.gci_by_body.get(h).is_empty()
                            && !is_modal_concept[h as usize]
                            && !is_modal_filler[h as usize];
                        if !is_inert {
                            propagate_incremental(&[], &[(x, h, true)], false, &mut pos, &mut pos_list, &mut neg, &m, &en);
                        }
                    }
                }
            }
            if !any_change {
                break;
            }
        }
        // If an active existential `some a r b` on `x` is still unmet among `r`-neighbours,
        // pick a compatible `r`-neighbour `y` with `!neg.get(y, b)`
        let pos_x = pos_list[x].clone();
        for a in pos_x {
            if !is_modal_concept[a as usize] {
                continue;
            }
            for &(r, b) in nf.ex_by.get(a) {
                let met = m.elems[x]
                    .edges
                    .iter()
                    .any(|&(y, l)| en.labs.has(l, r) && pos.get(y as usize, b as usize));
                if !met {
                    let chosen_y = m.elems[x]
                        .edges
                        .iter()
                        .find(|&&(y, l)| {
                            en.labs.has(l, r)
                                && !neg.get(y as usize, b as usize)
                                && test_candidate_on_elem(y as usize, b, &mut pos, &mut neg, &mut en)
                        })
                        .or_else(|| {
                            m.elems[x]
                                .edges
                                .iter()
                                .find(|&&(y, l)| en.labs.has(l, r) && !neg.get(y as usize, b as usize))
                        });
                    if let Some(&(y, _)) = chosen_y {
                        if !pos.get(y as usize, b as usize) {
                            pos.set(y as usize, b as usize, true);
                            pos_list[y as usize].push(b);
                        }
                        propagate_incremental(&[], &[(y as usize, b, true)], false, &mut pos, &mut pos_list, &mut neg, &m, &en);
                    }
                }
            }
        }
    }
    }

    // Store closed types into `m`
    for x in 0..k_elems {
        let mut p_vec = std::mem::take(&mut pos_list[x]);
        p_vec.sort_unstable();
        p_vec.dedup();
        let tid = en.sets.intern(p_vec);
        let e = m.em(x as Id);
        e.ty = tid;
        e.forced = tid;
        e.forbid = 0;
        e.target = 0;
        m.tm_push(tid, x as Id);
    }

    // Self-check, with optional bounded saturation repair if an exported node needed an unexpanded filler
    let mut rep = check::verify(&mut en, &m);
    if rep.violations > 0 && Instant::now() < deadline && !en.mem_exceeded() {
        for x in 0..k_elems {
            let f_vec: Vec<u32> = named_or_nom
                .iter()
                .copied()
                .filter(|&a| !pos.get(x, a as usize))
                .collect();
            let tgt_vec: Vec<u32> = named_or_nom
                .iter()
                .copied()
                .filter(|&a| pos.get(x, a as usize))
                .collect();
            let fid = en.sets.intern(f_vec);
            let tgt_id = en.sets.intern(tgt_vec);
            let e = m.em(x as Id);
            e.forbid = fid;
            e.target = tgt_id;
        }
        let rep_deadline = deadline.min(Instant::now() + std::time::Duration::from_secs(12));
        en.opt.deadline = Some(rep_deadline);
        for _round in 0..4 {
            if rep.violations == 0 || Instant::now() > rep_deadline || en.mem_exceeded() {
                break;
            }
            for &bad_x in &rep.bad {
                if Instant::now() > rep_deadline || en.mem_exceeded() {
                    break;
                }
                let bad_x = m.find(bad_x);
                let nbs: Vec<Id> = m.elems[bad_x as usize].edges.iter().map(|e| m.find(e.0)).collect();
                for y in nbs {
                    m.em(y).forbid = 0;
                }
                let e = &m.elems[bad_x as usize];
                let (ty0, fb0, tgt0, nom0) = (e.ty, e.forbid, e.target, e.nom);
                if let CloseRes::Ok(t_new) = en.close(ty0, fb0, tgt0, nom0) {
                    m.em(bad_x).ty = t_new;
                } else if let CloseRes::Ok(t_new) = en.close(ty0, 0, tgt0, nom0) {
                    let em = m.em(bad_x);
                    em.ty = t_new;
                    em.forbid = 0;
                } else if let CloseRes::Ok(t_new) = en.close(tgt0, fb0, tgt0, nom0) {
                    let em = m.em(bad_x);
                    em.ty = t_new;
                    em.forced = tgt0;
                } else if let CloseRes::Ok(t_new) = en.close(tgt0, 0, tgt0, nom0) {
                    let em = m.em(bad_x);
                    em.ty = t_new;
                    em.forced = tgt0;
                    em.forbid = 0;
                } else {
                    // Greedily keep a maximal subset of `tgt0` (preserving nominals) that closes
                    let orig = en.sets.get(tgt0);
                    let mut kept: Vec<u32> = orig.iter().copied().filter(|&a| nf.is_nom[a as usize]).collect();
                    for &a in orig.iter() {
                        if nf.is_nom[a as usize] {
                            continue;
                        }
                        let mut try_v = kept.clone();
                        try_v.push(a);
                        try_v.sort_unstable();
                        let try_id = en.sets.intern(try_v.clone());
                        if matches!(en.close(try_id, 0, try_id, nom0), CloseRes::Ok(_)) {
                            kept = try_v;
                        }
                    }
                    let kid = en.sets.intern(kept);
                    if let CloseRes::Ok(t_new) = en.close(kid, 0, kid, nom0) {
                        let em = m.em(bad_x);
                        em.ty = t_new;
                        em.forced = kid;
                        em.target = kid;
                        em.forbid = 0;
                    }
                }
                m.enqueue(bad_x);
            }
            // Process queued elements one by one so a single failing element does not abort the repair queue
            let mut proc_steps = 0usize;
            while let Some(x) = m.pop() {
                proc_steps += 1;
                if proc_steps > 25_000 || Instant::now() > rep_deadline || en.mem_exceeded() {
                    break;
                }
                if en.process(&mut m, x).is_err() {
                    let x = m.find(x);
                    if m.elems[x as usize].alive {
                        m.em(x).forbid = 0;
                        let nbs: Vec<Id> = m.elems[x as usize].edges.iter().map(|e| m.find(e.0)).collect();
                        for y in nbs {
                            if m.elems[y as usize].alive {
                                m.em(y).forbid = 0;
                            }
                        }
                        let _ = en.process(&mut m, x);
                    }
                }
            }
            let canon_now: Vec<Id> = m.canonical().collect();
            for &x in &canon_now {
                let tx = en.sets.get(m.elems[x as usize].ty);
                let edges = m.elems[x as usize].edges.clone();
                for &a in tx.iter() {
                    for &(s, c) in nf.all_by.get(a) {
                        for &(y, l) in &edges {
                            let y = m.find(y);
                            if en.labs.has(l, s) && !en.sets.has(m.elems[y as usize].ty, c) {
                                m.em(y).pending.push(c);
                            }
                        }
                    }
                }
            }
            for &x in &canon_now {
                if !m.elems[x as usize].pending.is_empty() {
                    let mut pend = std::mem::take(&mut m.em(x).pending);
                    pend.sort_unstable();
                    pend.dedup();
                    let e = &m.elems[x as usize];
                    let (ty0, tgt0, nom0) = (e.ty, e.target, e.nom);
                    let merged = en.sets.union_vec(ty0, &pend);
                    let new_tgt = en.sets.union_vec(tgt0, &pend);
                    if let CloseRes::Ok(t_new) = en.close(merged, 0, new_tgt, nom0) {
                        let em = m.em(x);
                        em.ty = t_new;
                        em.target = new_tgt;
                        em.forced = new_tgt;
                        m.enqueue(x);
                    } else {
                        let orig = en.sets.get(tgt0);
                        let mut kept: Vec<u32> = orig.iter().copied().filter(|&a| nf.is_nom[a as usize]).collect();
                        for &a in pend.iter().chain(orig.iter()) {
                            if kept.binary_search(&a).is_ok() {
                                continue;
                            }
                            let mut try_v = kept.clone();
                            try_v.push(a);
                            try_v.sort_unstable();
                            let try_id = en.sets.intern(try_v.clone());
                            if matches!(en.close(try_id, 0, try_id, nom0), CloseRes::Ok(_)) {
                                kept = try_v;
                            }
                        }
                        let kid = en.sets.intern(kept);
                        if let CloseRes::Ok(t_new) = en.close(kid, 0, kid, nom0) {
                            let em = m.em(x);
                            em.ty = t_new;
                            em.forced = kid;
                            em.target = kid;
                            em.forbid = 0;
                            m.enqueue(x);
                        }
                    }
                }
            }
            for &x in &canon_now {
                let tx = en.sets.get(m.elems[x as usize].ty);
                let edges = m.elems[x as usize].edges.clone();
                let mut drop_y: Vec<Id> = Vec::new();
                for &(y, l) in &edges {
                    let y = m.find(y);
                    let violated = tx.iter().any(|&a| {
                        nf.all_by
                            .get(a)
                            .iter()
                            .any(|&(s, c)| en.labs.has(l, s) && !en.sets.has(m.elems[y as usize].ty, c))
                    });
                    if violated {
                        drop_y.push(y);
                    }
                }
                if !drop_y.is_empty() {
                    for y in drop_y {
                        en.remove_edge(&mut m, x, y);
                    }
                    m.enqueue(x);
                }
            }
            rep = check::verify(&mut en, &m);
        }
        while m.pop().is_some() {}
    }

    // Build witness table (`wits`)
    let mut wits: Vec<(Option<u32>, Id)> = Vec::new();
    let mut wit_covered: BTreeSet<Option<u32>> = BTreeSet::new();
    let mut wit_pairs: BTreeSet<(Option<u32>, Id)> = BTreeSet::new();
    let canon_0 = m.canonical().next().unwrap_or(0);
    wits.push((None, canon_0));
    wit_covered.insert(None);
    wit_pairs.insert((None, canon_0));

    for (cls_iri, el_id, _) in &exp_witnesses {
        if cls_iri == THING {
            if let Some(&idx) = id_to_idx.get(el_id) {
                let w = m.find(idx as Id);
                if wit_pairs.insert((None, w)) {
                    wits.push((None, w));
                }
            }
            continue;
        }
        if let (Some(&c), Some(&idx)) = (nf.cidx.get(cls_iri.as_str()), id_to_idx.get(el_id)) {
            if rowclass[c as usize] {
                let w = m.find(idx as Id);
                if en.sets.has(m.elems[w as usize].ty, c) && wit_pairs.insert((Some(c), w)) {
                    wit_covered.insert(Some(c));
                    wits.push((Some(c), w));
                }
            }
        }
    }
    let mut first_witness: Vec<Id> = vec![NONE; n];
    let canon_all: Vec<Id> = m.canonical().collect();
    for &x in &canon_all {
        for &a in en.sets.get(m.elems[x as usize].ty).iter() {
            if first_witness[a as usize] == NONE {
                first_witness[a as usize] = x;
            }
        }
    }
    for &c in &classes {
        if wit_covered.contains(&Some(c)) {
            continue;
        }
        if let Some(km_ref) = km {
            if km_ref.unsat.contains(nf.cname_of(c)) {
                continue;
            }
        }
        let w = first_witness[c as usize];
        if w != NONE && wit_pairs.insert((Some(c), w)) {
            wit_covered.insert(Some(c));
            wits.push((Some(c), w));
        }
    }

    // If `km` is provided, check if any exported witness for `c` has dirty rowclasses
    // that another existing element in `m` already separates, or (when not `--export-only`)
    // search only for what the export lacks.
    let mut searched_wits = 0usize;
    let mut export_only_full = false;
    let mut plus_search_full = false;
    if let Some(km_ref) = km {
        let ci = |iri: &str| nf.cidx.get(iri).copied().filter(|&c| nf.named[c as usize]);
        let mut top: Vec<u32> = km_ref.top.iter().filter_map(|s| ci(s)).collect();
        if let Some(t) = thing_c {
            top.push(t);
        }
        top.sort_unstable();
        top.dedup();
        let mut sup_of: HashMap<u32, Vec<u32>> = HashMap::new();
        for &c in &classes {
            let mut v: Vec<u32> = km_ref
                .sup
                .get(nf.cname_of(c))
                .map(|s| s.iter().filter_map(|x| ci(x)).collect())
                .unwrap_or_default();
            v.push(c);
            v.extend_from_slice(&top);
            v.sort_unstable();
            v.dedup();
            sup_of.insert(c, v);
        }
        let mut elems_by_class: Vec<Vec<Id>> = vec![Vec::new(); n];
        for &x in &canon_all {
            for &a in en.sets.get(m.elems[x as usize].ty).iter() {
                if (a as usize) < n && rowclass[a as usize] {
                    elems_by_class[a as usize].push(x);
                }
            }
        }
        // Pass 1: use existing elements in `m` to separate any dirty rowclasses
        let mut dirty_of: HashMap<u32, Vec<u32>> = HashMap::new();
        let mut missing_exp = 0usize;
        for &c in &classes {
            if km_ref.unsat.contains(nf.cname_of(c)) {
                continue;
            }
            if !wit_covered.contains(&Some(c)) {
                missing_exp += 1;
                continue;
            }
            let sup = &sup_of[&c];
            let mut left: Option<Vec<u32>> = None;
            for &(wc, w) in &wits {
                if wc == Some(c) {
                    let ts = en.sets.get(m.elems[m.find(w) as usize].ty);
                    let d: Vec<u32> = ts
                        .iter()
                        .copied()
                        .filter(|&b| rowclass[b as usize] && sup.binary_search(&b).is_err())
                        .collect();
                    left = Some(match left {
                        None => d,
                        Some(l) => l.into_iter().filter(|b| d.binary_search(b).is_ok()).collect(),
                    });
                }
            }
            if let Some(mut d) = left {
                if !d.is_empty() {
                    for &x in &elems_by_class[c as usize] {
                        if d.is_empty() {
                            break;
                        }
                        let ty = m.elems[x as usize].ty;
                        if d.iter().any(|&b| !en.sets.has(ty, b)) {
                            if wit_pairs.insert((Some(c), x)) {
                                wits.push((Some(c), x));
                            }
                            d.retain(|&b| en.sets.has(ty, b));
                        }
                    }
                    if !d.is_empty() {
                        dirty_of.insert(c, d);
                    }
                }
            }
        }
        export_only_full = rep.violations == 0 && missing_exp == 0 && dirty_of.is_empty();
        // Pass 2: if not `--export-only` and `rep.violations == 0`, search for missing/dirty witnesses
        let export_only = std::env::args().any(|a| a == "--export-only");
        if !export_only && rep.violations == 0 && !export_only_full {
            en.opt.deadline = Some(deadline);
            m.tm_clear();
            let try_add_clean_wit = |en: &mut Engine, m: &mut Model, c: u32, fb: u32, tgt: u32| -> Option<Id> {
                let seed = en.sets.intern(vec![c]);
                let base_bad = en.bad.clone();
                let mut res = None;
                for attempt in 0..4 {
                    let (t, is_clean) = if attempt == 0 {
                        match en.close_clean(seed, fb, tgt, true) {
                            CloseRes::Ok(t) => (t, true),
                            _ => match en.close(seed, fb, tgt, true) {
                                CloseRes::Ok(t) => (t, false),
                                _ => break,
                            },
                        }
                    } else {
                        match en.close(seed, fb, tgt, true) {
                            CloseRes::Ok(t) => (t, false),
                            _ => break,
                        }
                    };
                    if en.sets.get(t).iter().any(|&o| en.nf.is_nom[o as usize]) {
                        break;
                    }
                    m.begin();
                    let w = en.new_elem_closed(m, seed, t, fb, tgt, false);
                    if !is_clean {
                        m.em(w).owner = w;
                    }
                    match en.saturate(m) {
                        Ok(()) => {
                            let w = m.find(w);
                            let polluted = m.saved_iter().any(|(&i, old)| {
                                let cur = m.find(i);
                                if cur != i {
                                    return true;
                                }
                                let newt = m.elems[cur as usize].ty;
                                if newt == old.ty {
                                    return false;
                                }
                                en.sets
                                    .get(newt)
                                    .iter()
                                    .any(|&a| (rowclass[a as usize] || nf.is_nom[a as usize]) && !en.sets.has(old.ty, a))
                            });
                            if !polluted
                                && en.sets.has(m.elems[w as usize].ty, c)
                                && (fb == 0 || !en.sets.get(fb).iter().any(|&b| en.sets.has(m.elems[w as usize].ty, b)))
                            {
                                m.em(w).pinned = true;
                                m.commit();
                                res = Some(w);
                                break;
                            }
                            m.rollback();
                            break;
                        }
                        Err(e) => {
                            m.rollback();
                            if e.is_budget() {
                                break;
                            }
                            let new: Vec<u32> = e
                                .blame
                                .iter()
                                .copied()
                                .filter(|&bt| {
                                    bt != 0
                                        && !en.bad.contains(&bt)
                                        && !en.sets.get(bt).iter().any(|&a| en.nf.is_nom[a as usize])
                                })
                                .collect();
                            if new.is_empty() {
                                break;
                            }
                            en.bad.extend(new);
                            en.clear_memo();
                        }
                    }
                }
                if en.bad.len() != base_bad.len() {
                    en.bad = base_bad;
                    en.clear_memo();
                }
                res
            };
            for &c in &classes {
                if Instant::now() > deadline || en.mem_exceeded() {
                    break;
                }
                if km_ref.unsat.contains(nf.cname_of(c)) {
                    continue;
                }
                let sup = &sup_of[&c];
                let tgt = en.sets.intern(sup.clone());
                if !wit_covered.contains(&Some(c)) {
                    if let Some(w) = try_add_clean_wit(&mut en, &mut m, c, 0, tgt) {
                        wit_covered.insert(Some(c));
                        wit_pairs.insert((Some(c), w));
                        wits.push((Some(c), w));
                        searched_wits += 1;
                        let ts = en.sets.get(m.elems[w as usize].ty);
                        let d: Vec<u32> = ts
                            .iter()
                            .copied()
                            .filter(|&b| rowclass[b as usize] && sup.binary_search(&b).is_err())
                            .collect();
                        if !d.is_empty() {
                            dirty_of.insert(c, d);
                        }
                    }
                }
                if let Some(d) = dirty_of.get(&c).cloned() {
                    let fb_all = en.sets.intern(d.clone());
                    if let Some(w) = try_add_clean_wit(&mut en, &mut m, c, fb_all, tgt) {
                        if wit_pairs.insert((Some(c), w)) {
                            wits.push((Some(c), w));
                            searched_wits += 1;
                        }
                        dirty_of.remove(&c);
                    } else {
                        let mut rem_d = Vec::new();
                        for b in d {
                            if Instant::now() > deadline || en.mem_exceeded() {
                                rem_d.push(b);
                                continue;
                            }
                            let fb1 = en.sets.intern(vec![b]);
                            if let Some(w) = try_add_clean_wit(&mut en, &mut m, c, fb1, tgt) {
                                if wit_pairs.insert((Some(c), w)) {
                                    wits.push((Some(c), w));
                                    searched_wits += 1;
                                }
                            } else {
                                rem_d.push(b);
                            }
                        }
                        if rem_d.is_empty() {
                            dirty_of.remove(&c);
                        } else {
                            dirty_of.insert(c, rem_d);
                        }
                    }
                }
            }
            if searched_wits > 0 {
                rep = check::verify(&mut en, &m);
            }
        }
        // Compact `wits` per class so any class with a clean witness (0 dirty rowclasses) keeps only 1 witness
        let mut by_cls: BTreeMap<Option<u32>, Vec<Id>> = BTreeMap::new();
        for &(a, w) in &wits {
            let w = m.find(w);
            let e = by_cls.entry(a).or_default();
            if !e.contains(&w) {
                e.push(w);
            }
        }
        let mut comp_wits: Vec<(Option<u32>, Id)> = Vec::new();
        for (a, ws) in by_cls {
            let Some(c) = a else {
                for w in ws {
                    comp_wits.push((None, w));
                }
                continue;
            };
            if ws.len() <= 1 {
                for w in ws {
                    comp_wits.push((Some(c), w));
                }
                continue;
            }
            let sup = &sup_of[&c];
            let mut cands: Vec<(Id, Vec<u32>, usize)> = Vec::with_capacity(ws.len());
            for w in ws {
                let ts = en.sets.get(m.elems[w as usize].ty);
                let miss = sup.iter().filter(|&&b| rowclass[b as usize] && ts.binary_search(&b).is_err()).count();
                let d: Vec<u32> = ts
                    .iter()
                    .copied()
                    .filter(|&b| rowclass[b as usize] && sup.binary_search(&b).is_err())
                    .collect();
                cands.push((w, d, miss));
            }
            if let Some((best_w, _, _)) = cands.iter().find(|(_, d, miss)| *miss == 0 && d.is_empty()) {
                comp_wits.push((Some(c), *best_w));
            } else {
                cands.sort_by_key(|(w, d, miss)| (*miss, d.len(), *w));
                comp_wits.push((Some(c), cands[0].0));
                let mut cur_d = cands[0].1.clone();
                let mut used = vec![false; cands.len()];
                used[0] = true;
                while !cur_d.is_empty() {
                    let mut best_i = None;
                    let mut best_rem = 0usize;
                    for (i, (_, d, miss)) in cands.iter().enumerate() {
                        if used[i] || *miss > 0 {
                            continue;
                        }
                        let rem = cur_d.iter().filter(|b| d.binary_search(b).is_err()).count();
                        if rem > best_rem {
                            best_rem = rem;
                            best_i = Some(i);
                        }
                    }
                    if let Some(i) = best_i {
                        used[i] = true;
                        comp_wits.push((Some(c), cands[i].0));
                        let d = &cands[i].1;
                        cur_d.retain(|b| d.binary_search(b).is_ok());
                    } else {
                        break;
                    }
                }
            }
        }
        wits = comp_wits;
        if let Some((target_set, prev_dirty)) = aux_targets {
            wits.retain(|&(wc, _)| wc.is_none() || wc.is_some_and(|c| target_set.contains(&c)));
            dirty_of.clear();
            for (&c, prev_ds) in prev_dirty {
                let mut left: Option<Vec<u32>> = None;
                for &(wc, w) in &wits {
                    if wc == Some(c) {
                        let ts = en.sets.get(m.elems[m.find(w) as usize].ty);
                        let d: Vec<u32> = prev_ds
                            .iter()
                            .copied()
                            .filter(|&b| ts.binary_search(&b).is_ok())
                            .collect();
                        left = Some(match left {
                            None => d,
                            Some(l) => l.into_iter().filter(|b| d.binary_search(b).is_ok()).collect(),
                        });
                    }
                }
                match left {
                    Some(d) if d.is_empty() => {}
                    Some(d) => {
                        dirty_of.insert(c, d);
                    }
                    None => {
                        dirty_of.insert(c, prev_ds.clone());
                    }
                }
            }
        }
        let all_sat_cov = classes
            .iter()
            .all(|&c| km_ref.unsat.contains(nf.cname_of(c)) || wit_covered.contains(&Some(c)));
        plus_search_full = rep.violations == 0 && all_sat_cov && dirty_of.is_empty();
        *dirty_out = dirty_of;
    }

    let mut roots: Vec<Id> = wits.iter().map(|x| x.1).collect();
    roots.extend(m.nom_elem.values().copied());
    let keep = emit::reachable(&m, &roots);
    let mut bytes = 0u64;
    let mut edges_cnt = 0usize;
    if cfg.write {
        let hp = format!("{}/model{}.hint", outdir, slot_idx);
        let wp = format!("{}/model{}.wit", outdir, slot_idx);
        let label = format!("km-hints export model {}", slot_idx);
        let dc = en.data.as_ref().map(|(d, v)| (d, v));
        if let Ok((wr, _, _)) = emit::write_hint_d(&en, &m, &keep, &hp, &label, dc) {
            bytes = wr.bytes;
            edges_cnt = wr.edges;
            let mut tbl: Vec<(&str, String, u32)> = Vec::new();
            for &(a, w) in &wits {
                let w = m.find(w);
                if let Some(&ix) = wr.index.get(&w) {
                    let iri = match a {
                        Some(c) => nf.cname_of(c).to_string(),
                        None => THING.to_string(),
                    };
                    tbl.push(("witness", iri, ix));
                }
            }
            let _ = emit::write_table(&tbl, &wp);
        }
    }

    let secs = t0.elapsed().as_secs_f64();
    let why_json = match &rep.first {
        Some(s) => json_str(s),
        None => "null".into(),
    };
    format!(
        "{{\"ok\":{},\"status\":{},\"route\":{},\"elements\":{},\"edges\":{},\"bytes\":{},\"witnesses\":{},\"witnesses_searched\":{},\"export_only_full\":{},\"plus_search_full\":{},\"violations\":{},\"first_violation\":{},\"why\":{},\"reason\":{},\"secs\":{:.3}}}",
        rep.violations == 0,
        json_str(&exp_status),
        json_str(&route),
        keep.len(),
        edges_cnt,
        bytes,
        wits.len(),
        searched_wits,
        export_only_full,
        plus_search_full,
        rep.violations,
        why_json,
        why_json,
        why_json,
        secs
    )
}
