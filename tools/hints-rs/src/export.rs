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
    b: &'a [u8],
    i: usize,
}

impl<'a> JParser<'a> {
    fn new(s: &'a str) -> Self {
        Self { b: s.as_bytes(), i: 0 }
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
        let mut out = String::new();
        while self.i < self.b.len() {
            let c = self.b[self.i];
            self.i += 1;
            if c == b'"' {
                return Ok(out);
            }
            if c == b'\\' {
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
                        let hex = std::str::from_utf8(&self.b[self.i..self.i + 4]).map_err(|e| e.to_string())?;
                        let code = u32::from_str_radix(hex, 16).map_err(|e| e.to_string())?;
                        if let Some(ch) = char::from_u32(code) {
                            out.push(ch);
                        }
                        self.i += 4;
                    }
                    other => out.push(other as char),
                }
            } else {
                // UTF-8 byte sequence
                self.i -= 1;
                let rest = std::str::from_utf8(&self.b[self.i..]).map_err(|e| e.to_string())?;
                let ch = rest.chars().next().ok_or("empty utf8")?;
                out.push(ch);
                self.i += ch.len_utf8();
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
                    if st != "ok" {
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
        let mut kept = Vec::new();
        for ind in e.individuals.drain(..) {
            if !ind_elem.contains_key(&ind) {
                ind_elem.insert(ind.clone(), idx);
                kept.push(ind);
            }
        }
        e.individuals = kept;
    }
    for (grp, el_opt) in &exp_sames {
        let target_idx = el_opt
            .as_ref()
            .and_then(|id| id_to_idx.get(id).copied())
            .or_else(|| grp.iter().find_map(|ind| ind_elem.get(ind).copied()))
            .unwrap_or(0);
        for ind in grp {
            if let Some(&prev_idx) = ind_elem.get(ind) {
                if prev_idx != target_idx {
                    exp_elems[prev_idx].individuals.retain(|x| x != ind);
                }
            }
            if !exp_elems[target_idx].individuals.contains(ind) {
                exp_elems[target_idx].individuals.push(ind.clone());
            }
            ind_elem.insert(ind.clone(), target_idx);
        }
    }
    let mut placed_noms: BTreeSet<u32> = BTreeSet::new();
    for e in &mut exp_elems {
        let mut kept = Vec::new();
        for ind in e.individuals.drain(..) {
            if let Some(& (_, c)) = nf.nominal.iter().find(|(i, _)| i == &ind) {
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
    if !exp_blocked.is_empty() {
        let mut edge_set: std::collections::HashSet<(String, String, String)> =
            exp_edges.iter().cloned().collect();
        for _pass in 0..4 {
            for (el_id, blk_id) in &exp_blocked {
                let (Some(&ei), Some(&bi)) = (id_to_idx.get(el_id), id_to_idx.get(blk_id)) else { continue };
                let blk_classes = exp_elems[bi].classes.clone();
                exp_elems[ei].classes.extend(blk_classes);
                exp_elems[ei].classes.sort_unstable();
                exp_elems[ei].classes.dedup();
                let el_roles: std::collections::HashSet<String> = exp_edges
                    .iter()
                    .filter(|(f, _, _)| f == el_id)
                    .map(|(_, r, _)| r.clone())
                    .collect();
                let blk_out: Vec<(String, String)> = exp_edges
                    .iter()
                    .filter(|(f, r, t)| {
                        if f != blk_id {
                            return false;
                        }
                        if el_roles.contains(r) {
                            if let Some(&ti) = id_to_idx.get(t) {
                                if ti < bi && exp_elems[ti].individuals.is_empty() {
                                    return false;
                                }
                            }
                        }
                        true
                    })
                    .map(|(_, r, t)| (r.clone(), t.clone()))
                    .collect();
                for (r, t) in blk_out {
                    let edge = (el_id.clone(), r, t);
                    if edge_set.insert(edge.clone()) {
                        exp_edges.push(edge);
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
    let mut pos: Vec<Vec<bool>> = vec![vec![false; n]; k_elems];
    let mut neg: Vec<Vec<bool>> = vec![vec![false; n]; k_elems];

    for (idx, ee) in exp_elems.iter().enumerate() {
        if let Some(tc) = thing_c {
            pos[idx][tc as usize] = true;
        }
        for c_iri in &ee.classes {
            if let Some(&c) = nf.cidx.get(c_iri.as_str()) {
                pos[idx][c as usize] = true;
            }
        }
        let mut has_nom = false;
        for i_iri in &ee.individuals {
            if let Some(&o) = nom_map.get(i_iri.as_str()) {
                pos[idx][o as usize] = true;
                has_nom = true;
            }
        }
        let seed_vec: Vec<u32> = (0..n as u32).filter(|&a| pos[idx][a as usize]).collect();
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
            if let Some(&o) = nom_map.get(i_iri.as_str()) {
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
                pos[x][h[0] as usize] = true;
            }
        }
        for a in 0..n as u32 {
            if pos[x][a as usize] {
                q_pos.push((x, a));
            }
        }
    }
    while let Some((x, a)) = q_pos.pop() {
        for &g in nf.gci_by_body.get(a) {
            let (body, head) = &nf.gci[g as usize];
            if head.len() == 1 && !pos[x][head[0] as usize] && body.iter().all(|&b| pos[x][b as usize]) {
                let h0 = head[0];
                pos[x][h0 as usize] = true;
                q_pos.push((x, h0));
            }
        }
        for &(s, c) in nf.all_by.get(a) {
            for &(y, l) in &m.elems[x].edges {
                if en.labs.has(l, s) && !pos[y as usize][c as usize] {
                    pos[y as usize][c as usize] = true;
                    q_pos.push((y as usize, c));
                }
            }
        }
    }

    // Initialize `neg[x]` for all source concepts (`named` or `is_nom`) not in `pos[x]`
    for x in 0..k_elems {
        for c in 0..n {
            if (nf.named[c] || nf.is_nom[c]) && !pos[x][c] {
                neg[x][c] = true;
            }
        }
    }

    // Precompute reverse index `head_by[h]` (which GCIs have `h` in `head`),
    // `modal_concepts` (concepts with existential/universal/cardinality restrictions),
    // `is_modal_filler` (concepts appearing as the target of a modal clause),
    // and incoming element neighbours `in_elems[y]`
    let mut head_by: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (gi, (_, head)) in nf.gci.iter().enumerate() {
        for &h in head {
            head_by[h as usize].push(gi as u32);
        }
    }
    let mut is_modal_filler = vec![false; n];
    for &(_, _, b) in &nf.ex {
        if (b as usize) < n {
            is_modal_filler[b as usize] = true;
        }
    }
    for &(_, _, _, b) in &nf.ge {
        if (b as usize) < n {
            is_modal_filler[b as usize] = true;
        }
    }
    for &(_, _, _, b) in &nf.le {
        if (b as usize) < n {
            is_modal_filler[b as usize] = true;
        }
    }
    for &(_, _, b) in &nf.all {
        if (b as usize) < n {
            is_modal_filler[b as usize] = true;
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
    let mut in_elems: Vec<Vec<usize>> = vec![Vec::new(); k_elems];
    for x in 0..k_elems {
        for &(y, _) in &m.elems[x].edges {
            if (y as usize) < k_elems {
                in_elems[y as usize].push(x);
            }
        }
    }
    for v in &mut in_elems {
        v.sort_unstable();
        v.dedup();
    }

    let check_gci_unit = |gi: u32,
                          x: usize,
                          pos: &mut [Vec<bool>],
                          neg: &mut [Vec<bool>],
                          q_lit: &mut Vec<(usize, u32, bool)>| {
        let (body, head) = &nf.gci[gi as usize];
        let body_true = body.iter().all(|&b| pos[x][b as usize]);
        if body_true {
            if head.iter().any(|&h| pos[x][h as usize]) {
                return;
            }
            let mut open_h = NONE;
            let mut cnt_h = 0usize;
            for &h in head {
                if !neg[x][h as usize] {
                    open_h = h;
                    cnt_h += 1;
                    if cnt_h > 1 {
                        break;
                    }
                }
            }
            if cnt_h == 1 && !pos[x][open_h as usize] {
                pos[x][open_h as usize] = true;
                q_lit.push((x, open_h, true));
            }
        } else if head.iter().all(|&h| neg[x][h as usize]) {
            if body.iter().any(|&b| neg[x][b as usize]) {
                return;
            }
            let mut open_b = NONE;
            let mut cnt_b = 0usize;
            for &b in body {
                if !pos[x][b as usize] {
                    open_b = b;
                    cnt_b += 1;
                    if cnt_b > 1 {
                        break;
                    }
                }
            }
            if cnt_b == 1 && !neg[x][open_b as usize] {
                neg[x][open_b as usize] = true;
                q_lit.push((x, open_b, false));
            }
        }
    };

    let data_rel_concepts: Vec<u32> = if en.data.is_some() {
        (0..n as u32).filter(|&a| en.has_data[a as usize]).collect()
    } else {
        Vec::new()
    };

    // Incremental forward (`pos`) + backward (`neg`) fixpoint starting from dirty elements / literals
    let propagate_incremental = |dirty_seed: &[usize],
                                 seed_lits: &[(usize, u32, bool)],
                                 full_gci_scan: bool,
                                 pos: &mut [Vec<bool>],
                                 neg: &mut [Vec<bool>],
                                 m: &Model,
                                 en: &Engine| {
        let mut q_lit: Vec<(usize, u32, bool)> = seed_lits.to_vec();
        let mut dirty_modal: Vec<bool> = vec![false; k_elems];
        let mut modal_q: Vec<usize> = Vec::new();
        for &x in dirty_seed {
            if !dirty_modal[x] {
                dirty_modal[x] = true;
                modal_q.push(x);
            }
            if full_gci_scan {
                for gi in 0..nf.gci.len() as u32 {
                    check_gci_unit(gi, x, pos, neg, &mut q_lit);
                }
            }
        }
        let mut steps = 0usize;
        loop {
            while let Some((x, a, is_pos)) = q_lit.pop() {
                steps += 1;
                if steps & 4095 == 0 && Instant::now() > deadline {
                    return;
                }
                if is_pos {
                    if !data_rel_concepts.is_empty() && data_rel_concepts.binary_search(&a).is_ok() {
                        for &peer in &data_rel_concepts {
                            if peer != a
                                && !neg[x][peer as usize]
                                && !pos[x][peer as usize]
                                && en.has_conflict_peer(a, peer)
                            {
                                neg[x][peer as usize] = true;
                                q_lit.push((x, peer, false));
                            }
                        }
                    }
                    for &gi in nf.gci_by_body.get(a) {
                        check_gci_unit(gi, x, pos, neg, &mut q_lit);
                    }
                    if !nf.all_by.get(a).is_empty()
                        || !nf.ex_by.get(a).is_empty()
                        || !nf.ge_by.get(a).is_empty()
                        || nf.has_le[a as usize]
                    {
                        if !dirty_modal[x] {
                            dirty_modal[x] = true;
                            modal_q.push(x);
                        }
                    }
                } else {
                    for &gi in &head_by[a as usize] {
                        check_gci_unit(gi, x, pos, neg, &mut q_lit);
                    }
                }
                if is_modal_filler[a as usize] {
                    for &pred in &in_elems[x] {
                        if !dirty_modal[pred] {
                            dirty_modal[pred] = true;
                            modal_q.push(pred);
                        }
                    }
                }
            }
            let Some(x) = modal_q.pop() else { break };
            dirty_modal[x] = false;
            steps += 1;
            if steps & 1023 == 0 && Instant::now() > deadline {
                return;
            }
            if m.elems[x].edges.is_empty() {
                // Only `ex_by` / `ge_by` with k > 0 can refute `a` when `x` has no outgoing edges
                for &a in &modal_concepts {
                    if pos[x][a as usize] || neg[x][a as usize] {
                        continue;
                    }
                    if !nf.ex_by.get(a).is_empty() || nf.ge_by.get(a).iter().any(|&(k, _, _)| k > 0) {
                        neg[x][a as usize] = true;
                        q_lit.push((x, a, false));
                    }
                }
                continue;
            }
            // Backward refutation from missing/violated edges on `x`
            for &a in &modal_concepts {
                if pos[x][a as usize] || neg[x][a as usize] {
                    continue;
                }
                let mut ref_a = false;
                for &(r, b) in nf.ex_by.get(a) {
                    let has_poss = m.elems[x]
                        .edges
                        .iter()
                        .any(|&(y, l)| en.labs.has(l, r) && !neg[y as usize][b as usize]);
                    if !has_poss {
                        ref_a = true;
                        break;
                    }
                }
                if !ref_a {
                    for &(k, r, b) in nf.ge_by.get(a) {
                        let poss_cnt = m.elems[x]
                            .edges
                            .iter()
                            .filter(|&&(y, l)| en.labs.has(l, r) && !neg[y as usize][b as usize])
                            .count();
                        if poss_cnt < k as usize {
                            ref_a = true;
                            break;
                        }
                    }
                }
                if !ref_a && nf.has_le[a as usize] {
                    for &(k, r, b) in nf.le_by.get(a) {
                        let forced_cnt = m.elems[x]
                            .edges
                            .iter()
                            .filter(|&&(y, l)| en.labs.has(l, r) && pos[y as usize][b as usize])
                            .count();
                        if forced_cnt > k as usize {
                            ref_a = true;
                            break;
                        }
                    }
                }
                if !ref_a {
                    for &(s, c) in nf.all_by.get(a) {
                        let bad_all = m.elems[x]
                            .edges
                            .iter()
                            .any(|&(y, l)| en.labs.has(l, s) && neg[y as usize][c as usize]);
                        if bad_all {
                            ref_a = true;
                            break;
                        }
                    }
                }
                if ref_a {
                    neg[x][a as usize] = true;
                    q_lit.push((x, a, false));
                }
            }
            // Edge propagation from `pos[x]`
            for &a in &modal_concepts {
                if !pos[x][a as usize] {
                    continue;
                }
                for &(s, c) in nf.all_by.get(a) {
                    for &(y, l) in &m.elems[x].edges {
                        if en.labs.has(l, s) && !pos[y as usize][c as usize] && !neg[y as usize][c as usize] {
                            pos[y as usize][c as usize] = true;
                            q_lit.push((y as usize, c, true));
                        }
                    }
                }
                for &(r, b) in nf.ex_by.get(a) {
                    let already = m.elems[x]
                        .edges
                        .iter()
                        .any(|&(y, l)| en.labs.has(l, r) && pos[y as usize][b as usize]);
                    if !already {
                        let mut only_y: Option<usize> = None;
                        let mut cnt = 0usize;
                        for &(y, l) in &m.elems[x].edges {
                            if en.labs.has(l, r) && !neg[y as usize][b as usize] {
                                only_y = Some(y as usize);
                                cnt += 1;
                                if cnt > 1 {
                                    break;
                                }
                            }
                        }
                        if cnt == 1 {
                            let y0 = only_y.unwrap();
                            if !pos[y0][b as usize] {
                                pos[y0][b as usize] = true;
                                q_lit.push((y0, b, true));
                            }
                        }
                    }
                }
                for &(k, r, b) in nf.ge_by.get(a) {
                    let cands: Vec<Id> = m.elems[x]
                        .edges
                        .iter()
                        .filter(|&&(y, l)| en.labs.has(l, r) && !neg[y as usize][b as usize])
                        .map(|e| e.0)
                        .collect();
                    if cands.len() == k as usize {
                        for y0 in cands {
                            if !pos[y0 as usize][b as usize] {
                                pos[y0 as usize][b as usize] = true;
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
                            .filter(|&&(y, l)| en.labs.has(l, r) && pos[y as usize][b as usize])
                            .count();
                        if pos_cnt == k as usize {
                            for &(y, l) in &m.elems[x].edges {
                                if en.labs.has(l, r) && !pos[y as usize][b as usize] && !neg[y as usize][b as usize] {
                                    neg[y as usize][b as usize] = true;
                                    q_lit.push((y as usize, b, false));
                                }
                            }
                        }
                    }
                }
            }
        }
    };

    let all_elems: Vec<usize> = (0..k_elems).collect();
    propagate_incremental(&all_elems, &[], true, &mut pos, &mut neg, &m, &en);

    // Step 3: Close any remaining open disjunctive GCIs or existentials on each element
    // avoiding `neg[x]` (and preferring 0-requirement fresh concepts such as `dall`)
    let test_candidate_on_elem = |x: usize,
                                  cand_lit: u32,
                                  pos: &[Vec<bool>],
                                  neg: &[Vec<bool>],
                                  en: &mut Engine|
     -> bool {
        if neg[x][cand_lit as usize] {
            return false;
        }
        let mut px = pos[x].clone();
        let mut nx = neg[x].clone();
        px[cand_lit as usize] = true;
        let mut q: Vec<(u32, bool)> = vec![(cand_lit, true)];
        while let Some((a, is_p)) = q.pop() {
            if is_p {
                if !data_rel_concepts.is_empty() && data_rel_concepts.binary_search(&a).is_ok() {
                    for &peer in &data_rel_concepts {
                        if peer != a && en.has_conflict_peer(a, peer) {
                            if px[peer as usize] {
                                return false;
                            }
                            if !nx[peer as usize] {
                                nx[peer as usize] = true;
                                q.push((peer, false));
                            }
                        }
                    }
                }
                for &g in nf.gci_by_body.get(a) {
                    let (b_g, h_g) = &nf.gci[g as usize];
                    if b_g.iter().all(|&b| px[b as usize]) {
                        if h_g.iter().any(|&h| px[h as usize]) {
                            continue;
                        }
                        let mut open_h = NONE;
                        let mut cnt = 0usize;
                        for &h in h_g {
                            if !nx[h as usize] {
                                open_h = h;
                                cnt += 1;
                                if cnt > 1 {
                                    break;
                                }
                            }
                        }
                        if cnt == 0 {
                            return false;
                        }
                        if cnt == 1 && !px[open_h as usize] {
                            px[open_h as usize] = true;
                            q.push((open_h, true));
                        }
                    }
                }
            } else {
                for &g in &head_by[a as usize] {
                    let (b_g, h_g) = &nf.gci[g as usize];
                    if b_g.iter().all(|&b| px[b as usize]) {
                        if h_g.iter().any(|&h| px[h as usize]) {
                            continue;
                        }
                        let mut open_h = NONE;
                        let mut cnt = 0usize;
                        for &h in h_g {
                            if !nx[h as usize] {
                                open_h = h;
                                cnt += 1;
                                if cnt > 1 {
                                    break;
                                }
                            }
                        }
                        if cnt == 0 {
                            return false;
                        }
                        if cnt == 1 && !px[open_h as usize] {
                            px[open_h as usize] = true;
                            q.push((open_h, true));
                        }
                    } else if h_g.iter().all(|&h| nx[h as usize]) {
                        if b_g.iter().any(|&b| nx[b as usize]) {
                            continue;
                        }
                        let mut open_b = NONE;
                        let mut cnt = 0usize;
                        for &b in b_g {
                            if !px[b as usize] {
                                open_b = b;
                                cnt += 1;
                                if cnt > 1 {
                                    break;
                                }
                            }
                        }
                        if cnt == 0 {
                            return false;
                        }
                        if cnt == 1 && !nx[open_b as usize] {
                            nx[open_b as usize] = true;
                            q.push((open_b, false));
                        }
                    }
                }
            }
        }
        if !data_rel_concepts.is_empty() {
            let active_d: Vec<u32> = data_rel_concepts
                .iter()
                .copied()
                .filter(|&a| px[a as usize])
                .collect();
            for i in 0..active_d.len() {
                for j in (i + 1)..active_d.len() {
                    if en.has_conflict_peer(active_d[i], active_d[j]) {
                        return false;
                    }
                }
            }
            if !active_d.is_empty() && !en.has_data_star(active_d) {
                return false;
            }
        }
        true
    };
    for x in 0..k_elems {
        if Instant::now() > deadline || en.mem_exceeded() {
            let why = if en.mem_hit { "memory cap (8 GB) exceeded" } else { "from-export time budget exceeded" };
            return format!(
                "{{\"ok\":false,\"status\":\"timeout\",\"route\":{},\"why\":{},\"reason\":{}}}",
                json_str(&route),
                json_str(why),
                json_str(why)
            );
        }
        for _pass in 0..3 {
            let mut any_change = false;
            for gi in 0..nf.gci.len() {
                let (body, head) = &nf.gci[gi];
                if !body.iter().all(|&b| pos[x][b as usize]) || head.iter().any(|&h| pos[x][h as usize]) {
                    continue;
                }
                let mut best_h: Option<((bool, usize, u32), u32)> = None;
                let mut newly_neg: Vec<(usize, u32, bool)> = Vec::new();
                for &h in head {
                    if neg[x][h as usize] {
                        continue;
                    }
                    if !test_candidate_on_elem(x, h, &pos, &neg, &mut en) {
                        neg[x][h as usize] = true;
                        newly_neg.push((x, h, false));
                        continue;
                    }
                    let is_src = nf.named[h as usize] || nf.is_nom[h as usize];
                    let reqs = nf.ex_by.get(h).len()
                        + nf.ge_by.get(h).len()
                        + en.dreq.get(h as usize).copied().unwrap_or(0) as usize;
                    let key = (is_src, reqs, h);
                    if best_h.map(|b| key < b.0).unwrap_or(true) {
                        best_h = Some((key, h));
                    }
                }
                if !newly_neg.is_empty() {
                    propagate_incremental(&[], &newly_neg, false, &mut pos, &mut neg, &m, &en);
                    any_change = true;
                }
                if head.iter().any(|&h| pos[x][h as usize]) {
                    continue;
                }
                if let Some((_, h)) = best_h {
                    if !neg[x][h as usize] {
                        pos[x][h as usize] = true;
                        any_change = true;
                        let is_inert = nf.gci_by_body.get(h).is_empty()
                            && nf.all_by.get(h).is_empty()
                            && nf.ex_by.get(h).is_empty()
                            && nf.ge_by.get(h).is_empty()
                            && !nf.has_le[h as usize]
                            && !is_modal_filler[h as usize];
                        if !is_inert {
                            propagate_incremental(&[], &[(x, h, true)], false, &mut pos, &mut neg, &m, &en);
                        }
                    }
                }
            }
            if !any_change {
                break;
            }
        }
        // If an active existential `some a r b` on `x` is still unmet among `r`-neighbours,
        // pick a compatible `r`-neighbour `y` with `!neg[y][b]`
        for &a in &modal_concepts {
            if !pos[x][a as usize] {
                continue;
            }
            for &(r, b) in nf.ex_by.get(a) {
                let met = m.elems[x]
                    .edges
                    .iter()
                    .any(|&(y, l)| en.labs.has(l, r) && pos[y as usize][b as usize]);
                if !met {
                    let chosen_y = m.elems[x]
                        .edges
                        .iter()
                        .find(|&&(y, l)| {
                            en.labs.has(l, r)
                                && !neg[y as usize][b as usize]
                                && test_candidate_on_elem(y as usize, b, &pos, &neg, &mut en)
                        })
                        .or_else(|| {
                            m.elems[x]
                                .edges
                                .iter()
                                .find(|&&(y, l)| en.labs.has(l, r) && !neg[y as usize][b as usize])
                        });
                    if let Some(&(y, _)) = chosen_y {
                        pos[y as usize][b as usize] = true;
                        propagate_incremental(&[], &[(y as usize, b, true)], false, &mut pos, &mut neg, &m, &en);
                    }
                }
            }
        }
    }

    // Store closed types into `m`
    for x in 0..k_elems {
        let p_vec: Vec<u32> = (0..n as u32).filter(|&a| pos[x][a as usize]).collect();
        let f_vec: Vec<u32> = (0..n as u32)
            .filter(|&a| (nf.named[a as usize] || nf.is_nom[a as usize]) && !pos[x][a as usize])
            .collect();
        let tid = en.sets.intern(p_vec);
        let fid = en.sets.intern(f_vec);
        let tgt_vec: Vec<u32> = (0..n as u32)
            .filter(|&a| pos[x][a as usize] && (nf.named[a as usize] || nf.is_nom[a as usize]))
            .collect();
        let tgt_id = en.sets.intern(tgt_vec);
        let e = m.em(x as Id);
        e.ty = tid;
        e.forced = tid;
        e.forbid = fid;
        e.target = tgt_id;
        m.tm_push(tid, x as Id);
    }

    // Self-check, with optional bounded saturation repair if an exported node needed an unexpanded filler
    let mut rep = check::verify(&mut en, &m);
    if rep.violations > 0 && Instant::now() < deadline && !en.mem_exceeded() {
        let rep_deadline = deadline.min(Instant::now() + std::time::Duration::from_secs(10));
        en.opt.deadline = Some(rep_deadline);
        for &bad_x in &rep.bad {
            if Instant::now() > rep_deadline || en.mem_exceeded() {
                break;
            }
            let e = &m.elems[bad_x as usize];
            if let CloseRes::Ok(t_new) = en.close(e.ty, e.forbid, e.target, e.nom) {
                m.em(bad_x).ty = t_new;
            }
            m.enqueue(bad_x);
        }
        let _ = en.saturate(&mut m);
        rep = check::verify(&mut en, &m);
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
    for x in m.canonical() {
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

    // Pass 1: if `km` classification is provided and a class `c` still has unseparated
    // non-superclasses across its current witnesses in `wits`, check if any other
    // existing canonical element in `m` separates them.
    if let Some(km_ref) = km {
        let canon_elems: Vec<Id> = m.canonical().collect();
        for &c in &classes {
            let c_iri = nf.cname_of(c);
            if km_ref.unsat.contains(c_iri) {
                continue;
            }
            let cur_wits: Vec<Id> = wits
                .iter()
                .filter_map(|&(wc, w)| if wc == Some(c) { Some(m.find(w)) } else { None })
                .collect();
            if cur_wits.is_empty() {
                continue;
            }
            let sup_set = km_ref.sup.get(c_iri);
            let mut unsep: Vec<u32> = classes
                .iter()
                .copied()
                .filter(|&b| {
                    b != c
                        && !km_ref.top.contains(nf.cname_of(b))
                        && !sup_set.map(|s| s.contains(nf.cname_of(b))).unwrap_or(false)
                        && cur_wits
                            .iter()
                            .all(|&w| en.sets.has(m.elems[w as usize].ty, b))
                })
                .collect();
            if unsep.is_empty() {
                continue;
            }
            for &x in &canon_elems {
                let ty = m.elems[x as usize].ty;
                if !en.sets.has(ty, c) {
                    continue;
                }
                if unsep.iter().any(|&b| !en.sets.has(ty, b)) {
                    if wit_pairs.insert((Some(c), x)) {
                        wits.push((Some(c), x));
                    }
                    unsep.retain(|&b| en.sets.has(ty, b));
                    if unsep.is_empty() {
                        break;
                    }
                }
            }
        }
    }

    let mut roots: Vec<Id> = wits.iter().map(|x| x.1).collect();
    roots.extend(m.nom_elem.values().copied());
    let keep = emit::reachable(&m, &roots);
    let mut bytes = 0u64;
    let mut edges_cnt = 0usize;
    if cfg.write {
        let hp = format!("{}/model0.hint", outdir);
        let wp = format!("{}/model0.wit", outdir);
        let dc = en.data.as_ref().map(|(d, v)| (d, v));
        if let Ok((wr, _, _)) = emit::write_hint_d(&en, &m, &keep, &hp, "km-hints export model 0", dc) {
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
        "{{\"ok\":{},\"route\":{},\"elements\":{},\"edges\":{},\"bytes\":{},\"witnesses\":{},\"violations\":{},\"first_violation\":{},\"why\":{},\"reason\":{},\"secs\":{:.3}}}",
        rep.violations == 0,
        json_str(&route),
        keep.len(),
        edges_cnt,
        bytes,
        wits.len(),
        rep.violations,
        why_json,
        why_json,
        why_json,
        secs
    )
}
