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
                return format!(
                    "{{\"ok\":false,\"status\":\"bad-export\",\"why\":{}}}",
                    json_str(&format!("line {}: {}", lno + 1, e))
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
                            "{{\"ok\":false,\"status\":{},\"route\":{},\"why\":{}}}",
                            json_str(st),
                            json_str(&route),
                            json_str(why)
                        );
                    }
                }
            }
            "element" => {
                let id = val.str_field("id").unwrap_or("").to_string();
                let classes = val.str_list("classes");
                let individuals = val.str_list("individuals");
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
                let inds = val.str_list("individuals");
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

    // Apply `same` groups and ensure every ontology nominal is placed on an element
    let mut ind_elem: HashMap<String, usize> = HashMap::new();
    for (idx, e) in exp_elems.iter().enumerate() {
        for ind in &e.individuals {
            ind_elem.insert(ind.clone(), idx);
        }
    }
    for (grp, el_opt) in &exp_sames {
        let target_idx = el_opt
            .as_ref()
            .and_then(|id| id_to_idx.get(id).copied())
            .or_else(|| grp.iter().find_map(|ind| ind_elem.get(ind).copied()))
            .unwrap_or(0);
        for ind in grp {
            if !exp_elems[target_idx].individuals.contains(ind) {
                exp_elems[target_idx].individuals.push(ind.clone());
            }
            ind_elem.insert(ind.clone(), target_idx);
        }
    }
    for (iri, _) in &nf.nominal {
        if !iri.starts_with("urn:km:")
            && !iri.starts_with('#')
            && !iri.starts_with('%')
            && !ind_elem.contains_key(iri)
        {
            let idx = exp_elems.len();
            let id = format!("__ind_{}", idx);
            id_to_idx.insert(id.clone(), idx);
            exp_elems.push(ExportElem { id, classes: Vec::new(), individuals: vec![iri.clone()] });
            ind_elem.insert(iri.clone(), idx);
        }
    }

    // Resolve `blocked` pairs by copying blocker classes and outgoing edges to the blocked element
    if !exp_blocked.is_empty() {
        for _pass in 0..4 {
            for (el_id, blk_id) in &exp_blocked {
                let (Some(&ei), Some(&bi)) = (id_to_idx.get(el_id), id_to_idx.get(blk_id)) else { continue };
                let blk_classes = exp_elems[bi].classes.clone();
                for c in blk_classes {
                    if !exp_elems[ei].classes.contains(&c) {
                        exp_elems[ei].classes.push(c);
                    }
                }
                let blk_out: Vec<(String, String)> = exp_edges
                    .iter()
                    .filter(|(f, _, _)| f == blk_id)
                    .map(|(_, r, t)| (r.clone(), t.clone()))
                    .collect();
                for (r, t) in blk_out {
                    let edge = (el_id.clone(), r, t);
                    if !exp_edges.contains(&edge) {
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
    let nom_map: HashMap<&str, u32> = nf.nominal.iter().map(|(i, c)| (i.as_str(), *c)).collect();

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

    // Add exported edges
    for (from_id, role_iri, to_id) in &exp_edges {
        let (Some(&u), Some(&v)) = (id_to_idx.get(from_id), id_to_idx.get(to_id)) else { continue };
        if u == v && !cfg.loops && !m.elems[u].nom {
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
                        if u == v && !cfg.loops && !m.elems[u as usize].nom {
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

    // Step 1: Forward pure-Horn + universal closure on `pos` so implied source superclasses
    // and positive definers are present before initializing `neg` on complement source names
    loop {
        let mut changed = false;
        for x in 0..k_elems {
            for &g in &nf.gci_empty {
                let h = &nf.gci[g as usize].1;
                if h.len() == 1 && !pos[x][h[0] as usize] {
                    pos[x][h[0] as usize] = true;
                    changed = true;
                }
            }
            for (body, head) in &nf.gci {
                if head.len() == 1 && body.iter().all(|&b| pos[x][b as usize]) && !pos[x][head[0] as usize] {
                    pos[x][head[0] as usize] = true;
                    changed = true;
                }
            }
            for a in 0..n as u32 {
                if !pos[x][a as usize] {
                    continue;
                }
                for &(s, c) in nf.all_by.get(a) {
                    for &(y, l) in &m.elems[x].edges {
                        if en.labs.has(l, s) && !pos[y as usize][c as usize] {
                            pos[y as usize][c as usize] = true;
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
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

    // Step 2: Deterministic forward (`pos`) + backward (`neg`) fixpoint over the graph
    let propagate_fixpoint = |pos: &mut [Vec<bool>], neg: &mut [Vec<bool>], m: &Model, en: &Engine| {
        loop {
            let mut changed = false;
            for x in 0..k_elems {
                // Backward refutation from missing/violated edges
                for a in 0..n as u32 {
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
                        changed = true;
                    }
                }
                // GCI unit propagation (forward and contrapositive backward)
                for (body, head) in &nf.gci {
                    let body_true = body.iter().all(|&b| pos[x][b as usize]);
                    if body_true {
                        if head.iter().any(|&h| pos[x][h as usize]) {
                            continue;
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
                            changed = true;
                        }
                    } else if head.iter().all(|&h| neg[x][h as usize]) {
                        if body.iter().any(|&b| neg[x][b as usize]) {
                            continue;
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
                            changed = true;
                        }
                    }
                }
                // Edge propagation from `pos[x]`
                for a in 0..n as u32 {
                    if !pos[x][a as usize] {
                        continue;
                    }
                    for &(s, c) in nf.all_by.get(a) {
                        for &(y, l) in &m.elems[x].edges {
                            if en.labs.has(l, s) && !pos[y as usize][c as usize] && !neg[y as usize][c as usize] {
                                pos[y as usize][c as usize] = true;
                                changed = true;
                            }
                        }
                    }
                    for &(r, b) in nf.ex_by.get(a) {
                        let already = m.elems[x]
                            .edges
                            .iter()
                            .any(|&(y, l)| en.labs.has(l, r) && pos[y as usize][b as usize]);
                        if !already {
                            let cands: Vec<Id> = m.elems[x]
                                .edges
                                .iter()
                                .filter(|&&(y, l)| en.labs.has(l, r) && !neg[y as usize][b as usize])
                                .map(|e| e.0)
                                .collect();
                            if cands.len() == 1 {
                                let y0 = cands[0] as usize;
                                pos[y0][b as usize] = true;
                                changed = true;
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
                                    changed = true;
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
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
    };

    propagate_fixpoint(&mut pos, &mut neg, &m, &en);

    // Step 3: Close any remaining open disjunctive GCIs or existentials on each element
    // avoiding `neg[x]` (and preferring 0-requirement fresh concepts such as `dall`)
    for x in 0..k_elems {
        loop {
            let mut picked_any = false;
            let mut negated_any = false;
            for (body, head) in &nf.gci {
                if body.iter().all(|&b| pos[x][b as usize]) && !head.iter().any(|&h| pos[x][h as usize]) {
                    let mut best_h: Option<((bool, usize, u32), u32)> = None;
                    for &h in head {
                        if neg[x][h as usize] {
                            continue;
                        }
                        if let Some((d, v)) = &en.data {
                            let mut cand: Vec<u32> = (0..n as u32).filter(|&a| pos[x][a as usize] || a == h).collect();
                            cand.sort_unstable();
                            if crate::data::star(d, v, &cand).is_none() {
                                neg[x][h as usize] = true;
                                negated_any = true;
                                continue;
                            }
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
                    if negated_any {
                        break;
                    }
                    if let Some((_, h)) = best_h {
                        pos[x][h as usize] = true;
                        picked_any = true;
                        break;
                    }
                }
            }
            if negated_any || picked_any {
                propagate_fixpoint(&mut pos, &mut neg, &m, &en);
            } else {
                break;
            }
        }
        // If an active existential `some a r b` on `x` is still unmet among `r`-neighbours,
        // pick a compatible `r`-neighbour `y` with `!neg[y][b]`
        for a in 0..n as u32 {
            if !pos[x][a as usize] {
                continue;
            }
            for &(r, b) in nf.ex_by.get(a) {
                let met = m.elems[x]
                    .edges
                    .iter()
                    .any(|&(y, l)| en.labs.has(l, r) && pos[y as usize][b as usize]);
                if !met {
                    if let Some(&(y, _)) = m.elems[x]
                        .edges
                        .iter()
                        .find(|&&(y, l)| en.labs.has(l, r) && !neg[y as usize][b as usize])
                    {
                        pos[y as usize][b as usize] = true;
                        propagate_fixpoint(&mut pos, &mut neg, &m, &en);
                    }
                }
            }
        }
    }

    // Store closed types into `m`
    for x in 0..k_elems {
        let p_vec: Vec<u32> = (0..n as u32).filter(|&a| pos[x][a as usize]).collect();
        let f_vec: Vec<u32> = (0..n as u32).filter(|&a| neg[x][a as usize]).collect();
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

    // Self-check, with optional saturation repair if an exported node needed an unexpanded filler
    let mut rep = check::verify(&mut en, &m);
    if rep.violations > 0 {
        for &bad_x in &rep.bad {
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
    let canon_0 = m.canonical().next().unwrap_or(0);
    wits.push((None, canon_0));
    wit_covered.insert(None);

    for (cls_iri, el_id, _) in &exp_witnesses {
        if cls_iri == THING {
            if let Some(&idx) = id_to_idx.get(el_id) {
                wits[0] = (None, m.find(idx as Id));
            }
            continue;
        }
        if let (Some(&c), Some(&idx)) = (nf.cidx.get(cls_iri.as_str()), id_to_idx.get(el_id)) {
            if rowclass[c as usize] {
                let w = m.find(idx as Id);
                if en.sets.has(m.elems[w as usize].ty, c) && wit_covered.insert(Some(c)) {
                    wits.push((Some(c), w));
                }
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
        if let Some(w) = m.canonical().find(|&x| en.sets.has(m.elems[x as usize].ty, c)) {
            wit_covered.insert(Some(c));
            wits.push((Some(c), w));
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
    format!(
        "{{\"ok\":{},\"route\":{},\"elements\":{},\"edges\":{},\"bytes\":{},\"witnesses\":{},\"violations\":{},\"first_violation\":{},\"secs\":{:.3}}}",
        rep.violations == 0,
        json_str(&route),
        keep.len(),
        edges_cnt,
        bytes,
        wits.len(),
        rep.violations,
        match &rep.first {
            Some(s) => json_str(s),
            None => "null".into(),
        },
        secs
    )
}
