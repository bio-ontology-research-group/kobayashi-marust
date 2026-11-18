//! The producer: km's rows and the normal form in, one or more global
//! models with witness tables out.
//!
//! Model 0 holds an element per named individual (merged per km's SAME
//! rows) and a witness element per satisfiable class. A witness whose
//! construction would add a named class outside the target of an earlier
//! witness or individual ("pollution") moves to model 1, 2, ...; a witness
//! that holds a named class km does not list as a superclass is "dirty" and
//! gets extra witnesses that forbid the dirty names (split witnesses).

use crate::check;
use crate::emit;
use crate::engine::{CloseRes, Engine, Fail, FxMap, Id, Model, Opts};
use crate::km::{Km, NOTHING, THING};
use crate::nf::Nf;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::time::Instant;

pub struct Config {
    pub max_models: usize,
    pub retries: usize,
    pub split_cap: usize,
    pub unsat_checks: usize,
    pub time_limit: f64,
    pub loops: bool,
    pub write: bool,
    pub no_realize: bool,
    /// the data clauses, for data stars (None: no `dstar` lines)
    pub data: Option<crate::data::DataNf>,
}

pub struct Slot {
    pub m: Model,
    /// (class concept or None for owl:Thing, element)
    pub wits: Vec<(Option<u32>, Id)>,
    pub wit_of: FxMap<Id, Vec<Option<u32>>>,
}

enum WRes {
    Ok(Id),
    Polluted,
    Fail(String),
}

pub struct Ctx<'a> {
    #[allow(dead_code)]
    nf: &'a Nf,
    rowclass: Vec<bool>,
    target: FxMap<Option<u32>, u32>,
    nom_target: FxMap<u32, u32>,
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

pub fn peak_rss_mb() -> u64 {
    if let Ok(s) = std::fs::read_to_string("/proc/self/status") {
        for l in s.lines() {
            if let Some(r) = l.strip_prefix("VmHWM:") {
                let kb: u64 = r.trim().trim_end_matches("kB").trim().parse().unwrap_or(0);
                return kb / 1024;
            }
        }
    }
    0
}

impl<'a> Ctx<'a> {
    fn named_gain(&self, en: &Engine, old: u32, new: u32) -> Vec<u32> {
        let o = en.sets.get(old);
        en.sets
            .get(new)
            .iter()
            .copied()
            .filter(|&a| self.rowclass[a as usize] && o.binary_search(&a).is_err())
            .collect()
    }
}

fn polluted(cx: &Ctx, en: &Engine, s: &Slot, check_nom: bool) -> (bool, Vec<u32>) {
    let mut is_poll = false;
    let mut pnoms: Vec<u32> = Vec::new();
    for (&i, old) in s.m.saved_iter() {
        let cur = s.m.find(i);
        let newt = s.m.elems[cur as usize].ty;
        if newt == old.ty {
            continue;
        }
        let gained = cx.named_gain(en, old.ty, newt);
        if gained.is_empty() {
            continue;
        }
        if let Some(cs) = s.wit_of.get(&i) {
            for c in cs {
                let t = cx.target[c];
                if gained.iter().any(|&g| !en.sets.has(t, g)) {
                    is_poll = true;
                    if old.nom {
                        for &o in en.sets.get(old.ty).iter() {
                            if en.nf.is_nom[o as usize] {
                                pnoms.push(o);
                            }
                        }
                    }
                }
            }
        }
        if check_nom && old.nom {
            for &o in en.sets.get(old.ty).iter() {
                if let Some(&t) = cx.nom_target.get(&o) {
                    if gained.iter().any(|&g| !en.sets.has(t, g)) {
                        is_poll = true;
                        pnoms.push(o);
                    }
                }
            }
        }
    }
    pnoms.sort_unstable();
    pnoms.dedup();
    (is_poll, pnoms)
}

fn build_witness(
    cx: &Ctx,
    en: &mut Engine,
    m: &mut Model,
    a: Option<u32>,
    forbid: u32,
    target: u32,
    use_clean: bool,
) -> Result<Id, Fail> {
    let scan_cap = if forbid == 0 { 512 } else { 32768 };
    if m.elems.len() <= scan_cap {
        let fb_slice = en.sets.get(forbid);
        let tgt_slice = en.sets.get(target);
        let mut best: Option<(usize, Id)> = None;
        for y in m.canonical() {
            if !m.elems[y as usize].pending.is_empty() {
                continue;
            }
            let ty = m.elems[y as usize].ty;
            if let Some(c) = a {
                if !en.sets.has(ty, c) {
                    continue;
                }
            }
            if forbid != 0 && fb_slice.iter().any(|&b| en.sets.has(ty, b)) {
                continue;
            }
            if !tgt_slice.iter().all(|&s| !cx.rowclass[s as usize] || en.sets.has(ty, s)) {
                continue;
            }
            let dirty = en
                .sets
                .get(ty)
                .iter()
                .filter(|&&b| cx.rowclass[b as usize] && !en.sets.has(target, b))
                .count();
            if dirty == 0 {
                return Ok(y);
            }
            if forbid != 0 && best.map(|x| dirty < x.0).unwrap_or(true) {
                best = Some((dirty, y));
            }
        }
        if let Some((_, y)) = best {
            return Ok(y);
        }
    }
    let seed = match a {
        Some(c) => en.sets.intern(vec![c]),
        None => 0,
    };
    let cr = if use_clean {
        match en.close_clean(seed, forbid, target, true) {
            CloseRes::Ok(t) => CloseRes::Ok(t),
            _ => en.close(seed, forbid, target, true),
        }
    } else {
        en.close(seed, forbid, target, true)
    };
    let t = match cr {
        CloseRes::Ok(t) => t,
        CloseRes::Clash => return Err(Fail::new("seed type clash", vec![])),
        CloseRes::Budget => {
            let r = if en.mem_hit { "memory cap (8 GB)" } else { "closure budget" };
            return Err(Fail::new(r, vec![]));
        }
    };
    let nom = en.sets.get(t).iter().copied().find(|&o| en.nf.is_nom[o as usize]);
    if let (Some(_), Some(c)) = (nom, a) {
        // a class over nominals: an individual's element that already holds it
        let mut els: Vec<Id> = m.nom_elem.values().map(|&e| m.find(e)).collect();
        els.sort_unstable();
        els.dedup();
        let mut best: Option<(usize, Id)> = None;
        for e in els {
            let ts = en.sets.get(m.elems[e as usize].ty);
            if ts.binary_search(&c).is_err()
                || (forbid != 0 && en.sets.get(forbid).iter().any(|b| ts.binary_search(b).is_ok()))
            {
                continue;
            }
            let dirty = ts.iter().filter(|&&b| en.nf.named[b as usize] && !en.sets.has(target, b)).count();
            if best.map(|x| dirty < x.0).unwrap_or(true) {
                best = Some((dirty, e));
            }
        }
        if let Some((_, e)) = best {
            return Ok(e);
        }
    }
    let run_sat = |en: &mut Engine, m: &mut Model| -> Result<(), Fail> {
        let old_step = en.opt.step_budget;
        let old_node = en.opt.node_budget;
        en.opt.step_budget = old_step.min(50_000);
        en.opt.node_budget = old_node.min(m.elems.len() + 20_000);
        let res = en.saturate(m);
        en.opt.step_budget = old_step;
        en.opt.node_budget = old_node;
        res
    };
    let w = if let Some(o) = nom {
        let w = match m.nom_elem.get(&o) {
            Some(&w) => m.find(w),
            None => return Err(Fail::new("nominal without element", vec![])),
        };
        let ts = en.sets.get(t);
        m.em(w).pending.extend_from_slice(&ts);
        m.enqueue(w);
        run_sat(en, m)?;
        m.find(w)
    } else {
        let cand = m
            .typemap
            .get(&t)
            .and_then(|v| {
                v.iter().rev().copied().find(|&y| {
                    let e = &m.elems[y as usize];
                    e.alive && m.uf[y as usize] == y && e.ty == t && e.pending.is_empty()
                })
            })
            .or_else(|| {
                if seed == 0 {
                    return None;
                }
                let fb_slice = en.sets.get(forbid);
                let tgt_slice = en.sets.get(target);
                m.typemap.get(&(seed | crate::engine::SEED_KEY)).and_then(|v| {
                    v.iter().rev().copied().find(|&y| {
                        let e = &m.elems[y as usize];
                        if !e.alive || m.uf[y as usize] != y || !e.pending.is_empty() || !en.sets.subset(seed, e.ty) {
                            return false;
                        }
                        if forbid != 0 && fb_slice.iter().any(|&b| en.sets.has(e.ty, b)) {
                            return false;
                        }
                        !en.sets
                            .get(e.ty)
                            .iter()
                            .any(|&b| cx.rowclass[b as usize] && !en.sets.has(target, b))
                            && tgt_slice.iter().all(|&s| !cx.rowclass[s as usize] || en.sets.has(e.ty, s))
                    })
                })
            });
        match cand {
            Some(y) => y,
            None => {
                let w = en.new_elem_closed(m, seed, t, forbid, target, false);
                run_sat(en, m)?;
                m.find(w)
            }
        }
    };
    if forbid != 0 {
        let ft = en.sets.get(forbid);
        if ft.iter().any(|&b| en.sets.has(m.elems[w as usize].ty, b)) {
            return Err(Fail::new("a forbidden name is forced", vec![]));
        }
    }
    Ok(w)
}

fn try_witness(
    cx: &Ctx,
    en: &mut Engine,
    s: &mut Slot,
    a: Option<u32>,
    forbid: u32,
    check_nom: bool,
    retries: usize,
) -> WRes {
    let base_bad = en.bad.clone();
    let target = cx.target[&a];
    let mut why = String::from("no attempt");
    let mut local_forbid = forbid;
    let mut attempts = 0usize;
    let mut nom_retries = 0usize;
    let max_attempts = retries.max(1);
    while attempts < max_attempts {
        s.m.begin();
        match build_witness(cx, en, &mut s.m, a, local_forbid, target, attempts == 0) {
            Ok(w) => {
                let (is_poll, pnoms) = polluted(cx, en, s, check_nom);
                if is_poll {
                    s.m.rollback();
                    if !pnoms.is_empty() && nom_retries < 16 {
                        let fb2 = en.sets.union_vec(local_forbid, &pnoms);
                        if fb2 != local_forbid {
                            local_forbid = fb2;
                            nom_retries += 1;
                            continue;
                        }
                    }
                    restore_bad(en, &base_bad);
                    return WRes::Polluted;
                }
                let moved: Vec<(Id, Id)> = s
                    .m
                    .saved_iter()
                    .map(|(&i, _)| (i, s.m.find(i)))
                    .filter(|&(i, c)| c != i)
                    .collect();
                s.m.commit();
                for (i, c) in moved {
                    if let Some(v) = s.wit_of.remove(&i) {
                        s.wit_of.entry(c).or_default().extend(v);
                    }
                }
                s.m.em(w).pinned = true;
                s.wits.push((a, w));
                s.wit_of.entry(w).or_default().push(a);
                restore_bad(en, &base_bad);
                return WRes::Ok(w);
            }
            Err(e) => {
                s.m.rollback();
                if attempts == 0 || (e.reason != "seed type clash" && e.reason != "closure budget") {
                    why = e.reason.clone();
                }
                attempts += 1;
                if e.is_budget() {
                    break;
                }
                let mut new: Vec<u32> = e
                    .blame
                    .iter()
                    .copied()
                    .filter(|&t| {
                        t != 0
                            && !en.bad.contains(&t)
                            && !en.sets.get(t).iter().any(|&c| en.nf.is_nom[c as usize])
                    })
                    .collect();
                if new.is_empty() {
                    new = e.blame.iter().copied().filter(|&t| t != 0 && !en.bad.contains(&t)).collect();
                }
                if new.is_empty() {
                    if attempts == 1 {
                        continue;
                    }
                    break;
                }
                en.bad.extend(new);
                en.clear_memo();
            }
        }
    }
    restore_bad(en, &base_bad);
    if nom_retries > 0 {
        WRes::Polluted
    } else {
        WRes::Fail(why)
    }
}

fn restore_bad(en: &mut Engine, base: &crate::engine::FxSet<u32>) {
    if en.bad.len() != base.len() {
        en.bad = base.clone();
        en.clear_memo();
    }
}

#[derive(Clone, Copy)]
struct Place {
    model: usize,
    elem: Id,
}

#[allow(clippy::too_many_arguments)]
fn place(
    cx: &Ctx,
    en: &mut Engine,
    slots: &mut Vec<Slot>,
    base: &Model,
    a: Option<u32>,
    forbid: u32,
    cfg: &Config,
    polluted_count: &mut u64,
) -> Result<Place, String> {
    let mut k = 0;
    let mut had_polluted = false;
    loop {
        if k >= cfg.max_models {
            return Err("pollution in every model".into());
        }
        if k == slots.len() {
            slots.push(Slot { m: base.clone_base(), wits: Vec::new(), wit_of: FxMap::default() });
        }
        match try_witness(cx, en, &mut slots[k], a, forbid, k == 0, cfg.retries) {
            WRes::Ok(w) => return Ok(Place { model: k, elem: w }),
            WRes::Polluted => {
                *polluted_count += 1;
                had_polluted = true;
                k += 1;
            }
            WRes::Fail(r) => {
                if k + 1 < slots.len()
                    || ((had_polluted || r == "clash when growing a type")
                        && !slots[k].wits.is_empty()
                        && k + 1 < cfg.max_models)
                {
                    k += 1;
                } else {
                    return Err(r);
                }
            }
        }
    }
}

pub type Hook<'h> = &'h mut dyn FnMut(&mut Engine, &[Slot], &[(u64, Option<String>)]);

pub fn produce(nf: &Nf, km: &Km, cfg: &Config, outdir: &str, hook: Option<Hook>) -> String {
    let t0 = Instant::now();
    let search_limit = if cfg.time_limit > 30.0 { cfg.time_limit - 15.0 } else { cfg.time_limit * 0.9 };
    let deadline = t0 + std::time::Duration::from_secs_f64(search_limit);
    // a divergence (an infinite or very large model) should fail fast
    let node_budget = 100_000 + 40 * (nf.n + nf.noms.len());
    let opt = Opts { loops: cfg.loops, deadline: Some(deadline), node_budget, ..Opts::default() };
    let mut en = Engine::new(nf, opt);
    if let Some(d) = cfg.data.as_ref().filter(|d| !d.is_empty()) {
        let v = crate::data::Values::new(d);
        // only a fully understood data part can declare a type data-unsatisfiable
        if v.complete() {
            en.set_data(d.clone(), v);
        }
    }
    let mut j = String::new();
    let mut disagree: Vec<String> = Vec::new();
    let mut notes: Vec<String> = Vec::new();

    // ---- signature and km rows in normal-form indices ----
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
    let ci = |iri: &str| nf.cidx.get(iri).copied().filter(|&c| nf.named[c as usize]);
    let mut top: Vec<u32> = km.top.iter().filter_map(|s| ci(s)).collect();
    if let Some(t) = thing_c {
        top.push(t);
    }
    top.sort_unstable();
    top.dedup();
    let unsat: Vec<u32> = km.unsat.iter().filter_map(|s| ci(s)).collect();
    let mut is_unsat = vec![false; n];
    for &u in &unsat {
        is_unsat[u as usize] = true;
    }
    let mut target: FxMap<Option<u32>, u32> = FxMap::default();
    let mut sup_of: FxMap<Option<u32>, Vec<u32>> = FxMap::default();
    let topset = en.sets.intern(top.clone());
    target.insert(None, topset);
    sup_of.insert(None, top.clone());
    for &a in &classes {
        let mut v: Vec<u32> = km
            .sup
            .get(nf.cname_of(a))
            .map(|s| s.iter().filter_map(|x| ci(x)).collect())
            .unwrap_or_default();
        v.push(a);
        v.extend_from_slice(&top);
        v.sort_unstable();
        v.dedup();
        sup_of.insert(Some(a), v.clone());
        let t = en.sets.intern(v);
        target.insert(Some(a), t);
    }
    // individuals, merged per SAME
    let mut inds: Vec<(String, u32)> = nf
        .nominal
        .iter()
        .filter(|(iri, _)| !iri.starts_with("urn:km:") && !iri.starts_with('#') && !iri.starts_with('%'))
        .cloned()
        .collect();
    inds.sort();
    let ind_c: HashMap<&str, u32> = nf.nominal.iter().map(|(i, c)| (i.as_str(), *c)).collect();
    let mut grp: FxMap<u32, u32> = FxMap::default();
    fn gfind(g: &FxMap<u32, u32>, mut x: u32) -> u32 {
        while let Some(&p) = g.get(&x) {
            if p == x {
                break;
            }
            x = p;
        }
        x
    }
    for &o in &nf.noms {
        grp.insert(o, o);
    }
    for (a, b) in &km.same {
        if let (Some(&x), Some(&y)) = (ind_c.get(a.as_str()), ind_c.get(b.as_str())) {
            let (rx, ry) = (gfind(&grp, x), gfind(&grp, y));
            if rx != ry {
                grp.insert(rx.max(ry), rx.min(ry));
            }
        }
    }
    for (body, head) in &nf.gci {
        if body.len() == 1 && head.len() == 1 {
            let (b, h) = (body[0], head[0]);
            if nf.is_nom[b as usize] && nf.is_nom[h as usize] {
                let (rx, ry) = (gfind(&grp, b), gfind(&grp, h));
                if rx != ry {
                    grp.insert(rx.max(ry), rx.min(ry));
                }
            }
        }
    }
    let mut ind_types: FxMap<u32, Vec<u32>> = FxMap::default();
    for (iri, c) in &inds {
        let mut v: Vec<u32> =
            km.types.get(iri).map(|s| s.iter().filter_map(|x| ci(x)).collect()).unwrap_or_default();
        v.extend_from_slice(&top);
        ind_types.entry(gfind(&grp, *c)).or_default().extend(v);
    }
    let mut nom_target: FxMap<u32, u32> = FxMap::default();
    let mut groups: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for &o in &nf.noms {
        groups.entry(gfind(&grp, o)).or_default().push(o);
    }
    let mut gtarget: FxMap<u32, u32> = FxMap::default();
    for (&g, _) in &groups {
        let mut v = ind_types.get(&g).cloned().unwrap_or_else(|| top.clone());
        v.sort_unstable();
        v.dedup();
        let t = en.sets.intern(v);
        gtarget.insert(g, t);
    }
    if !cfg.no_realize {
        for (iri, c) in &inds {
            let _ = iri;
            nom_target.insert(*c, gtarget[&gfind(&grp, *c)]);
        }
    }
    let cx = Ctx { nf, rowclass: rowclass.clone(), target: target.clone(), nom_target };

    // precompute which nominals cannot be coalesced before/after saturation
    let mut unsafe_nom = vec![false; n];
    let mut ref_nom = vec![false; n];
    for (body, head) in &nf.gci {
        if body.len() == 1
            && head.len() == 1
            && nf.is_nom[body[0] as usize]
            && nf.is_nom[head[0] as usize]
            && gfind(&grp, body[0]) == gfind(&grp, head[0])
        {
            continue;
        }
        if body.len() > 1 {
            for &a in body {
                if nf.is_nom[a as usize] {
                    ref_nom[a as usize] = true;
                }
            }
        }
        for &h in head {
            if nf.is_nom[h as usize] {
                ref_nom[h as usize] = true;
                unsafe_nom[h as usize] = true;
            }
        }
    }
    for &(_, _, b) in &nf.ex {
        if nf.is_nom[b as usize] {
            ref_nom[b as usize] = true;
        }
    }
    for &(_, k, _, b) in &nf.ge {
        if nf.is_nom[b as usize] {
            ref_nom[b as usize] = true;
            if k > 1 {
                unsafe_nom[b as usize] = true;
            }
        }
    }
    for &o in &nf.noms {
        if !nf.ex_by.get(o).is_empty()
            || !nf.ge_by.get(o).is_empty()
            || !nf.all_by.get(o).is_empty()
            || !nf.le_by.get(o).is_empty()
        {
            unsafe_nom[o as usize] = true;
        }
    }

    let mut in_data = vec![false; n];
    let mut in_dsome = vec![false; n];
    let mut in_dall = vec![false; n];
    let mut in_dcard = vec![false; n];
    if let Some((d, _)) = &en.data {
        for c in &d.dsome {
            if (c.0 as usize) < n {
                in_data[c.0 as usize] = true;
                in_dsome[c.0 as usize] = true;
            }
        }
        for c in &d.dall {
            if (c.0 as usize) < n {
                in_data[c.0 as usize] = true;
                in_dall[c.0 as usize] = true;
            }
        }
        for c in &d.datleast {
            if (c.0 as usize) < n {
                in_data[c.0 as usize] = true;
                in_dcard[c.0 as usize] = true;
            }
        }
        for c in &d.datmost {
            if (c.0 as usize) < n {
                in_data[c.0 as usize] = true;
                in_dcard[c.0 as usize] = true;
            }
        }
    }
    for &(_, _, _, c) in &nf.le {
        if (c as usize) < n {
            in_data[c as usize] = true;
            in_dcard[c as usize] = true;
        }
    }
    let mut pure_ex = vec![false; n];
    let mut pure_dall = vec![false; n];
    let mut pure_dsome = vec![false; n];
    for a in 0..n {
        if !nf.named[a]
            && !nf.is_nom[a]
            && nf.gci_by_body.get(a as u32).is_empty()
            && nf.all_by.get(a as u32).is_empty()
            && !nf.has_le[a]
            && nf.ge_by.get(a as u32).is_empty()
        {
            if !nf.ex_by.get(a as u32).is_empty() && !in_data[a] {
                pure_ex[a] = true;
            } else if nf.ex_by.get(a as u32).is_empty() && !in_dcard[a] {
                if in_dall[a] && !in_dsome[a] {
                    pure_dall[a] = true;
                } else if in_dsome[a] && !in_dall[a] {
                    pure_dsome[a] = true;
                }
            }
        }
    }
    let mut dall_gci: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (gi, (_, head)) in nf.gci.iter().enumerate() {
        for &h in head {
            if (h as usize) < n && pure_dall[h as usize] {
                dall_gci[h as usize].push(gi as u32);
            }
        }
    }

    let coalesce_post = |en: &mut Engine, m: &mut Model| {
        let trim_dall = |en: &mut Engine, all_c: &[u32]| -> u32 {
            let v: Vec<u32> = all_c
                .iter()
                .copied()
                .filter(|&a| {
                    !pure_dall[a as usize]
                        || !dall_gci[a as usize].iter().all(|&gi| {
                            en.nf.gci[gi as usize]
                                .1
                                .iter()
                                .any(|&h| h != a && all_c.binary_search(&h).is_ok())
                        })
                })
                .collect();
            en.sets.intern(v)
        };
        for strip_ex in [false, true] {
            if m.nom_elem.len() <= 1 {
                return;
            }
            let mut raw_buckets: HashMap<(u32, u32, u32, Vec<(Id, u32)>), Vec<Id>> = HashMap::new();
            for x in m.canonical() {
                if !m.elems[x as usize].nom {
                    continue;
                }
                let tx = m.elems[x as usize].ty;
                let ts = en.sets.get(tx);
                if ts.iter().any(|&a| en.nf.is_nom[a as usize] && unsafe_nom[a as usize]) {
                    continue;
                }
                let core_vec: Vec<u32> = ts
                    .iter()
                    .copied()
                    .filter(|&a| {
                        !en.nf.is_nom[a as usize]
                            && !(strip_ex && (pure_ex[a as usize] || pure_dall[a as usize] || pure_dsome[a as usize]))
                    })
                    .collect();
                let core_ty = en.sets.intern(core_vec);
                let mut edges_key: Vec<(Id, u32)> = Vec::new();
                let mut ok_edges = true;
                for &(z, l) in &m.elems[x as usize].edges {
                    let z = m.find(z);
                    if z == x {
                        ok_edges = false;
                        break;
                    }
                    let tz_id = m.elems[z as usize].ty;
                    let tz = en.sets.get(tz_id);
                    if tz.iter().any(|&a| !en.nf.ge_by.get(a).is_empty()) {
                        ok_edges = false;
                        break;
                    }
                    let fl = en.flip(l);
                    let f_tx = en.fwd(tx, l);
                    let f_core = en.fwd(core_ty, l);
                    let bk_z = en.fwd(tz_id, fl);
                    if f_tx != f_core || !en.sets.subset(bk_z, core_ty) {
                        ok_edges = false;
                        break;
                    }
                    let is_le_edge = strip_ex
                        && (ts.iter().any(|&a| {
                            en.nf.has_le[a as usize]
                                && en.nf.le_by.get(a).iter().any(|&(_, r_le, _)| en.labs.has(l, r_le))
                        }) || tz.iter().any(|&a| {
                            en.nf.has_le[a as usize]
                                && en.nf.le_by.get(a).iter().any(|&(_, r_le, _)| en.labs.has(fl, r_le))
                        }));
                    if !strip_ex || is_le_edge {
                        edges_key.push((z, l));
                    }
                }
                if !ok_edges {
                    continue;
                }
                edges_key.sort_unstable();
                edges_key.dedup();
                raw_buckets
                    .entry((m.elems[x as usize].target, m.elems[x as usize].forbid, core_ty, edges_key))
                    .or_default()
                    .push(x);
            }
            let mut buckets: Vec<Vec<Id>> = Vec::new();
            let mut group_of = vec![0usize; m.elems.len()];
            for grp in raw_buckets.values() {
                if grp.len() <= 1 {
                    continue;
                }
                if Instant::now() > deadline || en.mem_exceeded() {
                    return;
                }
                let base_idx = buckets.len() + 1;
                let mut subs: Vec<Vec<Id>> = Vec::new();
                let mut sub_concepts: Vec<Vec<u32>> = Vec::new();
                for &x in grp {
                    if Instant::now() > deadline || en.mem_exceeded() {
                        return;
                    }
                    let tx_s = en.sets.get(m.elems[x as usize].ty);
                    let has_ref_nom = tx_s.iter().any(|&a| en.nf.is_nom[a as usize] && ref_nom[a as usize]);
                    let has_dsome_x = strip_ex && tx_s.iter().any(|&a| in_dsome[a as usize]);
                    let mut placed = false;
                    'sub_loop: for (si, sub) in subs.iter_mut().enumerate() {
                        if (has_ref_nom || has_dsome_x) && sub.len() >= 128 {
                            continue 'sub_loop;
                        }
                        let gid = base_idx + si;
                        for &(z, _) in &m.elems[x as usize].edges {
                            let z = m.find(z);
                            if group_of[z as usize] == gid || sub.binary_search(&z).is_ok() {
                                continue 'sub_loop;
                            }
                        }
                        if has_ref_nom || has_dsome_x {
                            let mut comb = sub_concepts[si].clone();
                            let prev_len = comb.len();
                            comb.extend_from_slice(&tx_s);
                            comb.sort_unstable();
                            comb.dedup();
                            if has_ref_nom {
                                let t_cand = if strip_ex {
                                    trim_dall(en, &comb)
                                } else {
                                    en.sets.intern(comb.clone())
                                };
                                let gci_bad = tx_s.iter().any(|&a| {
                                    en.nf.is_nom[a as usize]
                                        && en.nf.gci_by_body.get(a).iter().any(|&gi| {
                                            let (bg, hg) = &en.nf.gci[gi as usize];
                                            bg.len() > 1
                                                && bg.iter().all(|&c| en.sets.has(t_cand, c))
                                                && !hg.iter().any(|&c| en.sets.has(t_cand, c))
                                        })
                                });
                                if gci_bad {
                                    continue 'sub_loop;
                                }
                            }
                            if has_dsome_x && comb.len() > prev_len {
                                let new_dsome = tx_s
                                    .iter()
                                    .any(|&a| in_dsome[a as usize] && sub_concepts[si].binary_search(&a).is_err());
                                if new_dsome && en.data.is_some() {
                                    let peer_bad = tx_s.iter().any(|&a| {
                                        in_dsome[a as usize]
                                            && sub_concepts[si]
                                                .iter()
                                                .any(|&b| !pure_dall[b as usize] && en.has_conflict_peer(a, b))
                                    });
                                    if peer_bad {
                                        continue 'sub_loop;
                                    }
                                    if tx_s.iter().any(|&a| in_dcard[a as usize]) {
                                        let t_cand = trim_dall(en, &comb);
                                        let ds: Vec<u32> = en
                                            .sets
                                            .get(t_cand)
                                            .iter()
                                            .copied()
                                            .filter(|&a| en.has_data[a as usize])
                                            .collect();
                                        if !en.has_data_star(ds) {
                                            continue 'sub_loop;
                                        }
                                    }
                                }
                            }
                            sub_concepts[si] = comb;
                        }
                        group_of[x as usize] = gid;
                        sub.push(x);
                        placed = true;
                        break;
                    }
                    if !placed {
                        let gid = base_idx + subs.len();
                        group_of[x as usize] = gid;
                        subs.push(vec![x]);
                        sub_concepts.push(tx_s.to_vec());
                    }
                }
                for sub in subs {
                    if sub.len() > 1 {
                        buckets.push(sub);
                    }
                }
            }
            if buckets.is_empty() {
                continue;
            }
            m.begin();
            let mut dead = vec![false; m.elems.len()];
            let mut rep: Vec<Id> = (0..m.elems.len() as Id).collect();
            for b in &buckets {
                let x0 = b[0];
                for &xi in &b[1..] {
                    dead[xi as usize] = true;
                    rep[xi as usize] = x0;
                }
            }
            for b in &buckets {
                let x0 = b[0];
                let mut all_concepts: Vec<u32> = Vec::new();
                let mut all_noms: Vec<u32> = Vec::new();
                let mut all_forced: Vec<u32> = Vec::new();
                let mut extra_edges: Vec<(Id, u32)> = Vec::new();
                for (idx, &xi) in b.iter().enumerate() {
                    let ts = en.sets.get(m.elems[xi as usize].ty);
                    all_concepts.extend_from_slice(&ts);
                    for &o in ts.iter() {
                        if en.nf.is_nom[o as usize] {
                            all_noms.push(o);
                        }
                    }
                    all_forced.extend_from_slice(&en.sets.get(m.elems[xi as usize].forced));
                    if idx > 0 {
                        for &(z, l) in &m.elems[xi as usize].edges {
                            let z2 = rep[m.find(z) as usize];
                            if z2 != x0 {
                                extra_edges.push((z2, l));
                            }
                        }
                    }
                }
                all_concepts.sort_unstable();
                all_concepts.dedup();
                all_noms.sort_unstable();
                all_noms.dedup();
                all_forced.extend_from_slice(&all_noms);
                all_forced.sort_unstable();
                all_forced.dedup();
                let t_merged = if strip_ex {
                    trim_dall(en, &all_concepts)
                } else {
                    en.sets.intern(all_concepts)
                };
                let f_merged = en.sets.intern(all_forced);
                {
                    let e0 = m.em(x0);
                    e0.ty = t_merged;
                    e0.forced = f_merged;
                }
                m.tm_push(t_merged, x0);
                for &xi in &b[1..] {
                    {
                        let ei = m.em(xi);
                        ei.alive = false;
                        ei.edges.clear();
                        ei.pending.clear();
                    }
                    m.set_uf(xi, x0);
                }
                for &o in &all_noms {
                    m.set_nom(o, x0);
                }
                for (z2, l) in extra_edges {
                    en.add_edge(m, x0, z2, l);
                }
            }
            let n_elems = m.elems.len();
            for z in 0..n_elems {
                if m.elems[z].alive
                    && m.elems[z].edges.iter().any(|&(w, _)| (w as usize) < dead.len() && dead[w as usize])
                {
                    let remapped: Vec<(Id, u32)> = m.elems[z]
                        .edges
                        .iter()
                        .filter_map(|&(w, l)| {
                            if (w as usize) < dead.len() && dead[w as usize] {
                                let w2 = rep[w as usize];
                                if w2 != z as Id {
                                    Some((w2, l))
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        })
                        .collect();
                    m.em(z as Id).edges.retain(|&(w, _)| (w as usize) >= dead.len() || !dead[w as usize]);
                    for (w2, l) in remapped {
                        en.add_edge(m, z as Id, w2, l);
                    }
                }
            }
            if check::verify(en, m).violations == 0 {
                m.commit();
            } else {
                m.rollback();
            }
        }
    };

    // ---- base: the individuals ----
    let mut base = Model::new();
    let mut base_ok = false;
    let mut base_why = String::new();
    for attempt in 0..(cfg.retries * 4).max(1) {
        if en.mem_exceeded() {
            base_why = "memory cap (8 GB)".into();
            break;
        }
        if Instant::now() > deadline {
            if base_why.is_empty() {
                base_why = "time budget".into();
            }
            break;
        }
        base.begin();
        let mut r: Result<(), Fail> = Ok(());
        let mut pre_buckets: FxMap<(u32, u32), Id> = FxMap::default();
        let mut pre_extra_noms: FxMap<Id, Vec<u32>> = FxMap::default();
        for (gi, (g, os)) in groups.iter().enumerate() {
            if gi & 255 == 0 && en.mem_exceeded() {
                r = Err(Fail::new("memory cap (8 GB)", vec![]));
                break;
            }
            if Instant::now() > deadline {
                r = Err(Fail::new("time budget", vec![]));
                break;
            }
            let seed = en.sets.intern(os.clone());
            let gt = gtarget[g];
            if attempt == 0 && groups.len() > 64 && os.iter().all(|&o| !unsafe_nom[o as usize] && !ref_nom[o as usize]) {
                let cr = if cfg.no_realize {
                    en.close(seed, 0, gt, true)
                } else {
                    en.close_clean(seed, 0, gt, true)
                };
                if let CloseRes::Ok(t) = cr {
                    let ts = en.sets.get(t);
                    if ts.iter().all(|&a| !en.nf.is_nom[a as usize] || os.binary_search(&a).is_ok()) {
                        let non_nom_vec: Vec<u32> = ts
                            .iter()
                            .copied()
                            .filter(|&a| !en.nf.is_nom[a as usize])
                            .collect();
                        let non_nom_ty = en.sets.intern(non_nom_vec);
                        if let Some(&y) = pre_buckets.get(&(gt, non_nom_ty)) {
                            pre_extra_noms.entry(y).or_default().extend_from_slice(os);
                            for &o in os {
                                base.set_nom(o, y);
                            }
                            continue;
                        } else {
                            let y = en.new_elem_closed(&mut base, seed, t, 0, gt, true);
                            if cfg.no_realize {
                                base.em(y).owner = y;
                            }
                            pre_buckets.insert((gt, non_nom_ty), y);
                            continue;
                        }
                    }
                }
            }
            if cfg.no_realize {
                match en.close(seed, 0, gt, true) {
                    CloseRes::Ok(t) => {
                        let y = en.new_elem_closed(&mut base, seed, t, 0, gt, true);
                        base.em(y).owner = y;
                    }
                    CloseRes::Clash => {
                        r = Err(Fail::new("clash in a seed type", vec![]));
                        break;
                    }
                    CloseRes::Budget => {
                        let msg = if en.mem_hit { "memory cap (8 GB)" } else { "closure budget" };
                        r = Err(Fail::new(msg, vec![]));
                        break;
                    }
                }
            } else if let Err(e) = en.new_elem(&mut base, seed, 0, gt, true) {
                r = Err(e);
                break;
            }
        }
        if r.is_ok() && !pre_extra_noms.is_empty() {
            for (y, mut extra) in pre_extra_noms {
                extra.sort_unstable();
                extra.dedup();
                let t_new = en.sets.union_vec(base.elems[y as usize].ty, &extra);
                let f_new = en.sets.union_vec(base.elems[y as usize].forced, &extra);
                let ey = base.em(y);
                ey.ty = t_new;
                ey.forced = f_new;
                base.tm_push(t_new, y);
            }
        }
        if r.is_ok() {
            r = en.saturate(&mut base);
        }
        match r {
            Ok(()) => {
                base.commit();
                base_ok = true;
                break;
            }
            Err(e) => {
                base.rollback();
                if attempt == 0 || (e.reason != "clash in a seed type" && e.reason != "closure budget") {
                    base_why = e.reason.clone();
                }
                if e.is_budget() {
                    break;
                }
                let mut new: Vec<u32> = e
                    .blame
                    .iter()
                    .copied()
                    .filter(|&t| {
                        t != 0
                            && !en.bad.contains(&t)
                            && !en.sets.get(t).iter().any(|&c| en.nf.is_nom[c as usize])
                    })
                    .collect();
                if new.is_empty() {
                    new = e.blame.iter().copied().filter(|&t| t != 0 && !en.bad.contains(&t)).collect();
                }
                if new.is_empty() && attempt > 0 {
                    break;
                }
                en.bad.extend(new);
                en.clear_memo();
            }
        }
    }
    if base_ok {
        coalesce_post(&mut en, &mut base);
    }
    for e in base.elems.iter_mut() {
        if e.nom {
            e.pinned = true;
        }
    }
    let base_secs = t0.elapsed().as_secs_f64();
    let mut slots: Vec<Slot> = Vec::new();
    let mut wit_ok: FxMap<Option<u32>, Vec<Place>> = FxMap::default();
    let mut wit_fail: BTreeMap<String, u64> = BTreeMap::new();
    let mut fail_of: FxMap<Option<u32>, String> = FxMap::default();
    let mut polluted_n = 0u64;
    let mut stopped: Option<String> = None;
    let mut split_witnesses = 0u64;
    let mut uncovered: Vec<(Option<u32>, u32, String)> = Vec::new();
    let mut unsat_checked = 0u64;
    if base_ok {
        slots.push(Slot { m: base.clone_base(), wits: Vec::new(), wit_of: FxMap::default() });
        // ---- general witnesses ----
        let mut order: Vec<Option<u32>> = vec![None];
        order.extend(classes.iter().filter(|&&c| !is_unsat[c as usize]).map(|&c| Some(c)));
        for (i, &a) in order.iter().enumerate() {
            if en.mem_exceeded() {
                stopped = Some(format!("memory cap (8 GB) after {} of {} witnesses", i, order.len()));
                break;
            }
            if Instant::now() > deadline {
                stopped = Some(format!("time budget after {} of {} witnesses", i, order.len()));
                break;
            }
            match place(&cx, &mut en, &mut slots, &base, a, 0, cfg, &mut polluted_n) {
                Ok(p) => wit_ok.entry(a).or_default().push(p),
                Err(r) => {
                    if en.mem_hit || r.contains("memory cap") {
                        stopped = Some(format!("memory cap (8 GB) after {} of {} witnesses", i, order.len()));
                        break;
                    }
                    *wit_fail.entry(r.clone()).or_default() += 1;
                    fail_of.insert(a, r);
                }
            }
        }
        // ---- split witnesses for dirty ones ----
        if stopped.is_none() {
            for &a in &order {
                if en.mem_exceeded() {
                    stopped = Some("memory cap (8 GB) in the split witnesses".into());
                    break;
                }
                if Instant::now() > deadline {
                    stopped = Some("time budget in the split witnesses".into());
                    break;
                }
                let p = match wit_ok.get(&a) {
                    Some(v) if !v.is_empty() => (v[0].model, v[0].elem),
                    _ => continue,
                };
                let w = slots[p.0].m.find(p.1);
                let t = target[&a];
                let d: Vec<u32> = en
                    .sets
                    .get(slots[p.0].m.elems[w as usize].ty)
                    .iter()
                    .copied()
                    .filter(|&b| rowclass[b as usize] && !en.sets.has(t, b))
                    .collect();
                if d.is_empty() {
                    continue;
                }
                let mut queue: Vec<Vec<u32>> = vec![d];
                let mut made = 0;
                while let Some(f) = queue.pop() {
                    if made >= cfg.split_cap || Instant::now() > deadline {
                        for b in f {
                            uncovered.push((a, b, "split cap".into()));
                        }
                        continue;
                    }
                    made += 1;
                    let fid = en.sets.intern(f.clone());
                    match place(&cx, &mut en, &mut slots, &base, a, fid, cfg, &mut polluted_n) {
                        Ok(p) => {
                            split_witnesses += 1;
                            wit_ok.entry(a).or_default().push(p);
                        }
                        Err(r) => {
                            if f.len() > 1 {
                                let h = f.len() / 2;
                                queue.push(f[h..].to_vec());
                                queue.push(f[..h].to_vec());
                            } else {
                                uncovered.push((a, f[0], r));
                            }
                        }
                    }
                }
            }
        }
        // ---- split base models for dirty individuals ----
        if stopped.is_none() && !inds.is_empty() && !cfg.no_realize {
            let slots_before = slots.len();
            let mut ever_dirty: crate::engine::FxSet<u32> = crate::engine::FxSet::default();
            for _round in 0..8 {
                if slots.len() >= cfg.max_models + 6 || Instant::now() > deadline {
                    break;
                }
                let mut rem_dirty: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
                for (&g, os) in &groups {
                    let o0 = os[0];
                    let gt = gtarget[&g];
                    let mut left: Option<Vec<u32>> = None;
                    for s in &slots {
                        if let Some(&e) = s.m.nom_elem.get(&o0) {
                            let e = s.m.find(e);
                            let ts = en.sets.get(s.m.elems[e as usize].ty);
                            let d: Vec<u32> = ts
                                .iter()
                                .copied()
                                .filter(|&b| rowclass[b as usize] && !en.sets.has(gt, b))
                                .collect();
                            left = Some(match left {
                                None => d,
                                Some(l) => l.into_iter().filter(|b| d.binary_search(b).is_ok()).collect(),
                            });
                        }
                    }
                    if let Some(d) = left {
                        if !d.is_empty() {
                            ever_dirty.insert(g);
                            rem_dirty.insert(g, d);
                        }
                    }
                }
                if rem_dirty.is_empty() {
                    break;
                }
                let mut skip_fb: crate::engine::FxSet<u32> = crate::engine::FxSet::default();
                let mut ind_m = Model::new();
                let mut sat_ok = false;
                for attempt in 0..32 {
                    if Instant::now() > deadline {
                        break;
                    }
                    ind_m = Model::new();
                    ind_m.begin();
                    let mut any_forbid = false;
                    let mut ok = true;
                    let mut elem_of_g: Vec<(u32, Id)> = Vec::new();
                    let mut pre_buckets: FxMap<(u32, u32), Id> = FxMap::default();
                    let mut pre_extra_noms: FxMap<Id, Vec<u32>> = FxMap::default();
                    for (&g, os) in &groups {
                        let seed = en.sets.intern(os.clone());
                        let gt = gtarget[&g];
                        let mut fb = 0u32;
                        if !skip_fb.contains(&g) {
                            if let Some(d) = rem_dirty.get(&g) {
                                let f_all = en.sets.intern(d.clone());
                                if matches!(en.close(seed, f_all, gt, true), CloseRes::Ok(_)) {
                                    fb = f_all;
                                    any_forbid = true;
                                } else if d.len() > 1 {
                                    let h = d.len() / 2;
                                    let f_h1 = en.sets.intern(d[..h].to_vec());
                                    let f_h2 = en.sets.intern(d[h..].to_vec());
                                    if matches!(en.close(seed, f_h1, gt, true), CloseRes::Ok(_)) {
                                        fb = f_h1;
                                        any_forbid = true;
                                    } else if matches!(en.close(seed, f_h2, gt, true), CloseRes::Ok(_)) {
                                        fb = f_h2;
                                        any_forbid = true;
                                    } else {
                                        for &b in d {
                                            let f1 = en.sets.intern(vec![b]);
                                            if matches!(en.close(seed, f1, gt, true), CloseRes::Ok(_)) {
                                                fb = f1;
                                                any_forbid = true;
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if fb == 0
                            && !ever_dirty.contains(&g)
                            && groups.len() > 64
                            && os.iter().all(|&o| !unsafe_nom[o as usize] && !ref_nom[o as usize])
                        {
                            if let CloseRes::Ok(t) = en.close_clean(seed, 0, gt, true) {
                                let ts = en.sets.get(t);
                                if ts.iter().all(|&a| !en.nf.is_nom[a as usize] || os.binary_search(&a).is_ok()) {
                                    let non_nom_vec: Vec<u32> =
                                        ts.iter().copied().filter(|&a| !en.nf.is_nom[a as usize]).collect();
                                    let non_nom_ty = en.sets.intern(non_nom_vec);
                                    if let Some(&y) = pre_buckets.get(&(gt, non_nom_ty)) {
                                        pre_extra_noms.entry(y).or_default().extend_from_slice(os);
                                        for &o in os {
                                            ind_m.set_nom(o, y);
                                        }
                                        continue;
                                    } else {
                                        let y = en.new_elem_closed(&mut ind_m, seed, t, 0, gt, true);
                                        pre_buckets.insert((gt, non_nom_ty), y);
                                        continue;
                                    }
                                }
                            }
                        }
                        let cr = if fb == 0 && ever_dirty.contains(&g) {
                            en.close(seed, 0, gt, true)
                        } else {
                            en.close_clean(seed, fb, gt, true)
                        };
                        match cr {
                            CloseRes::Ok(t) => {
                                let el = en.new_elem_closed(&mut ind_m, seed, t, fb, gt, true);
                                if fb != 0 {
                                    elem_of_g.push((g, el));
                                }
                            }
                            _ => {
                                if fb != 0 {
                                    if let CloseRes::Ok(t0) = en.close(seed, 0, gt, true) {
                                        en.new_elem_closed(&mut ind_m, seed, t0, 0, gt, true);
                                        skip_fb.insert(g);
                                    } else {
                                        ok = false;
                                        break;
                                    }
                                } else {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                    }
                    if !any_forbid || !ok {
                        break;
                    }
                    if !pre_extra_noms.is_empty() {
                        for (y, mut extra) in pre_extra_noms {
                            extra.sort_unstable();
                            extra.dedup();
                            let t_new = en.sets.union_vec(ind_m.elems[y as usize].ty, &extra);
                            let f_new = en.sets.union_vec(ind_m.elems[y as usize].forced, &extra);
                            let ey = ind_m.em(y);
                            ey.ty = t_new;
                            ey.forced = f_new;
                            ind_m.tm_push(t_new, y);
                        }
                    }
                    match en.saturate(&mut ind_m) {
                        Ok(()) => {
                            ind_m.commit();
                            sat_ok = true;
                            break;
                        }
                        Err(e) => {
                            if e.is_budget() {
                                break;
                            }
                            let new: Vec<u32> = e
                                .blame
                                .iter()
                                .copied()
                                .filter(|&t| {
                                    t != 0
                                        && !en.bad.contains(&t)
                                        && !en.sets.get(t).iter().any(|&a| en.nf.is_nom[a as usize])
                                })
                                .collect();
                            if !new.is_empty() {
                                en.bad.extend(new);
                                en.clear_memo();
                            } else {
                                let mut dropped_any = false;
                                if let Some(&t0) = e.blame.first() {
                                    for &(g, el) in &elem_of_g {
                                        let el = ind_m.find(el);
                                        if ind_m.elems[el as usize].ty == t0 && skip_fb.insert(g) {
                                            dropped_any = true;
                                        }
                                    }
                                }
                                if !dropped_any {
                                    for &(g, el) in &elem_of_g {
                                        let el = ind_m.find(el);
                                        let ty_el = ind_m.elems[el as usize].ty;
                                        if e.blame.contains(&ty_el) && skip_fb.insert(g) {
                                            dropped_any = true;
                                        }
                                    }
                                }
                                if !dropped_any && attempt > 0 {
                                    break;
                                }
                            }
                        }
                    }
                }
                if !sat_ok {
                    break;
                }
                coalesce_post(&mut en, &mut ind_m);
                for e in ind_m.elems.iter_mut() {
                    if e.nom {
                        e.pinned = true;
                    }
                }
                let mut progressed = false;
                for (&g, d_old) in &rem_dirty {
                    let o0 = groups[&g][0];
                    let gt = gtarget[&g];
                    if let Some(&e) = ind_m.nom_elem.get(&o0) {
                        let e = ind_m.find(e);
                        let ts = en.sets.get(ind_m.elems[e as usize].ty);
                        if d_old.iter().any(|b| ts.binary_search(b).is_err())
                            && en.sets.get(gt).iter().all(|b| !rowclass[*b as usize] || ts.binary_search(b).is_ok())
                        {
                            progressed = true;
                        }
                    }
                }
                if !progressed {
                    break;
                }
                let wits = match ind_m.canonical().next() {
                    Some(c0) => vec![(None, c0)],
                    None => Vec::new(),
                };
                slots.push(Slot { m: ind_m, wits, wit_of: FxMap::default() });
            }
            if slots.len() > slots_before && !uncovered.is_empty() {
                let old_unc = std::mem::take(&mut uncovered);
                for (a, b, r_old) in old_unc {
                    let fid = en.sets.intern(vec![b]);
                    let mut found = false;
                    for si in slots_before..slots.len() {
                        if let WRes::Ok(w) = try_witness(&cx, &mut en, &mut slots[si], a, fid, false, cfg.retries) {
                            split_witnesses += 1;
                            wit_ok.entry(a).or_default().push(Place { model: si, elem: w });
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        uncovered.push((a, b, r_old));
                    }
                }
            }
        }
        // ---- km UNSAT classes: does the producer find them satisfiable? ----
        for &u in unsat.iter().take(cfg.unsat_checks) {
            if Instant::now() > deadline {
                break;
            }
            unsat_checked += 1;
            let s = &mut slots[0];
            s.m.begin();
            let tgt = en.sets.intern(vec![u]);
            let r = build_witness(&cx, &mut en, &mut s.m, Some(u), 0, tgt, false);
            if let Ok(w) = r {
                let rep = check::verify(&mut en, &s.m);
                if rep.violations == 0 {
                    disagree.push(format!(
                        "km UNSAT {} but the producer's self-checked model has element {} in it",
                        nf.cname_of(u),
                        w
                    ));
                }
            }
            s.m.rollback();
        }
    }
    let build_secs = t0.elapsed().as_secs_f64();

    // ---- self-check, with a repair round ----
    let mut verified: Vec<(u64, Option<String>)> = Vec::new();
    for s in slots.iter_mut() {
        let mut rep = check::verify(&mut en, &s.m);
        for _ in 0..3 {
            if rep.violations == 0 {
                break;
            }
            let mut nom_holders: FxMap<u32, Vec<Id>> = FxMap::default();
            for x in s.m.canonical() {
                for &a in en.sets.get(s.m.elems[x as usize].ty).iter() {
                    if nf.is_nom[a as usize] {
                        nom_holders.entry(a).or_default().push(x);
                    }
                }
            }
            for xs in nom_holders.values() {
                if xs.len() > 1 {
                    let x0 = s.m.find(xs[0]);
                    for &xi in &xs[1..] {
                        let xi = s.m.find(xi);
                        if xi != x0 {
                            en.merge(&mut s.m, xi, x0);
                        }
                    }
                }
            }
            for &x in &rep.bad {
                let x = s.m.find(x);
                if s.m.elems[x as usize].alive {
                    s.m.enqueue(x);
                    let nb: Vec<Id> = s.m.elems[x as usize].edges.iter().map(|e| e.0).collect();
                    for y in nb {
                        let y = s.m.find(y);
                        if s.m.elems[y as usize].alive {
                            s.m.enqueue(y);
                        }
                    }
                }
            }
            let repair_end = (t0 + std::time::Duration::from_secs_f64(cfg.time_limit + 20.0))
                .min(Instant::now() + std::time::Duration::from_secs(15));
            if Instant::now() >= repair_end {
                break;
            }
            en.opt.deadline = Some(repair_end);
            if let Err(e) = en.saturate(&mut s.m) {
                notes.push(format!("repair failed: {}", e.reason));
                break;
            }
            rep = check::verify(&mut en, &s.m);
        }
        verified.push((rep.violations, rep.first.clone()));
    }
    let check_secs = t0.elapsed().as_secs_f64() - build_secs;

    // ---- rows (unchecked: from the producer's own models) ----
    let nclasses = classes.len() as u64;
    let ok_model = |k: usize| verified.get(k).map(|v| v.0 == 0).unwrap_or(false);
    let mut order_all: Vec<Option<u32>> = vec![None];
    order_all.extend(classes.iter().map(|&c| Some(c)));
    let mut rows_nonsub = 0u64;
    let mut rows_sat = 0u64;
    let mut cert_nonsub = 0u64;
    let mut cert_sat = 0u64;
    let (mut c_general, mut c_split, mut c_partial, mut c_none) = (0u64, 0u64, 0u64, 0u64);
    let mut sup_missing = 0u64;
    let mut uncovered_rows = 0u64;
    let mut uncovered_examples: Vec<String> = Vec::new();
    let mut compacted_wits: Vec<Vec<(Option<u32>, Id)>> = vec![Vec::new(); slots.len()];
    for &a in &order_all {
        if let Some(c) = a {
            if is_unsat[c as usize] {
                continue;
            }
        }
        rows_sat += 1;
        let sup = &sup_of[&a];
        let nonsub: u64 = nclasses - sup.iter().filter(|&&b| rowclass[b as usize]).count() as u64;
        rows_nonsub += nonsub;
        let mut raw_places: Vec<Place> = Vec::new();
        if let Some(v) = wit_ok.get(&a) {
            for p in v {
                if ok_model(p.model) {
                    let w = slots[p.model].m.find(p.elem);
                    if !raw_places.iter().any(|q| q.model == p.model && q.elem == w) {
                        raw_places.push(Place { model: p.model, elem: w });
                    }
                }
            }
        }
        if raw_places.is_empty() {
            c_none += 1;
            continue;
        }
        cert_sat += 1;
        // Compute dirty rowclasses and missing superclasses per candidate place
        let mut cand_info: Vec<(Place, Vec<u32>, usize)> = Vec::with_capacity(raw_places.len());
        for p in raw_places {
            let ts = en.sets.get(slots[p.model].m.elems[p.elem as usize].ty);
            let miss = sup.iter().filter(|&&b| rowclass[b as usize] && ts.binary_search(&b).is_err()).count();
            let d: Vec<u32> = ts
                .iter()
                .copied()
                .filter(|&b| rowclass[b as usize] && sup.binary_search(&b).is_err())
                .collect();
            cand_info.push((p, d, miss));
        }
        // Compact: if any place has 0 missing superclasses and 0 dirty rowclasses, keep only 1 (preferring model 0)
        let mut places: Vec<Place> = Vec::new();
        if let Some((best_p, _, _)) = cand_info
            .iter()
            .filter(|(_, d, miss)| *miss == 0 && d.is_empty())
            .min_by_key(|(p, _, _)| (p.model != 0, p.model, p.elem))
        {
            places.push(*best_p);
        } else if cand_info.len() == 1 {
            places.push(cand_info[0].0);
        } else {
            cand_info.sort_by_key(|(p, d, miss)| (*miss, d.len(), p.model != 0, p.model, p.elem));
            places.push(cand_info[0].0);
            let mut cur_d = cand_info[0].1.clone();
            let mut used = vec![false; cand_info.len()];
            used[0] = true;
            while !cur_d.is_empty() {
                let mut best_idx = None;
                let mut best_rem = 0usize;
                for (idx, (_, d, miss)) in cand_info.iter().enumerate() {
                    if used[idx] || *miss > 0 {
                        continue;
                    }
                    let rem = cur_d.iter().filter(|b| d.binary_search(b).is_err()).count();
                    if rem > best_rem {
                        best_rem = rem;
                        best_idx = Some(idx);
                    }
                }
                if let Some(idx) = best_idx {
                    used[idx] = true;
                    places.push(cand_info[idx].0);
                    let d = &cand_info[idx].1;
                    cur_d.retain(|b| d.binary_search(b).is_ok());
                } else {
                    break;
                }
            }
        }
        for p in &places {
            compacted_wits[p.model].push((a, p.elem));
        }
        // names left uncertified: in every witness
        let mut left: Option<Vec<u32>> = None;
        for p in &places {
            let w = slots[p.model].m.find(p.elem);
            let ts = en.sets.get(slots[p.model].m.elems[w as usize].ty);
            // km's superclasses must all be there
            for &b in sup.iter() {
                if rowclass[b as usize] && ts.binary_search(&b).is_err() {
                    sup_missing += 1;
                    if disagree.len() < 50 {
                        disagree.push(format!(
                            "witness of {} (model {}) lacks {}, which km lists as a superclass",
                            a.map(|c| nf.cname_of(c)).unwrap_or(THING),
                            p.model,
                            nf.cname_of(b)
                        ));
                    }
                }
            }
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
        let left = left.unwrap_or_default();
        cert_nonsub += nonsub - left.len() as u64;
        if left.is_empty() {
            if places.len() == 1 {
                c_general += 1;
            } else {
                c_split += 1;
            }
        } else {
            c_partial += 1;
            uncovered_rows += left.len() as u64;
            if uncovered_examples.len() < 20 {
                uncovered_examples.push(format!(
                    "{} not certified outside {}",
                    a.map(|c| nf.cname_of(c)).unwrap_or(THING),
                    nf.cname_of(left[0])
                ));
            }
        }
    }
    // individuals: intersect dirty classes across all verified models
    let mut rows_nontype = 0u64;
    let mut cert_nontype = 0u64;
    let mut type_missing = 0u64;
    let mut ind_dirty = 0u64;
    let mut nontype_sep_outside = 0u64;
    let mut model_needed_for_ind = vec![false; slots.len()];
    if !cfg.no_realize {
        for (iri, c) in &inds {
            let g = gfind(&grp, *c);
            let tgt = ind_types.get(&g).cloned().unwrap_or_default();
            let mut tg = tgt.clone();
            tg.sort_unstable();
            tg.dedup();
            let own: Vec<u32> = {
                let mut v: Vec<u32> =
                    km.types.get(iri).map(|s| s.iter().filter_map(|x| ci(x)).collect()).unwrap_or_default();
                v.extend_from_slice(&top);
                v.sort_unstable();
                v.dedup();
                v
            };
            let nontype = nclasses - own.iter().filter(|&&b| rowclass[b as usize]).count() as u64;
            rows_nontype += nontype;
            if !ok_model(0) {
                continue;
            }
            let mut left_ind: Option<Vec<u32>> = None;
            for (k, s) in slots.iter().enumerate() {
                if !ok_model(k) {
                    continue;
                }
                let e = match s.m.nom_elem.get(c) {
                    Some(&e) => s.m.find(e),
                    None => continue,
                };
                let ts = en.sets.get(s.m.elems[e as usize].ty);
                if k == 0 {
                    for &b in &own {
                        if rowclass[b as usize] && ts.binary_search(&b).is_err() {
                            type_missing += 1;
                            if disagree.len() < 80 {
                                disagree.push(format!(
                                    "individual {} lacks {} in model 0, which km lists as a type",
                                    iri,
                                    nf.cname_of(b)
                                ));
                            }
                        }
                    }
                }
                let d: Vec<u32> =
                    ts.iter().copied().filter(|&b| rowclass[b as usize] && own.binary_search(&b).is_err()).collect();
                left_ind = Some(match left_ind {
                    None => {
                        model_needed_for_ind[k] = true;
                        d
                    }
                    Some(l) => {
                        let prev_len = l.len();
                        let next_l: Vec<u32> = l.into_iter().filter(|b| d.binary_search(b).is_ok()).collect();
                        if next_l.len() < prev_len {
                            model_needed_for_ind[k] = true;
                        }
                        next_l
                    }
                });
            }
            let Some(left_ind) = left_ind else { continue };
            let d = left_ind.len() as u64;
            if d > 0 {
                ind_dirty += 1;
            }
            cert_nontype += nontype - d;
        }
    } else if ok_model(0) {
        for (_iri, c) in &inds {
            let mut in_all: Option<Vec<u32>> = None;
            for (k, s) in slots.iter().enumerate() {
                if !ok_model(k) {
                    continue;
                }
                let e = match s.m.nom_elem.get(c) {
                    Some(&e) => s.m.find(e),
                    None => continue,
                };
                let ts = en.sets.get(s.m.elems[e as usize].ty);
                let d: Vec<u32> = ts.iter().copied().filter(|&b| rowclass[b as usize]).collect();
                in_all = Some(match in_all {
                    None => d,
                    Some(l) => l.into_iter().filter(|b| d.binary_search(b).is_ok()).collect(),
                });
            }
            if let Some(in_all) = in_all {
                nontype_sep_outside += nclasses - (in_all.len() as u64);
            }
        }
    }
    for (k, s) in slots.iter_mut().enumerate() {
        let mut cw = std::mem::take(&mut compacted_wits[k]);
        if cw.is_empty() && (k == 0 || model_needed_for_ind[k]) {
            if let Some(c0) = s.m.canonical().next() {
                cw.push((None, c0));
            }
        }
        s.wits = cw;
    }

    if let Some(h) = hook {
        h(&mut en, &slots, &verified);
    }
    // ---- emit ----
    let dvals = if slots.is_empty() {
        None
    } else if let Some((_, v)) = &en.data {
        Some(v.clone())
    } else {
        cfg.data.as_ref().filter(|d| !d.is_empty()).map(crate::data::Values::new)
    };
    let (mut dstar_with, mut dstar_without) = (0usize, 0usize);
    let mut models_json = Vec::new();
    for (k, s) in slots.iter().enumerate() {
        if k > 0 && (!ok_model(k) || s.wits.is_empty() || s.m.canonical().next().is_none()) {
            continue;
        }
        let out_k = models_json.len();
        let mut roots: Vec<Id> = s.wits.iter().map(|w| w.1).collect();
        roots.extend(s.m.nom_elem.values().copied());
        if roots.is_empty() {
            roots.extend(s.m.canonical().take(1));
        }
        let keep = emit::reachable(&s.m, &roots);
        let mut written = None;
        if cfg.write {
            let hp = format!("{}/model{}.hint", outdir, out_k);
            let dc = dvals.as_ref().map(|v| (cfg.data.as_ref().unwrap(), v));
            match emit::write_hint_d(&en, &s.m, &keep, &hp, &format!("km-hints global model {}", out_k), dc) {
                Ok((w, dw, dwo)) => {
                    dstar_with += dw;
                    dstar_without += dwo;
                    let mut rows: Vec<(&str, String, u32)> = Vec::new();
                    // the H2 witness table: `witness CLASS W`; owl:Thing only when the
                    // translation requested it (it is then a listed concept)
                    for (a, e) in &s.wits {
                        let e = s.m.find(*e);
                        let iri = match a {
                            Some(c) => nf.cname_of(*c),
                            None if thing_c.is_some() => THING,
                            None => continue,
                        };
                        if let Some(&i) = w.index.get(&e) {
                            rows.push(("witness", iri.to_string(), i));
                        }
                    }
                    let _ = emit::write_table(&rows, &format!("{}/model{}.wit", outdir, out_k));
                    written = Some(w);
                }
                Err(e) => notes.push(format!("write failed: {}", e)),
            }
        }
        let alive = s.m.canonical().count();
        let (el, ed, te, by) = match &written {
            Some(w) => (w.elements, w.edges, w.type_entries, w.bytes),
            None => {
                let ed: usize = keep.iter().map(|&x| s.m.elems[x as usize].edges.len()).sum();
                (keep.len(), ed / 2, 0, 0)
            }
        };
        models_json.push(format!(
            "{{\"model\":{},\"elements\":{},\"alive\":{},\"edges\":{},\"type_entries\":{},\"bytes\":{},\"witnesses\":{},\"violations\":{},\"first_violation\":{}}}",
            out_k,
            el,
            alive,
            ed,
            te,
            by,
            s.wits.len(),
            verified[k].0,
            verified[k].1.as_deref().map(json_str).unwrap_or("null".into())
        ));
    }
    if cfg.write {
        let mut stale_k = models_json.len();
        while std::path::Path::new(&format!("{}/model{}.hint", outdir, stale_k)).exists() {
            let _ = std::fs::remove_file(format!("{}/model{}.hint", outdir, stale_k));
            let _ = std::fs::remove_file(format!("{}/model{}.wit", outdir, stale_k));
            stale_k += 1;
        }
    }
    let total = t0.elapsed().as_secs_f64();
    let st = &en.stats;
    let _ = write!(j, "{{\"nf\":{{\"concepts\":{},\"roles\":{},\"gci\":{},\"some\":{},\"all\":{},\"atleast\":{},\"atmost\":{},\"chain\":{},\"long_chains\":{},\"noms\":{},\"data_clauses\":{}}}",
        nf.n, nf.m, nf.gci.len(), nf.ex.len(), nf.all.len(), nf.ge.len(), nf.le.len(), nf.chains.len(), nf.long_chains, nf.noms.len(), nf.data_clauses);
    let _ = write!(j, ",\"classes\":{},\"individuals\":{},\"km_unsat\":{},\"km_consistent\":{},\"no_realize\":{}", nclasses, inds.len(), unsat.len(),
        match km.consistent { Some(true) => "true", Some(false) => "false", None => "null" }, cfg.no_realize);
    if cfg.no_realize {
        let _ = write!(j, ",\"nontype_separate\":{{\"individuals\":{},\"pairs\":{},\"outside\":{}}}",
            inds.len(), (inds.len() as u64) * nclasses, nontype_sep_outside);
    }
    let _ = write!(j, ",\"dstars\":{{\"with\":{},\"without\":{}}}", dstar_with, dstar_without);
    let _ = write!(j, ",\"base\":{{\"ok\":{},\"why\":{},\"secs\":{:.3}}}", base_ok, json_str(&base_why), base_secs);
    let _ = write!(j, ",\"models\":[{}]", models_json.join(","));
    let _ = write!(j, ",\"witness\":{{\"general\":{},\"split\":{},\"partial\":{},\"none\":{},\"split_witnesses\":{},\"polluted_moves\":{},\"fail\":{{{}}}}}",
        c_general, c_split, c_partial, c_none, split_witnesses, polluted_n,
        wit_fail.iter().map(|(k, v)| format!("{}:{}", json_str(k), v)).collect::<Vec<_>>().join(","));
    let fex: Vec<String> = fail_of
        .iter()
        .take(20)
        .map(|(a, r)| json_str(&format!("{}: {}", a.map(|c| nf.cname_of(c)).unwrap_or(THING), r)))
        .collect();
    let _ = write!(j, ",\"fail_examples\":[{}]", fex.join(","));
    let _ = write!(j, ",\"rows\":{{\"consistency\":1,\"sat\":{},\"nonsub\":{},\"nontype\":{}}}", rows_sat, rows_nonsub, rows_nontype);
    let _ = write!(j, ",\"unchecked\":{{\"consistency\":{},\"sat\":{},\"nonsub\":{},\"nontype\":{}}}",
        if ok_model(0) { 1 } else { 0 }, cert_sat, cert_nonsub, cert_nontype);
    let _ = write!(j, ",\"uncovered\":{{\"rows\":{},\"pairs_tried\":{},\"individuals_dirty\":{},\"examples\":[{}]}}",
        uncovered_rows, uncovered.len(), ind_dirty, uncovered_examples.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(","));
    let _ = write!(j, ",\"disagreements\":{{\"sup_missing\":{},\"type_missing\":{},\"unsat_checked\":{},\"list\":[{}]}}",
        sup_missing, type_missing, unsat_checked, disagree.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(","));
    let _ = write!(j, ",\"stats\":{{\"closures\":{},\"close_runs\":{},\"steps\":{},\"reused\":{},\"created\":{},\"merges\":{},\"folds\":{},\"reclose_scratch\":{},\"sets\":{},\"labels\":{}}}",
        st.closures, st.close_runs, st.steps, st.reused, st.created, st.merges, st.folds, st.reclose_scratch, en.sets.len(), en.labs.len());
    let _ = write!(j, ",\"stopped\":{},\"notes\":[{}],\"secs\":{{\"base\":{:.3},\"build\":{:.3},\"check\":{:.3},\"total\":{:.3}}},\"rss_mb\":{}}}",
        stopped.as_deref().map(json_str).unwrap_or("null".into()),
        notes.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(","),
        base_secs, build_secs, check_secs, total, peak_rss_mb());
    j
}
