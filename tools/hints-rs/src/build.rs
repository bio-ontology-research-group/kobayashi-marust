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

fn polluted(cx: &Ctx, en: &Engine, s: &Slot, check_nom: bool) -> bool {
    for (i, old) in s.m.changed() {
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
                    return true;
                }
            }
        }
        if check_nom && old.nom {
            for &o in en.sets.get(old.ty).iter() {
                if let Some(&t) = cx.nom_target.get(&o) {
                    if gained.iter().any(|&g| !en.sets.has(t, g)) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn build_witness(en: &mut Engine, m: &mut Model, a: Option<u32>, forbid: u32, target: u32) -> Result<Id, Fail> {
    let seed = match a {
        Some(c) => en.sets.intern(vec![c]),
        None => 0,
    };
    let t = match en.close(seed, forbid, target, true) {
        CloseRes::Ok(t) => t,
        CloseRes::Clash => return Err(Fail::new("seed type clash", vec![])),
        CloseRes::Budget => return Err(Fail::new("closure budget", vec![])),
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
            if ts.binary_search(&c).is_err() || (forbid != 0 && en.sets.get(forbid).iter().any(|b| ts.binary_search(b).is_ok())) {
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
    let w = if let Some(o) = nom {
        let w = match m.nom_elem.get(&o) {
            Some(&w) => m.find(w),
            None => return Err(Fail::new("nominal without element", vec![])),
        };
        let ts = en.sets.get(t);
        m.em(w).pending.extend_from_slice(&ts);
        m.enqueue(w);
        en.saturate(m)?;
        m.find(w)
    } else {
        let cand = m.typemap.get(&t).and_then(|v| {
            v.iter().rev().copied().find(|&y| {
                let e = &m.elems[y as usize];
                e.alive && m.uf[y as usize] == y && e.ty == t
            })
        });
        match cand {
            Some(y) => y,
            None => {
                let w = en.new_elem(m, seed, forbid, target, false)?;
                en.saturate(m)?;
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
    for _ in 0..retries.max(1) {
        s.m.begin();
        match build_witness(en, &mut s.m, a, forbid, target) {
            Ok(w) => {
                if polluted(cx, en, s, check_nom) {
                    s.m.rollback();
                    restore_bad(en, &base_bad);
                    return WRes::Polluted;
                }
                let changed = s.m.changed();
                s.m.commit();
                for (i, _) in changed {
                    let c = s.m.find(i);
                    if c != i {
                        if let Some(v) = s.wit_of.remove(&i) {
                            s.wit_of.entry(c).or_default().extend(v);
                        }
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
                why = e.reason.clone();
                if e.is_budget() {
                    break;
                }
                let new: Vec<u32> = e.blame.iter().copied().filter(|&t| t != 0 && !en.bad.contains(&t)).collect();
                if new.is_empty() {
                    break;
                }
                en.bad.extend(new);
                en.clear_memo();
            }
        }
    }
    restore_bad(en, &base_bad);
    WRes::Fail(why)
}

fn restore_bad(en: &mut Engine, base: &crate::engine::FxSet<u32>) {
    if en.bad.len() != base.len() {
        en.bad = base.clone();
        en.clear_memo();
    }
}

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
                k += 1;
            }
            WRes::Fail(r) => return Err(r),
        }
    }
}

pub type Hook<'h> = &'h mut dyn FnMut(&mut Engine, &[Slot], &[(u64, Option<String>)]);

pub fn produce(nf: &Nf, km: &Km, cfg: &Config, outdir: &str, hook: Option<Hook>) -> String {
    let t0 = Instant::now();
    let deadline = t0 + std::time::Duration::from_secs_f64(cfg.time_limit);
    // a divergence (an infinite or very large model) should fail fast
    let node_budget = 100_000 + 40 * (nf.n + nf.noms.len());
    let opt = Opts { loops: cfg.loops, deadline: Some(deadline), node_budget, ..Opts::default() };
    let mut en = Engine::new(nf, opt);
    if let Some(d) = cfg.data.as_ref().filter(|d| !d.is_empty()) {
        let v = crate::data::Values::new(d);
        // only a fully understood data part can declare a type data-unsatisfiable
        if v.complete() {
            en.data = Some((d.clone(), v));
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
        .filter(|(iri, _)| !iri.starts_with("urn:km:") && !iri.starts_with('#'))
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
    for (iri, c) in &inds {
        let _ = iri;
        nom_target.insert(*c, gtarget[&gfind(&grp, *c)]);
    }
    let cx = Ctx { nf, rowclass: rowclass.clone(), target: target.clone(), nom_target };

    // ---- base: the individuals ----
    let mut base = Model::new();
    let mut base_ok = false;
    let mut base_why = String::new();
    for _ in 0..(cfg.retries * 4).max(1) {
        base.begin();
        let mut r: Result<(), Fail> = Ok(());
        for (g, os) in &groups {
            let seed = en.sets.intern(os.clone());
            if let Err(e) = en.new_elem(&mut base, seed, 0, gtarget[g], true) {
                r = Err(e);
                break;
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
                base_why = e.reason.clone();
                if e.is_budget() {
                    break;
                }
                let new: Vec<u32> = e.blame.iter().copied().filter(|&t| t != 0 && !en.bad.contains(&t)).collect();
                if new.is_empty() {
                    break;
                }
                en.bad.extend(new);
                en.clear_memo();
            }
        }
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
            if Instant::now() > deadline {
                stopped = Some(format!("time budget after {} of {} witnesses", i, order.len()));
                break;
            }
            match place(&cx, &mut en, &mut slots, &base, a, 0, cfg, &mut polluted_n) {
                Ok(p) => wit_ok.entry(a).or_default().push(p),
                Err(r) => {
                    *wit_fail.entry(r.clone()).or_default() += 1;
                    fail_of.insert(a, r);
                }
            }
        }
        // ---- split witnesses for dirty ones ----
        if stopped.is_none() {
            for &a in &order {
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
        // ---- km UNSAT classes: does the producer find them satisfiable? ----
        for &u in unsat.iter().take(cfg.unsat_checks) {
            if Instant::now() > deadline {
                break;
            }
            unsat_checked += 1;
            let s = &mut slots[0];
            s.m.begin();
            let tgt = en.sets.intern(vec![u]);
            let r = build_witness(&mut en, &mut s.m, Some(u), 0, tgt);
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
            for &x in &rep.bad {
                s.m.enqueue(x);
                let nb: Vec<Id> = s.m.elems[x as usize].edges.iter().map(|e| e.0).collect();
                for y in nb {
                    s.m.enqueue(y);
                }
            }
            en.opt.deadline = Some(Instant::now() + std::time::Duration::from_secs(60));
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
        let places: Vec<&Place> =
            wit_ok.get(&a).map(|v| v.iter().filter(|p| ok_model(p.model)).collect()).unwrap_or_default();
        if places.is_empty() {
            c_none += 1;
            continue;
        }
        cert_sat += 1;
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
    // individuals: model 0 only
    let mut rows_nontype = 0u64;
    let mut cert_nontype = 0u64;
    let mut type_missing = 0u64;
    let mut ind_dirty = 0u64;
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
        let s = &slots[0];
        let e = match s.m.nom_elem.get(c) {
            Some(&e) => s.m.find(e),
            None => continue,
        };
        let ts = en.sets.get(s.m.elems[e as usize].ty);
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
        let d = ts.iter().filter(|&&b| rowclass[b as usize] && own.binary_search(&b).is_err()).count() as u64;
        if d > 0 {
            ind_dirty += 1;
        }
        cert_nontype += nontype - d;
    }

    if let Some(h) = hook {
        h(&mut en, &slots, &verified);
    }
    // ---- emit ----
    let dvals = cfg.data.as_ref().filter(|d| !d.is_empty()).map(crate::data::Values::new);
    let (mut dstar_with, mut dstar_without) = (0usize, 0usize);
    let mut models_json = Vec::new();
    for (k, s) in slots.iter().enumerate() {
        let mut roots: Vec<Id> = s.wits.iter().map(|w| w.1).collect();
        roots.extend(s.m.nom_elem.values().copied());
        if roots.is_empty() {
            roots.extend(s.m.canonical().take(1));
        }
        let keep = emit::reachable(&s.m, &roots);
        let mut written = None;
        if cfg.write {
            let hp = format!("{}/model{}.hint", outdir, k);
            let dc = dvals.as_ref().map(|v| (cfg.data.as_ref().unwrap(), v));
            match emit::write_hint_d(&en, &s.m, &keep, &hp, &format!("km-hints global model {}", k), dc) {
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
                    let _ = emit::write_table(&rows, &format!("{}/model{}.wit", outdir, k));
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
            k,
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
    let total = t0.elapsed().as_secs_f64();
    let st = &en.stats;
    let _ = write!(j, "{{\"nf\":{{\"concepts\":{},\"roles\":{},\"gci\":{},\"some\":{},\"all\":{},\"atleast\":{},\"atmost\":{},\"chain\":{},\"long_chains\":{},\"noms\":{},\"data_clauses\":{}}}",
        nf.n, nf.m, nf.gci.len(), nf.ex.len(), nf.all.len(), nf.ge.len(), nf.le.len(), nf.chains.len(), nf.long_chains, nf.noms.len(), nf.data_clauses);
    let _ = write!(j, ",\"classes\":{},\"individuals\":{},\"km_unsat\":{},\"km_consistent\":{}", nclasses, inds.len(), unsat.len(),
        match km.consistent { Some(true) => "true", Some(false) => "false", None => "null" });
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
