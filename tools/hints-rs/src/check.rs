//! Self-check of a model against the normal form: every clause at every
//! element, the edge symmetry, up-closed labels, and one element per
//! nominal name. Untrusted, for debugging and speed: the proved checker
//! decides. Written independently of the construction in `engine.rs`
//! (it reads only the elements' final types and edges).

use crate::engine::{Engine, Id, Model};
use std::collections::HashMap;

pub struct Report {
    pub violations: u64,
    pub first: Option<String>,
    pub bad: Vec<Id>,
}

pub fn verify(en: &mut Engine, m: &Model) -> Report {
    let nf = en.nf;
    let mut rep = Report { violations: 0, first: None, bad: Vec::new() };
    let note = |rep: &mut Report, x: Id, msg: String| {
        rep.violations += 1;
        if rep.first.is_none() {
            rep.first = Some(format!("element {}: {}", x, msg));
        }
        if rep.bad.last() != Some(&x) {
            rep.bad.push(x);
        }
    };
    let mut nom_at: HashMap<u32, Vec<Id>> = HashMap::new();
    let ids: Vec<Id> = m.canonical().collect();
    let mut edge_map: crate::engine::FxMap<(Id, Id), u32> = crate::engine::FxMap::default();
    for &x in &ids {
        for &(y, l) in &m.elems[x as usize].edges {
            edge_map.insert((x, y), l);
        }
    }
    let mut ok_labs: crate::engine::FxSet<(u32, Option<u32>, bool)> = crate::engine::FxSet::default();
    let has_all = !nf.all.is_empty();
    let has_ge = !nf.ge.is_empty();
    let has_le = !nf.le.is_empty();
    for &x in &ids {
        let e = &m.elems[x as usize];
        let ts = en.sets.get(e.ty);
        let has = |a: u32| ts.binary_search(&a).is_ok();
        if !e.pending.is_empty() {
            note(&mut rep, x, "pending names left".into());
        }
        // gcis
        for &g in &nf.gci_empty {
            let h = &nf.gci[g as usize].1;
            if !h.iter().any(|&b| has(b)) {
                note(&mut rep, x, format!("gci {} (empty body) not met", g));
            }
        }
        for &a in ts.iter() {
            if nf.is_nom[a as usize] {
                nom_at.entry(a).or_default().push(x);
            }
            for &g in nf.gci_by_body.get(a) {
                let (b, h) = &nf.gci[g as usize];
                if b[0] != a {
                    continue;
                }
                if b.iter().all(|&c| has(c)) && !h.iter().any(|&c| has(c)) {
                    note(&mut rep, x, format!("gci {} {:?} -> {:?} not met", g, b, h));
                }
            }
        }
        // edges
        let mut nbrs: Vec<(Id, std::rc::Rc<[u32]>)> = Vec::with_capacity(e.edges.len());
        for &(y, l) in &e.edges {
            if !m.elems[y as usize].alive || m.uf[y as usize] != y {
                note(&mut rep, x, format!("edge to a dead element {}", y));
                continue;
            }
            let ls = en.labs.get(l);
            if ls.is_empty() {
                continue;
            }
            let back = edge_map.get(&(y, x)).copied();
            let lkey = (l, back, y == x);
            if !ok_labs.contains(&lkey) {
                let mut lab_ok = true;
                for &r in ls.iter() {
                    for &s in &nf.up[r as usize] {
                        if ls.binary_search(&s).is_err() {
                            note(&mut rep, x, format!("label to {} not up-closed", y));
                            lab_ok = false;
                        }
                    }
                }
                let want: Vec<u32> = {
                    let mut v: Vec<u32> = ls.iter().map(|r| r ^ 1).collect();
                    v.sort_unstable();
                    v
                };
                match back {
                    Some(bl) if y != x => {
                        if *en.labs.get(bl) != *want.as_slice() {
                            note(&mut rep, x, format!("edge to {} not symmetric", y));
                            lab_ok = false;
                        }
                    }
                    None => {
                        note(&mut rep, x, format!("edge to {} has no reverse", y));
                        lab_ok = false;
                    }
                    _ => {
                        if *ls != *want.as_slice() {
                            note(&mut rep, x, "loop label not closed under inverse".into());
                            lab_ok = false;
                        }
                    }
                }
                if lab_ok {
                    ok_labs.insert(lkey);
                }
            }
            if has_all {
                let tys = en.sets.get(m.elems[y as usize].ty);
                for &a in ts.iter() {
                    for &(s, c) in nf.all_by.get(a) {
                        if ls.binary_search(&s).is_ok() && tys.binary_search(&c).is_err() {
                            note(&mut rep, x, format!("universal {} {} {} fails at {}", a, s, c, y));
                        }
                    }
                }
            }
            nbrs.push((y, ls));
        }
        let has_nbr = |r: u32, b: u32| -> bool {
            nbrs.iter()
                .any(|(y, ls)| ls.binary_search(&r).is_ok() && en.sets.has(m.elems[*y as usize].ty, b))
        };
        let count = |r: u32, b: u32| -> usize {
            let mut c = 0;
            for (y, ls) in &nbrs {
                if ls.binary_search(&r).is_ok() && en.sets.has(m.elems[*y as usize].ty, b) {
                    c += 1;
                }
            }
            c
        };
        if nbrs.len() > 16 {
            let mut need_by_r: crate::engine::FxMap<u32, crate::engine::FxSet<u32>> =
                crate::engine::FxMap::default();
            for &a in ts.iter() {
                for &(r, b) in nf.ex_by.get(a) {
                    need_by_r.entry(r).or_default().insert(b);
                }
            }
            if !need_by_r.is_empty() {
                for (y, ls) in &nbrs {
                    if need_by_r.is_empty() {
                        break;
                    }
                    let ty = m.elems[*y as usize].ty;
                    let tys = en.sets.get(ty);
                    for &r in ls.iter() {
                        let mut empty = false;
                        if let Some(bs) = need_by_r.get_mut(&r) {
                            if bs.len() > tys.len() {
                                for &c in tys.iter() {
                                    bs.remove(&c);
                                }
                            } else {
                                bs.retain(|b| tys.binary_search(b).is_err());
                            }
                            empty = bs.is_empty();
                        }
                        if empty {
                            need_by_r.remove(&r);
                        }
                    }
                }
                if !need_by_r.is_empty() {
                    for &a in ts.iter() {
                        for &(r, b) in nf.ex_by.get(a) {
                            if need_by_r.get(&r).map(|bs| bs.contains(&b)).unwrap_or(false) {
                                note(&mut rep, x, format!("existential {} {} {} unmet", a, r, b));
                            }
                        }
                    }
                }
            }
            if has_ge || has_le {
                for &a in ts.iter() {
                    for &(k, r, b) in nf.ge_by.get(a) {
                        if count(r, b) < k as usize {
                            note(&mut rep, x, format!("at-least {} {} {} {} unmet", a, k, r, b));
                        }
                    }
                    for &(k, r, b) in nf.le_by.get(a) {
                        let c = count(r, b);
                        if c > k as usize {
                            note(&mut rep, x, format!("at-most {} {} {} {} exceeded ({})", a, k, r, b, c));
                        }
                    }
                }
            }
        } else {
            for &a in ts.iter() {
                for &(r, b) in nf.ex_by.get(a) {
                    if !has_nbr(r, b) {
                        note(&mut rep, x, format!("existential {} {} {} unmet", a, r, b));
                    }
                }
                if has_ge {
                    for &(k, r, b) in nf.ge_by.get(a) {
                        if count(r, b) < k as usize {
                            note(&mut rep, x, format!("at-least {} {} {} {} unmet", a, k, r, b));
                        }
                    }
                }
                if has_le {
                    for &(k, r, b) in nf.le_by.get(a) {
                        let c = count(r, b);
                        if c > k as usize {
                            note(&mut rep, x, format!("at-most {} {} {} {} exceeded ({})", a, k, r, b, c));
                        }
                    }
                }
            }
        }
    }
    for &o in &nf.noms {
        let n = nom_at.get(&o).map(|v| v.len()).unwrap_or(0);
        if n != 1 {
            rep.violations += 1;
            if rep.first.is_none() {
                rep.first = Some(format!("nominal {} at {} elements", o, n));
            }
        }
    }
    rep
}
