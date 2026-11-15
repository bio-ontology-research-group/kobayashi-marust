//! Moves a global model to the normal form of a row's extended ontology,
//! so today's per-row checker (`--row ROW --hint H`) can judge it.
//!
//! The row's normal form is the base normal form under a renaming of the
//! indices plus the row's own clauses (checked here: every renamed base
//! clause must occur in the row's clauses). Listed names map by IRI, the
//! unlisted ones in index order. Every element is re-closed under the row's
//! clauses; for a `nonsubs A ...` row the fresh nominal of the row goes to
//! A's witness, and the guards of the row then clash if the witness is in
//! one of the listed classes.

use crate::build::{self, Config, Slot};
use crate::check;
use crate::emit;
use crate::engine::{Elem, Engine, Id, Model, Opts, NONE};
use crate::km::{Km, THING};
use crate::nf::Nf;
use std::collections::HashSet;

/// `urn:km:` names carry a run of `#` whose length is a fresh prefix chosen
/// against the other IRIs of the ontology, plus an offset that tells the
/// names apart; a row's extra IRIs lengthen the prefix. Key: the text
/// before the run, the run length minus the shortest run of that kind, and
/// the rest.
fn norm_all(names: &[Option<String>]) -> Vec<Option<String>> {
    fn split(s: &str) -> Option<(String, usize, String)> {
        if !s.starts_with("urn:km:") {
            return None;
        }
        let i = s.find('#')?;
        let rest = &s[i..];
        let k = rest.chars().take_while(|&c| c == '#').count();
        Some((s[..i].to_string(), k, rest[k..].to_string()))
    }
    let mut min: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    for nm in names.iter().flatten() {
        if let Some((p, k, _)) = split(nm) {
            let e = min.entry(p).or_insert(k);
            if k < *e {
                *e = k;
            }
        }
    }
    names
        .iter()
        .map(|nm| {
            nm.as_ref().map(|s| match split(s) {
                Some((p, k, r)) => format!("{}#{}#{}", p, k - min[&p], r),
                None => s.clone(),
            })
        })
        .collect()
}

fn name_map(base: &[Option<String>], _row_idx: &std::collections::HashMap<String, u32>, row: &[Option<String>]) -> Result<Vec<u32>, String> {
    let base = norm_all(base);
    let row = norm_all(row);
    let mut row_idx: std::collections::HashMap<String, u32> = std::collections::HashMap::new();
    for (i, nm) in row.iter().enumerate() {
        if let Some(s) = nm {
            if row_idx.insert(s.clone(), i as u32).is_some() {
                return Err(format!("two row names normalise to {}", s));
            }
        }
    }
    let row_idx = &row_idx;
    let mut out = vec![NONE; base.len()];
    let row_unlisted: Vec<u32> = (0..row.len() as u32).filter(|&i| row[i as usize].is_none()).collect();
    let mut k = 0;
    for (i, nm) in base.iter().enumerate() {
        match nm {
            Some(s) => match row_idx.get(s) {
                Some(&j) => out[i] = j,
                None => return Err(format!("base name {} not in the row's index", s)),
            },
            None => {
                if k >= row_unlisted.len() {
                    return Err("the row has fewer unlisted names than the base".into());
                }
                out[i] = row_unlisted[k];
                k += 1;
            }
        }
    }
    Ok(out)
}

#[derive(Hash, PartialEq, Eq)]
enum Cl {
    G(Vec<u32>, Vec<u32>),
    E(u32, u32, u32),
    A(u32, u32, u32),
    Ge(u32, u32, u32, u32),
    Le(u32, u32, u32, u32),
    C(Vec<u32>, u32),
}

fn clauses(nf: &Nf, c: &dyn Fn(u32) -> u32, r: &dyn Fn(u32) -> u32) -> Vec<Cl> {
    let sv = |v: &[u32], f: &dyn Fn(u32) -> u32| {
        let mut x: Vec<u32> = v.iter().map(|&a| f(a)).collect();
        x.sort_unstable();
        x.dedup();
        x
    };
    let mut out = Vec::new();
    for (b, h) in &nf.gci {
        out.push(Cl::G(sv(b, c), sv(h, c)));
    }
    for &(a, s, b) in &nf.ex {
        out.push(Cl::E(c(a), r(s), c(b)));
    }
    for &(a, s, b) in &nf.all {
        out.push(Cl::A(c(a), r(s), c(b)));
    }
    for &(a, k, s, b) in &nf.ge {
        out.push(Cl::Ge(c(a), k, r(s), c(b)));
    }
    for &(a, k, s, b) in &nf.le {
        out.push(Cl::Le(c(a), k, r(s), c(b)));
    }
    for (body, s) in &nf.chains {
        out.push(Cl::C(body.iter().map(|&x| r(x)).collect(), r(*s)));
    }
    out
}

pub fn row_hint(
    nf: &Nf,
    rnf: &Nf,
    km: &Km,
    cfg: &Config,
    class: Option<&str>,
    individual: Option<&str>,
    out: &str,
) -> Result<String, String> {
    let cmap = name_map(&nf.cname, &rnf.cidx, &rnf.cname)?;
    let rmap = name_map(&nf.rname, &rnf.ridx, &rnf.rname)?;
    let c = |a: u32| cmap[a as usize];
    let r = |x: u32| 2 * rmap[(x / 2) as usize] + (x & 1);
    let rows: HashSet<Cl> = clauses(rnf, &|a| a, &|x| x).into_iter().collect();
    let mapped = clauses(nf, &c, &r);
    let missing = mapped.iter().filter(|x| !rows.contains(x)).count();
    if missing > 0 {
        return Err(format!("{} renamed base clauses are not in the row's clauses", missing));
    }
    let nu = rnf.nominal.iter().find(|(i, _)| i.starts_with('#')).map(|x| x.1);
    let want_class: Option<Option<u32>> = match class {
        Some(THING) => Some(None),
        Some(s) => Some(Some(*nf.cidx.get(s).ok_or("class not in the index")?)),
        None => None,
    };
    let want_ind: Option<u32> = match individual {
        Some(s) => Some(nf.nominal.iter().find(|x| x.0 == s).ok_or("individual not in the index")?.1),
        None => None,
    };
    let mut result: Result<String, String> = Err("no witness for the class".into());
    let mut hook = |en: &mut Engine, slots: &[Slot], verified: &[(u64, Option<String>)]| {
        // the slot and element to carry the row's fresh nominal
        let mut pick: Option<(usize, Id)> = None;
        if let Some(a) = want_class {
            for (k, s) in slots.iter().enumerate() {
                if verified[k].0 != 0 {
                    continue;
                }
                if let Some(&(_, w)) = s.wits.iter().find(|x| x.0 == a) {
                    pick = Some((k, s.m.find(w)));
                    break;
                }
            }
        } else if want_ind.is_some() && !slots.is_empty() && verified[0].0 == 0 {
            pick = Some((0, NONE));
        }
        let (k, w) = match pick {
            Some(p) => p,
            None => return,
        };
        let s = &slots[k];
        // the row needs only the witness, the individuals, and what they reach
        let mut roots: Vec<Id> = if w != NONE { vec![w] } else { Vec::new() };
        roots.extend(s.m.nom_elem.values().copied());
        if roots.is_empty() {
            roots.extend(s.wits.iter().map(|x| x.1).take(1));
        }
        let keep = emit::reachable(&s.m, &roots);
        let mut ren = Engine::new(rnf, Opts { loops: cfg.loops, ..Opts::default() });
        let mut rm = Model::new();
        let mut idx = std::collections::HashMap::new();
        for &x in &keep {
            let mut ty: Vec<u32> = en.sets.get(s.m.elems[x as usize].ty).iter().map(|&a| c(a)).collect();
            if x == w {
                if let Some(nu) = nu {
                    ty.push(nu);
                }
            }
            ty.sort_unstable();
            let f = ren.sets.intern(ty.clone());
            let id = rm.push_elem(Elem {
                ty: 0,
                forced: f,
                forbid: 0,
                target: 0,
                edges: Vec::new(),
                pending: ty,
                nom: s.m.elems[x as usize].nom,
                pinned: true,
                owner: NONE,
                alive: true,
            });
            idx.insert(x, id);
            rm.enqueue(id);
        }
        for &x in &keep {
            for &(y, l) in &s.m.elems[x as usize].edges {
                let (Some(&a), Some(&b)) = (idx.get(&x), idx.get(&s.m.find(y))) else { continue };
                let roles: Vec<u32> = en.labs.get(l).iter().map(|&q| r(q)).collect();
                let rl = ren.upclose(&roles);
                if a <= b {
                    ren.add_edge(&mut rm, a, b, rl);
                }
            }
        }
        if let Err(e) = ren.saturate(&mut rm) {
            result = Err(format!("row model: {}", e.reason));
            return;
        }
        let rep = check::verify(&mut ren, &rm);
        if rep.violations > 0 {
            result = Err(format!("row model self-check: {}", rep.first.unwrap_or_default()));
            return;
        }
        let keep2: Vec<Id> = rm.canonical().collect();
        match emit::write_hint(&ren, &rm, &keep2, out, "km-hints row model") {
            Ok(wr) => {
                result = Ok(format!(
                    "{{\"ok\":true,\"model\":{},\"elements\":{},\"edges\":{},\"bytes\":{}}}",
                    k, wr.elements, wr.edges, wr.bytes
                ))
            }
            Err(e) => result = Err(e.to_string()),
        }
    };
    build::produce(nf, km, cfg, "", Some(&mut hook));
    result
}
