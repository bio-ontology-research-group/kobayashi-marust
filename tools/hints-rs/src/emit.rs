//! Output of a model: the hint text of the `sroiq-hint` route (a core
//! without tree records: `blocks`, `ty`, `lab`) and the witness table.
//! Kept in one module so the format can follow the checker (stage H2).

use crate::engine::{Engine, FxMap, Id, Model};
use crate::nf::rts;
use std::collections::VecDeque;
use std::io::{BufWriter, Write};

/// Canonical elements reachable from `roots`, in a stable order.
pub fn reachable(m: &Model, roots: &[Id]) -> Vec<Id> {
    let mut seen = vec![false; m.elems.len()];
    let mut out = Vec::new();
    let mut q = VecDeque::new();
    for &r in roots {
        let r = m.find(r);
        if !seen[r as usize] {
            seen[r as usize] = true;
            q.push_back(r);
        }
    }
    while let Some(x) = q.pop_front() {
        out.push(x);
        for &(y, _) in &m.elems[x as usize].edges {
            let y = m.find(y);
            if !seen[y as usize] {
                seen[y as usize] = true;
                q.push_back(y);
            }
        }
    }
    let mut nom_cnt: FxMap<Id, usize> = FxMap::default();
    for &e in m.nom_elem.values() {
        *nom_cnt.entry(m.find(e)).or_default() += 1;
    }
    out.sort_unstable_by_key(|&x| {
        let c = nom_cnt.get(&x).copied().unwrap_or(0);
        (c == 0 && !m.elems[x as usize].nom, std::cmp::Reverse(c), x)
    });
    out
}

pub struct Written {
    pub index: FxMap<Id, u32>,
    pub elements: usize,
    pub edges: usize,
    pub type_entries: usize,
    pub bytes: u64,
}

/// Data stars: the data part of the normal form and the candidate values.
pub type DataCtx<'d> = Option<(&'d crate::data::DataNf, &'d crate::data::Values)>;

pub fn write_hint(en: &Engine, m: &Model, keep: &[Id], path: &str, comment: &str) -> std::io::Result<Written> {
    write_hint_d(en, m, keep, path, comment, None).map(|x| x.0)
}

/// As `write_hint`, with a `dstar` star per element where one is found;
/// returns also (elements with a star, elements without).
pub fn write_hint_d(
    en: &Engine,
    m: &Model,
    keep: &[Id],
    path: &str,
    comment: &str,
    dc: DataCtx,
) -> std::io::Result<(Written, usize, usize)> {
    let mut index: FxMap<Id, u32> = FxMap::default();
    for (i, &x) in keep.iter().enumerate() {
        index.insert(x, i as u32);
    }
    let f = std::fs::File::create(path)?;
    let mut w = BufWriter::new(f);
    if !comment.is_empty() {
        writeln!(w, "# {}", comment)?;
    }
    writeln!(w, "blocks {}", keep.len())?;
    let mut tyn = 0;
    for (i, &x) in keep.iter().enumerate() {
        let ts = en.sets.get(m.elems[x as usize].ty);
        tyn += ts.len();
        write!(w, "ty {}", i)?;
        for a in ts.iter() {
            write!(w, " {}", a)?;
        }
        writeln!(w)?;
    }
    let mut ne = 0;
    for (i, &x) in keep.iter().enumerate() {
        for &(y, l) in &m.elems[x as usize].edges {
            let j = match index.get(&y) {
                Some(&j) => j,
                None => continue,
            };
            if (i as u32) > j {
                continue;
            }
            let ls = en.labs.get(l);
            if ls.is_empty() {
                continue;
            }
            ne += 1;
            write!(w, "lab {} {}", i, j)?;
            for &r in ls.iter() {
                write!(w, " {}", rts(r))?;
            }
            writeln!(w)?;
        }
    }
    let (mut with, mut without) = (0, 0);
    if let Some((d, vals)) = dc {
        if let Some(pl) = d.part_lines() {
            for l in pl {
                writeln!(w, "{}", l)?;
            }
        }
        let mut cache: FxMap<u32, Option<Vec<crate::data::Entry>>> = FxMap::default();
        for (i, &x) in keep.iter().enumerate() {
            let t = m.elems[x as usize].ty;
            let st = cache.entry(t).or_insert_with(|| crate::data::star(d, vals, &en.sets.get(t)));
            match st {
                Some(ents) => {
                    with += 1;
                    writeln!(w, "dstar {}", i)?;
                    for e in ents.iter() {
                        write!(w, "dstar {}", i)?;
                        for p in &e.label {
                            write!(w, " {}", p)?;
                        }
                        write!(w, " /")?;
                        for a in &e.ty {
                            write!(w, " {}", a)?;
                        }
                        writeln!(w)?;
                    }
                }
                None => without += 1,
            }
        }
    }
    w.flush()?;
    let bytes = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
    Ok((Written { index, elements: keep.len(), edges: ne, type_entries: tyn, bytes }, with, without))
}

/// The witness table of the H2 witness row: `witness CLASS ELEMENT` lines
/// (individuals are found by their nominal names).
pub fn write_table(rows: &[(&str, String, u32)], path: &str) -> std::io::Result<()> {
    let f = std::fs::File::create(path)?;
    let mut w = BufWriter::new(f);
    for (kind, iri, e) in rows {
        writeln!(w, "{} {} {}", kind, iri, e)?;
    }
    w.flush()
}
