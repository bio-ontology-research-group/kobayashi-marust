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
    out.sort_unstable();
    out
}

pub struct Written {
    pub index: FxMap<Id, u32>,
    pub elements: usize,
    pub edges: usize,
    pub type_entries: usize,
    pub bytes: u64,
}

pub fn write_hint(en: &Engine, m: &Model, keep: &[Id], path: &str, comment: &str) -> std::io::Result<Written> {
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
    w.flush()?;
    let bytes = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
    Ok(Written { index, elements: keep.len(), edges: ne, type_entries: tyn, bytes })
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
