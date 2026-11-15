//! The checker's normal form, read from `--print-index` and
//! `--print-clauses` of `km-owl-reference --procedure sroiq-hint`.
//!
//! Roles are encoded as integers: `+k` is `2k`, `-k` is `2k+1`, so the
//! inverse of `r` is `r ^ 1`.

use std::collections::HashMap;
use std::fmt;

/// Compressed rows: `off[i]..off[i+1]` indexes `dat`.
#[derive(Default, Clone)]
pub struct Csr<T> {
    off: Vec<u32>,
    dat: Vec<T>,
}

impl<T: Copy> Csr<T> {
    pub fn build(n: usize, items: impl Iterator<Item = (u32, T)> + Clone) -> Self {
        let mut cnt = vec![0u32; n + 1];
        for (k, _) in items.clone() {
            cnt[k as usize + 1] += 1;
        }
        for i in 0..n {
            cnt[i + 1] += cnt[i];
        }
        let mut pos = cnt.clone();
        let total = cnt[n] as usize;
        let mut dat: Vec<Option<T>> = vec![None; total];
        for (k, v) in items {
            let p = &mut pos[k as usize];
            dat[*p as usize] = Some(v);
            *p += 1;
        }
        Csr { off: cnt, dat: dat.into_iter().map(|x| x.unwrap()).collect() }
    }
    #[inline]
    pub fn get(&self, k: u32) -> &[T] {
        let k = k as usize;
        if k + 1 >= self.off.len() {
            return &[];
        }
        &self.dat[self.off[k] as usize..self.off[k + 1] as usize]
    }
}

pub fn rt(s: &str) -> Option<u32> {
    let (sign, rest) = s.split_at(1);
    let k: u32 = rest.parse().ok()?;
    match sign {
        "+" => Some(2 * k),
        "-" => Some(2 * k + 1),
        _ => None,
    }
}

pub fn rts(r: u32) -> String {
    format!("{}{}", if r % 2 == 0 { '+' } else { '-' }, r / 2)
}

#[derive(Default)]
pub struct Nf {
    pub n: usize,
    pub m: usize,
    /// concept index -> IRI, for the listed concepts
    pub cname: Vec<Option<String>>,
    pub cidx: HashMap<String, u32>,
    pub rname: Vec<Option<String>>,
    pub ridx: HashMap<String, u32>,
    /// individual IRI -> nominal concept
    pub nominal: Vec<(String, u32)>,
    pub gci: Vec<(Vec<u32>, Vec<u32>)>,
    pub ex: Vec<(u32, u32, u32)>,
    pub all: Vec<(u32, u32, u32)>,
    pub ge: Vec<(u32, u32, u32, u32)>,
    pub le: Vec<(u32, u32, u32, u32)>,
    pub chains: Vec<(Vec<u32>, u32)>,
    pub noms: Vec<u32>,
    pub data_clauses: usize,
    // derived
    pub is_nom: Vec<bool>,
    /// a listed concept with a source IRI (not `urn:km:`)
    pub named: Vec<bool>,
    pub gci_by_body: Csr<u32>,
    pub gci_empty: Vec<u32>,
    pub body_len: Vec<u32>,
    pub ex_by: Csr<(u32, u32)>,
    pub all_by: Csr<(u32, u32)>,
    pub ge_by: Csr<(u32, u32, u32)>,
    pub le_by: Csr<(u32, u32, u32)>,
    /// role -> its up-closure under the role inclusions (sorted)
    pub up: Vec<Vec<u32>>,
    pub long_chains: usize,
    /// concept -> it occurs in an at-most clause body (fast skip)
    pub has_le: Vec<bool>,
}

#[derive(Debug)]
pub struct ParseError(pub String);
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn num(s: Option<&str>, line: &str) -> Result<u32, ParseError> {
    s.and_then(|x| x.parse().ok()).ok_or_else(|| ParseError(format!("bad line: {}", line)))
}
fn role(s: Option<&str>, line: &str) -> Result<u32, ParseError> {
    s.and_then(rt).ok_or_else(|| ParseError(format!("bad role in: {}", line)))
}

impl Nf {
    pub fn parse(index: &str, clauses: &str) -> Result<Nf, ParseError> {
        let mut nf = Nf::default();
        for line in index.lines() {
            let mut it = line.splitn(3, ' ');
            let d = it.next().unwrap_or("");
            match d {
                "concepts" => nf.n = num(it.next(), line)? as usize,
                "roles" => nf.m = num(it.next(), line)? as usize,
                "concept" | "role" | "nominal" => {
                    let i = num(it.next(), line)?;
                    let iri = match it.next() {
                        Some(x) => x.to_string(),
                        None => continue,
                    };
                    match d {
                        "concept" => {
                            if nf.cname.len() <= i as usize {
                                nf.cname.resize(i as usize + 1, None);
                            }
                            nf.cidx.insert(iri.clone(), i);
                            nf.cname[i as usize] = Some(iri);
                        }
                        "role" => {
                            if nf.rname.len() <= i as usize {
                                nf.rname.resize(i as usize + 1, None);
                            }
                            nf.ridx.insert(iri.clone(), i);
                            nf.rname[i as usize] = Some(iri);
                        }
                        _ => nf.nominal.push((iri, i)),
                    }
                }
                _ => {}
            }
        }
        nf.cname.resize(nf.n, None);
        nf.rname.resize(nf.m, None);
        for line in clauses.lines() {
            let mut w = line.split_ascii_whitespace();
            let d = match w.next() {
                Some(d) => d,
                None => continue,
            };
            match d {
                "gci" => {
                    let mut body = Vec::new();
                    let mut head = Vec::new();
                    let mut in_head = false;
                    for t in w {
                        if t == "->" {
                            in_head = true;
                            continue;
                        }
                        let x: u32 = t.parse().map_err(|_| ParseError(format!("bad gci: {}", line)))?;
                        if in_head {
                            head.push(x)
                        } else {
                            body.push(x)
                        }
                    }
                    body.sort_unstable();
                    body.dedup();
                    head.sort_unstable();
                    head.dedup();
                    nf.gci.push((body, head));
                }
                "some" => {
                    let a = num(w.next(), line)?;
                    let r = role(w.next(), line)?;
                    let b = num(w.next(), line)?;
                    nf.ex.push((a, r, b));
                }
                "all" => {
                    let a = num(w.next(), line)?;
                    let r = role(w.next(), line)?;
                    let b = num(w.next(), line)?;
                    nf.all.push((a, r, b));
                }
                "atleast" | "atmost" => {
                    let a = num(w.next(), line)?;
                    let k = num(w.next(), line)?;
                    let r = role(w.next(), line)?;
                    let b = num(w.next(), line)?;
                    if d == "atleast" {
                        nf.ge.push((a, k, r, b))
                    } else {
                        nf.le.push((a, k, r, b))
                    }
                }
                "chain" => {
                    let toks: Vec<u32> = w
                        .filter(|t| *t != "->" && *t != "|")
                        .map(|t| role(Some(t), line))
                        .collect::<Result<_, _>>()?;
                    if toks.len() < 2 {
                        return Err(ParseError(format!("bad chain: {}", line)));
                    }
                    let s = *toks.last().unwrap();
                    nf.chains.push((toks[..toks.len() - 1].to_vec(), s));
                }
                "nom" => nf.noms.push(num(w.next(), line)?),
                "data-clauses" => nf.data_clauses = num(w.next(), line)? as usize,
                _ => {}
            }
        }
        nf.noms.sort_unstable();
        nf.noms.dedup();
        nf.index();
        Ok(nf)
    }

    fn index(&mut self) {
        let n = self.n;
        self.is_nom = vec![false; n];
        for &o in &self.noms {
            self.is_nom[o as usize] = true;
        }
        self.named = (0..n)
            .map(|i| matches!(&self.cname[i], Some(s) if !s.starts_with("urn:km:")))
            .collect();
        let gci = &self.gci;
        self.gci_by_body =
            Csr::build(n, gci.iter().enumerate().flat_map(|(g, (b, _))| b.iter().map(move |&a| (a, g as u32))));
        self.gci_empty = gci.iter().enumerate().filter(|(_, (b, _))| b.is_empty()).map(|(g, _)| g as u32).collect();
        self.body_len = gci.iter().map(|(b, _)| b.len() as u32).collect();
        self.ex_by = Csr::build(n, self.ex.iter().map(|&(a, r, b)| (a, (r, b))));
        self.all_by = Csr::build(n, self.all.iter().map(|&(a, r, b)| (a, (r, b))));
        self.ge_by = Csr::build(n, self.ge.iter().map(|&(a, k, r, b)| (a, (k, r, b))));
        self.le_by = Csr::build(n, self.le.iter().map(|&(a, k, r, b)| (a, (k, r, b))));
        self.has_le = vec![false; n];
        for &(a, _, _, _) in &self.le {
            self.has_le[a as usize] = true;
        }
        let nr = 2 * self.m;
        let mut step: Vec<Vec<u32>> = vec![Vec::new(); nr];
        for (body, s) in &self.chains {
            if body.len() == 1 {
                let r = body[0];
                if (r as usize) < nr && (*s as usize) < nr {
                    step[r as usize].push(*s);
                    step[(r ^ 1) as usize].push(s ^ 1);
                }
            } else {
                self.long_chains += 1;
            }
        }
        self.up = (0..nr)
            .map(|r| {
                let mut seen = vec![r as u32];
                let mut st = vec![r as u32];
                while let Some(x) = st.pop() {
                    for &y in &step[x as usize] {
                        if !seen.contains(&y) {
                            seen.push(y);
                            st.push(y);
                        }
                    }
                }
                seen.sort_unstable();
                seen
            })
            .collect();
    }

    pub fn cname_of(&self, c: u32) -> &str {
        self.cname.get(c as usize).and_then(|x| x.as_deref()).unwrap_or("")
    }
}
