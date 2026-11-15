//! Data stars per core element (`dstar B P... / A...` lines, checker
//! 02c7016a and later): for each element, data neighbours (entries) with a
//! label of data properties and the full atom type of a concrete value.
//!
//! Values are chosen from candidates (oneOf literals, facet bounds,
//! defaults per datatype); the type of an entry is every atom the value
//! satisfies, as the checker asks. An element whose data clauses use an
//! atom this module cannot evaluate (patterns, unknown datatypes) gets no
//! star, and the checker then searches its star itself. Untrusted.

use std::collections::HashMap;

#[derive(Clone, Debug)]
pub enum Lit {
    Pos(u32),
    Neg(u32),
}

#[derive(Default, Clone)]
pub struct DataNf {
    pub dsome: Vec<(u32, u32, Vec<u32>, Vec<u32>)>,
    pub dall: Vec<(u32, u32, Vec<Lit>)>,
    pub datleast: Vec<(u32, u32, u32, Vec<u32>, Vec<u32>)>,
    pub datmost: Vec<(u32, u32, u32, Vec<u32>, Vec<u32>)>,
    pub dsub: Vec<(u32, u32)>,
    pub atoms: HashMap<u32, String>,
    pub ndprops: u32,
}

#[derive(Clone, Debug, PartialEq)]
enum Val {
    Num(Kind, f64),
    Str(String),
    Bool(bool),
    Other(String, String),
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    Dec, // integer and decimal share a value space
    Float,
    Double,
}

const XSD: &str = "http://www.w3.org/2001/XMLSchema#";

fn parse_list(w: &[&str]) -> (Vec<u32>, Vec<u32>) {
    let i = w.iter().position(|x| *x == "/").unwrap_or(w.len());
    let p = w[..i].iter().filter_map(|x| x.parse().ok()).collect();
    let n = if i < w.len() { w[i + 1..].iter().filter_map(|x| x.parse().ok()).collect() } else { Vec::new() };
    (p, n)
}

impl DataNf {
    pub fn parse(clauses: &str) -> DataNf {
        let mut d = DataNf::default();
        for line in clauses.lines() {
            let w: Vec<&str> = line.split_ascii_whitespace().collect();
            if w.is_empty() {
                continue;
            }
            let num = |i: usize| -> u32 { w.get(i).and_then(|x| x.parse().ok()).unwrap_or(0) };
            match w[0] {
                "dsome" if w.len() >= 3 => {
                    let (p, n) = parse_list(&w[3..]);
                    d.dsome.push((num(1), num(2), p, n));
                    d.ndprops = d.ndprops.max(num(2) + 1);
                }
                "dall" if w.len() >= 3 => {
                    let lits = w[3..]
                        .iter()
                        .filter_map(|x| {
                            if let Some(r) = x.strip_prefix('~') {
                                r.parse().ok().map(Lit::Neg)
                            } else {
                                x.parse().ok().map(Lit::Pos)
                            }
                        })
                        .collect();
                    d.dall.push((num(1), num(2), lits));
                }
                "datleast" | "datmost" if w.len() >= 4 => {
                    let (p, n) = parse_list(&w[4..]);
                    let t = (num(1), num(2), num(3), p, n);
                    if w[0] == "datleast" {
                        d.datleast.push(t)
                    } else {
                        d.datmost.push(t)
                    }
                }
                "dsub" if w.len() >= 3 => d.dsub.push((num(1), num(2))),
                "atom" if w.len() >= 3 => {
                    let rest = line.splitn(3, ' ').nth(2).unwrap_or("").to_string();
                    d.atoms.insert(num(1), rest);
                }
                _ => {}
            }
        }
        d
    }

    pub fn is_empty(&self) -> bool {
        self.dsome.is_empty() && self.dall.is_empty() && self.datleast.is_empty() && self.datmost.is_empty()
    }
}

/// `{ lexical := "...", datatype := "...", lang := ... }` literals in an atom text.
fn literals(s: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut rest = s;
    while let Some(i) = rest.find("lexical := \"") {
        let r = &rest[i + 12..];
        let j = match r.find('"') {
            Some(j) => j,
            None => break,
        };
        let lex = r[..j].to_string();
        let r2 = &r[j..];
        let dt = match r2.find("datatype := \"") {
            Some(k) => {
                let r3 = &r2[k + 13..];
                r3[..r3.find('"').unwrap_or(0)].to_string()
            }
            None => String::new(),
        };
        out.push((lex, dt));
        rest = &r[j..];
    }
    out
}

fn first_quoted(s: &str) -> Option<String> {
    let i = s.find('"')?;
    let r = &s[i + 1..];
    Some(r[..r.find('"')?].to_string())
}

fn num_kind(dt: &str) -> Option<Kind> {
    let l = dt.strip_prefix(XSD)?;
    match l {
        "float" => Some(Kind::Float),
        "double" => Some(Kind::Double),
        "decimal" | "integer" | "nonNegativeInteger" | "positiveInteger" | "nonPositiveInteger"
        | "negativeInteger" | "long" | "int" | "short" | "byte" | "unsignedLong" | "unsignedInt"
        | "unsignedShort" | "unsignedByte" => Some(Kind::Dec),
        _ => None,
    }
}

fn lit_val(lex: &str, dt: &str) -> Option<Val> {
    if let Some(k) = num_kind(dt) {
        return lex.trim().parse::<f64>().ok().map(|x| Val::Num(k, x));
    }
    if dt == format!("{}string", XSD) || dt.ends_with("PlainLiteral") || dt.is_empty() {
        return Some(Val::Str(lex.to_string()));
    }
    if dt == format!("{}boolean", XSD) {
        return Some(Val::Bool(lex == "true" || lex == "1"));
    }
    Some(Val::Other(dt.to_string(), lex.to_string()))
}

/// Membership of a value in a named datatype; None: not understood.
fn in_dt(v: &Val, dt: &str) -> Option<bool> {
    if dt.ends_with("rdf-schema#Literal") {
        return Some(true);
    }
    if dt.ends_with("owl#real") || dt.ends_with("owl#rational") {
        return Some(matches!(v, Val::Num(Kind::Dec, _)));
    }
    if dt.ends_with("rdf-syntax-ns#PlainLiteral") {
        return Some(matches!(v, Val::Str(_)));
    }
    let l = match dt.strip_prefix(XSD) {
        Some(l) => l,
        None => return None,
    };
    let int = |x: f64| x.fract() == 0.0;
    Some(match (l, v) {
        ("string", Val::Str(_)) => true,
        ("normalizedString" | "token" | "Name" | "NCName" | "NMTOKEN", Val::Str(s)) => {
            !s.is_empty() && s.chars().all(|c| c.is_ascii_alphabetic())
        }
        ("boolean", Val::Bool(_)) => true,
        ("float", Val::Num(Kind::Float, _)) => true,
        ("double", Val::Num(Kind::Double, _)) => true,
        ("decimal", Val::Num(Kind::Dec, _)) => true,
        ("integer", Val::Num(Kind::Dec, x)) => int(*x),
        ("nonNegativeInteger", Val::Num(Kind::Dec, x)) => int(*x) && *x >= 0.0,
        ("positiveInteger", Val::Num(Kind::Dec, x)) => int(*x) && *x > 0.0,
        ("nonPositiveInteger", Val::Num(Kind::Dec, x)) => int(*x) && *x <= 0.0,
        ("negativeInteger", Val::Num(Kind::Dec, x)) => int(*x) && *x < 0.0,
        ("long", Val::Num(Kind::Dec, x)) => int(*x) && x.abs() < 9.2e18,
        ("int", Val::Num(Kind::Dec, x)) => int(*x) && *x >= -2147483648.0 && *x <= 2147483647.0,
        ("short", Val::Num(Kind::Dec, x)) => int(*x) && *x >= -32768.0 && *x <= 32767.0,
        ("byte", Val::Num(Kind::Dec, x)) => int(*x) && *x >= -128.0 && *x <= 127.0,
        ("unsignedLong" | "unsignedInt" | "unsignedShort" | "unsignedByte", Val::Num(Kind::Dec, x)) => {
            let hi = match l {
                "unsignedByte" => 255.0,
                "unsignedShort" => 65535.0,
                "unsignedInt" => 4294967295.0,
                _ => 1.8e19,
            };
            int(*x) && *x >= 0.0 && *x <= hi
        }
        ("language", _) => return None,
        (_, Val::Other(d, _)) => d == dt,
        (
            "string" | "normalizedString" | "token" | "Name" | "NCName" | "NMTOKEN" | "boolean" | "float"
            | "double" | "decimal" | "integer" | "nonNegativeInteger" | "positiveInteger"
            | "nonPositiveInteger" | "negativeInteger" | "long" | "int" | "short" | "byte" | "unsignedLong"
            | "unsignedInt" | "unsignedShort" | "unsignedByte",
            _,
        ) => false,
        _ => return None,
    })
}

fn num_of(v: &Val) -> Option<(Kind, f64)> {
    match v {
        Val::Num(k, x) => Some((*k, *x)),
        _ => None,
    }
}

/// Membership of a value in an atom; None: not understood.
fn member(v: &Val, atom: &str) -> Option<bool> {
    let a = atom.trim();
    if a.starts_with("ContextCalculus.OWL.DataRange.datatype") {
        return in_dt(v, &first_quoted(a)?);
    }
    if a.starts_with("ContextCalculus.OWL.DataRange.oneOf") {
        for (lex, dt) in literals(a) {
            let w = lit_val(&lex, &dt)?;
            let eq = match (&w, v) {
                (Val::Num(k1, x1), Val::Num(k2, x2)) => k1 == k2 && x1 == x2,
                _ => &w == v,
            };
            if eq {
                return Some(true);
            }
        }
        return Some(false);
    }
    if a.starts_with("ContextCalculus.OWL.DataRange.restriction") {
        let dt = first_quoted(a)?;
        if !in_dt(v, &dt)? {
            return Some(false);
        }
        // facets: ("FACET", { lexical := ... })
        let mut rest = &a[a.find('[')?..];
        while let Some(i) = rest.find("(\"") {
            let r = &rest[i + 2..];
            let facet = &r[..r.find('"')?];
            let lits = literals(r);
            let (lex, _) = lits.first()?.clone();
            let b: f64 = match lex.parse() {
                Ok(b) => b,
                Err(_) => return None,
            };
            let (_, x) = num_of(v)?;
            let ok = match facet.strip_prefix(XSD)? {
                "minInclusive" => x >= b,
                "minExclusive" => x > b,
                "maxInclusive" => x <= b,
                "maxExclusive" => x < b,
                _ => return None,
            };
            if !ok {
                return Some(false);
            }
            rest = &r[r.find('}')? ..];
        }
        return Some(true);
    }
    None
}

#[derive(Clone)]
pub struct Values {
    cands: Vec<Val>,
    /// candidate -> its atom type (sorted), None when some atom is not understood
    types: Vec<Option<Vec<u32>>>,
}

impl Values {
    /// Every candidate value was evaluated on every atom.
    pub fn complete(&self) -> bool {
        self.types.iter().all(|t| t.is_some())
    }

    pub fn new(d: &DataNf) -> Values {
        let mut cands: Vec<Val> = Vec::new();
        let mut push = |v: Val, c: &mut Vec<Val>| {
            if !c.contains(&v) {
                c.push(v)
            }
        };
        let mut keys: Vec<&u32> = d.atoms.keys().collect();
        keys.sort();
        for k in &keys {
            let a = &d.atoms[k];
            let lits = literals(a);
            let dt = first_quoted(a).unwrap_or_default();
            let kind = num_kind(&dt);
            let mut bounds: Vec<f64> = Vec::new();
            for (lex, ldt) in &lits {
                if let Some(v) = lit_val(lex, ldt) {
                    if let Val::Num(_, x) = v {
                        bounds.push(x);
                    }
                    push(v, &mut cands);
                }
            }
            if let Some(k) = kind {
                for &b in &bounds {
                    for x in [b - 1.0, b + 1.0, b - 0.5, b + 0.5] {
                        push(Val::Num(k, x), &mut cands);
                    }
                }
                if bounds.len() >= 2 {
                    let m = ((bounds[0] + bounds[1]) / 2.0).floor();
                    push(Val::Num(k, m), &mut cands);
                }
            } else if !dt.is_empty() && !dt.ends_with("Literal") && in_dt(&Val::Str("a".into()), &dt).is_none() {
                push(Val::Other(dt.clone(), "x".into()), &mut cands);
            }
        }
        for v in [
            Val::Str("a".into()),
            Val::Str("a b".into()),
            Val::Num(Kind::Dec, 0.0),
            Val::Num(Kind::Dec, 1.0),
            Val::Num(Kind::Dec, -1.0),
            Val::Num(Kind::Dec, 0.5),
            Val::Num(Kind::Dec, 1000.0),
            Val::Num(Kind::Float, 0.5),
            Val::Num(Kind::Double, 0.5),
            Val::Bool(true),
            Val::Bool(false),
        ] {
            push(v, &mut cands);
        }
        let types = cands
            .iter()
            .map(|v| {
                let mut t = Vec::new();
                for k in &keys {
                    match member(v, &d.atoms[k]) {
                        Some(true) => t.push(**k),
                        Some(false) => {}
                        None => return None,
                    }
                }
                Some(t)
            })
            .collect();
        Values { cands, types }
    }
}

pub struct Entry {
    pub label: Vec<u32>,
    pub ty: Vec<u32>,
}

fn has(v: &[u32], x: u32) -> bool {
    v.binary_search(&x).is_ok()
}

/// The data star of an element of type `t` (sorted names), or None.
pub fn star(d: &DataNf, vals: &Values, t: &[u32]) -> Option<Vec<Entry>> {
    let up = |u: u32| -> Vec<u32> {
        let mut out = vec![u];
        let mut i = 0;
        while i < out.len() {
            let x = out[i];
            for &(a, b) in &d.dsub {
                if a == x && !out.contains(&b) {
                    out.push(b);
                }
            }
            i += 1;
        }
        out.sort_unstable();
        out
    };
    let alls: Vec<&(u32, u32, Vec<Lit>)> = d.dall.iter().filter(|c| has(t, c.0)).collect();
    // an entry fits: range of the requirement and every universal over its label
    let fits = |label: &[u32], ty: &[u32], pos: &[u32], neg: &[u32]| -> bool {
        pos.iter().all(|p| has(ty, *p))
            && !neg.iter().any(|n| has(ty, *n))
            && alls.iter().all(|(_, u, lits)| {
                !has(label, *u)
                    || lits.iter().any(|l| match l {
                        Lit::Pos(j) => has(ty, *j),
                        Lit::Neg(j) => !has(ty, *j),
                    })
            })
    };
    let pick = |label: &[u32], pos: &[u32], neg: &[u32], avoid: &[Vec<u32>]| -> Option<Vec<u32>> {
        for ty in vals.types.iter().flatten() {
            if avoid.contains(ty) {
                continue;
            }
            if fits(label, ty, pos, neg) {
                return Some(ty.clone());
            }
        }
        None
    };
    let mut ents: Vec<Entry> = Vec::new();
    let mut reqs: Vec<(u32, u32, Vec<u32>, Vec<u32>)> = Vec::new();
    for c in &d.dsome {
        if has(t, c.0) {
            reqs.push((1, c.1, c.2.clone(), c.3.clone()));
        }
    }
    for c in &d.datleast {
        if has(t, c.0) {
            reqs.push((c.1, c.2, c.3.clone(), c.4.clone()));
        }
    }
    let cnt = |ents: &[Entry], u: u32, pos: &[u32], neg: &[u32]| -> u32 {
        ents.iter()
            .filter(|e| has(&e.label, u) && pos.iter().all(|p| has(&e.ty, *p)) && !neg.iter().any(|n| has(&e.ty, *n)))
            .count() as u32
    };
    for (n, u, pos, neg) in &reqs {
        while cnt(&ents, *u, pos, neg) < *n {
            let lu = up(*u);
            // extend an existing entry whose value already fits
            let mut done = false;
            if *n == 1 {
                for e in ents.iter_mut() {
                    let mut l2 = e.label.clone();
                    l2.extend_from_slice(&lu);
                    l2.sort_unstable();
                    l2.dedup();
                    if fits(&l2, &e.ty, pos, neg) && fits(&l2, &e.ty, &[], &[]) {
                        e.label = l2;
                        done = true;
                        break;
                    }
                }
            }
            if done {
                continue;
            }
            // a finite value type (a oneOf atom in it) is taken at most once
            let avoid: Vec<Vec<u32>> = ents
                .iter()
                .filter(|e| e.ty.iter().any(|j| d.atoms.get(j).map(|a| a.contains("oneOf")).unwrap_or(false)))
                .map(|e| e.ty.clone())
                .collect();
            let ty = match pick(&lu, pos, neg, &avoid) {
                Some(t) => t,
                None => {
                    if std::env::var("KM_HINTS_DEBUG").is_ok() {
                        eprintln!("dstar: no value for u {} pos {:?} neg {:?}; {} candidates, {} understood",
                            u, pos, neg, vals.types.len(), vals.types.iter().flatten().count());
                    }
                    return None;
                }
            };
            ents.push(Entry { label: lu, ty });
        }
    }
    for c in &d.datmost {
        if has(t, c.0) && cnt(&ents, c.2, &c.3, &c.4) > c.1 {
            if std::env::var("KM_HINTS_DEBUG").is_ok() {
                eprintln!("dstar: at-most {:?} exceeded", c);
            }
            return None;
        }
    }
    Some(ents)
}
