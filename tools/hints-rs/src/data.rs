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
    pub groups: u32,
    /// split cells: (index, size)
    pub cells: Vec<(u32, u32)>,
    pub dsome_by: HashMap<u32, Vec<usize>>,
    pub dall_by: HashMap<u32, Vec<usize>>,
    pub datleast_by: HashMap<u32, Vec<usize>>,
    pub datmost_by: HashMap<u32, Vec<usize>>,
    pub is_oneof_atom: HashMap<u32, bool>,
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
                        if t.1 > 0 {
                            d.datleast.push(t);
                        }
                    } else {
                        d.datmost.push(t);
                    }
                }
                "dsub" if w.len() >= 3 => d.dsub.push((num(1), num(2))),
                "groups" if w.len() >= 2 => d.groups = num(1),
                "cell" if w.len() >= 3 => d.cells.push((num(1), num(2))),
                "atom" if w.len() >= 3 => {
                    let rest = line.splitn(3, ' ').nth(2).unwrap_or("").to_string();
                    d.is_oneof_atom.insert(num(1), rest.contains("oneOf"));
                    d.atoms.insert(num(1), rest);
                }
                _ => {}
            }
        }
        for (i, c) in d.dsome.iter().enumerate() {
            d.dsome_by.entry(c.0).or_default().push(i);
        }
        for (i, c) in d.dall.iter().enumerate() {
            d.dall_by.entry(c.0).or_default().push(i);
        }
        for (i, c) in d.datleast.iter().enumerate() {
            d.datleast_by.entry(c.0).or_default().push(i);
        }
        for (i, c) in d.datmost.iter().enumerate() {
            d.datmost_by.entry(c.0).or_default().push(i);
        }
        d
    }

    /// `part` lines naming the data part, when it is determined: with one
    /// group every split cell puts its whole size in group 0.
    pub fn part_lines(&self) -> Option<Vec<String>> {
        if self.cells.is_empty() {
            return Some(vec!["part".to_string()]);
        }
        if self.groups == 1 {
            return Some(self.cells.iter().map(|(i, n)| format!("part {} 0 {}", i, n)).collect());
        }
        None
    }

    pub fn is_empty(&self) -> bool {
        self.dsome.is_empty() && self.dall.is_empty() && self.datleast.is_empty() && self.datmost.is_empty()
    }
}

/// `{ lexical := "...", datatype := "...", lang := ... }` literals in an atom text.
fn literals(s: &str) -> Vec<(String, String)> {
    literals_l(s).into_iter().map(|(l, d, g)| match g {
        // a language tag makes the value a language-tagged string
        Some(g) => (format!("{}@{}", l, g), "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral".to_string()),
        None => (l, d),
    }).collect()
}

/// (lexical, datatype, language tag) of each literal.
fn literals_l(s: &str) -> Vec<(String, String, Option<String>)> {
    let mut out: Vec<(String, String, Option<String>)> = Vec::new();
    let mut rest = s;
    while let Some(i) = rest.find("lexical :=") {
        let r0 = rest[i + 10..].trim_start();
        let Some(r) = r0.strip_prefix('"') else {
            rest = &rest[i + 10..];
            continue;
        };
        let j = match r.find('"') {
            Some(j) => j,
            None => break,
        };
        let lex = r[..j].to_string();
        let r2 = &r[j..];
        let dt = match r2.find("datatype :=") {
            Some(k) => {
                let r3 = r2[k + 11..].trim_start();
                if let Some(r4) = r3.strip_prefix('"') {
                    r4[..r4.find('"').unwrap_or(0)].to_string()
                } else {
                    String::new()
                }
            }
            None => String::new(),
        };
        let lang = r2.find("lang :=").and_then(|k| {
            let r3 = r2[k + 7..].trim_start();
            if let Some(r4) = r3.strip_prefix("some") {
                let r5 = r4.trim_start().strip_prefix('"')?;
                r5.find('"').map(|e| r5[..e].to_string())
            } else {
                None
            }
        });
        out.push((lex, dt, lang));
        rest = &r[j..];
    }
    out
}

fn first_quoted(s: &str) -> Option<String> {
    let i = s.find('"')?;
    let r = &s[i + 1..];
    Some(r[..r.find('"')?].to_string())
}

fn all_quoted_dts(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    for pat in ["DataRange.datatype", "DataRange.restriction"] {
        let mut rest = s;
        while let Some(i) = rest.find(pat) {
            let r = rest[i + pat.len()..].trim_start();
            if let Some(r2) = r.strip_prefix('"') {
                if let Some(j) = r2.find('"') {
                    out.push(r2[..j].to_string());
                    rest = &r2[j + 1..];
                    continue;
                }
            }
            rest = &rest[i + pat.len()..];
        }
    }
    out
}

fn is_lang_tag(s: &str) -> bool {
    !s.is_empty()
        && s.split('-').enumerate().all(|(i, p)| {
            !p.is_empty()
                && p.len() <= 8
                && p.chars().all(|c| if i == 0 { c.is_ascii_alphabetic() } else { c.is_ascii_alphanumeric() })
        })
}

fn strip_outer_parens(mut s: &str) -> &str {
    loop {
        s = s.trim();
        if !(s.starts_with('(') && s.ends_with(')')) {
            return s;
        }
        let mut depth = 0i32;
        let mut in_str = false;
        let mut ok = true;
        for (i, c) in s.char_indices() {
            if c == '"' {
                in_str = !in_str;
            } else if !in_str {
                if c == '(' {
                    depth += 1;
                } else if c == ')' {
                    depth -= 1;
                    if depth == 0 && i + c.len_utf8() < s.len() {
                        ok = false;
                        break;
                    }
                }
            }
        }
        if ok && depth == 0 {
            s = &s[1..s.len() - 1];
        } else {
            return s;
        }
    }
}

fn split_top_list(s: &str) -> Option<Vec<&str>> {
    let s = s.trim();
    let i = s.find('[')?;
    let s = s[i + 1..].strip_suffix(']')?;
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut in_str = false;
    let mut start = 0usize;
    for (idx, c) in s.char_indices() {
        if c == '"' {
            in_str = !in_str;
        } else if !in_str {
            match c {
                '[' | '(' | '{' => depth += 1,
                ']' | ')' | '}' => depth -= 1,
                ',' if depth == 0 => {
                    out.push(s[start..idx].trim());
                    start = idx + 1;
                }
                _ => {}
            }
        }
    }
    let tail = s[start..].trim();
    if !tail.is_empty() {
        out.push(tail);
    }
    Some(out)
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
    if dt.ends_with("PlainLiteral") {
        // rdf:PlainLiteral lexical forms are "text@lang"; "text@" is the string "text";
        // a form without '@' is ill-formed and denotes no value
        let i = lex.rfind('@')?;
        let (text, lang) = (&lex[..i], &lex[i + 1..]);
        if lang.is_empty() {
            return Some(Val::Str(text.to_string()));
        }
        return Some(Val::Other(format!("@{}", lang.to_ascii_lowercase()), text.to_string()));
    }
    if dt == format!("{}string", XSD) || dt.is_empty() {
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
        return Some(match v {
            Val::Str(_) => true,
            Val::Other(d, _) => d.starts_with('@'),
            _ => false,
        });
    }
    // other built-in datatypes (anyURI, dateTime, XMLLiteral, binary, ...): a value
    // space of their own; dateTimeStamp values are dateTime values
    let own_space = |v: &Val| -> Option<bool> {
        Some(match v {
            Val::Other(d, _) => d == dt || (dt.ends_with("#dateTime") && d.ends_with("#dateTimeStamp")),
            _ => false,
        })
    };
    let l = match dt.strip_prefix(XSD) {
        Some(l) => l,
        None => {
            if dt.starts_with("http://www.w3.org/1999/02/22-rdf-syntax-ns#") {
                return own_space(v);
            }
            return None;
        }
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
        ("language", Val::Str(s)) => is_lang_tag(s),
        ("anyURI" | "dateTime" | "dateTimeStamp" | "date" | "time" | "duration" | "hexBinary"
        | "base64Binary" | "gYear" | "gYearMonth" | "gMonth" | "gMonthDay" | "gDay" | "QName", _) => {
            return own_space(v)
        }
        (_, Val::Other(d, _)) => d == dt,
        (
            "string" | "normalizedString" | "token" | "language" | "Name" | "NCName" | "NMTOKEN" | "boolean"
            | "float" | "double" | "decimal" | "integer" | "nonNegativeInteger" | "positiveInteger"
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
    let a = strip_outer_parens(atom);
    if let Some(rest) = a.strip_prefix("ContextCalculus.OWL.DataRange.and") {
        let items = split_top_list(rest)?;
        let mut all_true = true;
        for item in items {
            match member(v, item) {
                Some(true) => {}
                Some(false) => return Some(false),
                None => all_true = false,
            }
        }
        return if all_true { Some(true) } else { None };
    }
    if let Some(rest) = a.strip_prefix("ContextCalculus.OWL.DataRange.or") {
        let items = split_top_list(rest)?;
        let mut all_false = true;
        for item in items {
            match member(v, item) {
                Some(true) => return Some(true),
                Some(false) => {}
                None => all_false = false,
            }
        }
        return if all_false { Some(false) } else { None };
    }
    if let Some(rest) = a.strip_prefix("ContextCalculus.OWL.DataRange.complement") {
        return member(v, rest).map(|b| !b);
    }
    if a.starts_with("ContextCalculus.OWL.DataRange.datatype") {
        return in_dt(v, &first_quoted(a)?);
    }
    if a.starts_with("ContextCalculus.OWL.DataRange.oneOf") {
        for (lex, dt) in literals(a) {
            // an ill-formed literal denotes no value
            let w = match lit_val(&lex, &dt) {
                Some(w) => w,
                None => continue,
            };
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

fn val_key(v: &Val) -> (u8, u8, u64, String, String) {
    match v {
        Val::Num(k, x) => {
            let kn = match k {
                Kind::Dec => 1,
                Kind::Float => 2,
                Kind::Double => 3,
            };
            let bits = if *x == 0.0 { 0 } else { x.to_bits() };
            (0, kn, bits, String::new(), String::new())
        }
        Val::Str(s) => (1, 0, 0, s.clone(), String::new()),
        Val::Bool(b) => (2, *b as u8, 0, String::new(), String::new()),
        Val::Other(d, l) => (3, 0, 0, d.clone(), l.clone()),
    }
}

#[allow(dead_code)]
#[derive(Clone)]
pub struct Values {
    cands: Vec<Val>,
    /// the values named by oneOf literals
    lits: Vec<Val>,
    /// candidate -> its atom type (sorted), None when some atom is not understood
    types: Vec<Option<Vec<u32>>>,
    distinct_types: Vec<Vec<u32>>,
    pub by_atom: HashMap<u32, Vec<usize>>,
    #[allow(dead_code)]
    fcard: HashMap<Vec<u32>, Option<usize>>,
    pub fcard_by_idx: Vec<Option<usize>>,
    pub is_oneof_by_idx: Vec<bool>,
}

impl Values {
    /// The number of values of type `ty` when every candidate of that type is
    /// a boolean or a oneOf literal (a finite space), else None.
    #[allow(dead_code)]
    pub fn finite_card(&self, ty: &[u32]) -> Option<usize> {
        self.fcard.get(ty).copied().flatten()
    }

    /// Every candidate value was evaluated on every atom.
    pub fn complete(&self) -> bool {
        self.types.iter().all(|t| t.is_some())
    }

    pub fn new(d: &DataNf) -> Values {
        let mut cands: Vec<Val> = Vec::new();
        let mut seen_cands: std::collections::HashSet<(u8, u8, u64, String, String)> =
            std::collections::HashSet::new();
        let mut push = |v: Val, c: &mut Vec<Val>| {
            if seen_cands.insert(val_key(&v)) {
                c.push(v);
            }
        };
        let mut keys: Vec<&u32> = d.atoms.keys().collect();
        keys.sort();
        let mut all_bounds: Vec<(Kind, f64)> = Vec::new();
        let mut lits: Vec<Val> = Vec::new();
        let mut lits_set: std::collections::HashSet<(u8, u8, u64, String, String)> =
            std::collections::HashSet::new();
        let mut oneof_by_val: HashMap<(u8, u8, u64, String, String), Vec<u32>> = HashMap::new();
        let mut other_atoms: HashMap<&str, Vec<u32>> = HashMap::new();
        for k in &keys {
            let a = &d.atoms[k];
            let a_trimmed = strip_outer_parens(a);
            let is_top_oneof = a_trimmed.starts_with("ContextCalculus.OWL.DataRange.oneOf");
            let has_oneof = is_top_oneof || a.contains("DataRange.oneOf");
            let atom_lits = literals(a);
            let dts = if is_top_oneof { Vec::new() } else { all_quoted_dts(a) };
            let mut kinds: Vec<Kind> = dts.iter().filter_map(|dt| num_kind(dt)).collect();
            let mut bounds: Vec<f64> = Vec::new();
            for (lex, ldt) in &atom_lits {
                if let Some(v) = lit_val(lex, ldt) {
                    if let Val::Num(vk, x) = v {
                        bounds.push(x);
                        all_bounds.push((vk, x));
                        if !kinds.contains(&vk) {
                            kinds.push(vk);
                        }
                    }
                    if has_oneof {
                        let vk = val_key(&v);
                        if lits_set.insert(vk.clone()) {
                            lits.push(v.clone());
                        }
                        if is_top_oneof {
                            oneof_by_val.entry(vk).or_default().push(**k);
                        }
                    }
                    push(v, &mut cands);
                }
            }
            if !is_top_oneof {
                other_atoms.entry(a.as_str()).or_default().push(**k);
            }
            for &k in &kinds {
                for &b in &bounds {
                    all_bounds.push((k, b));
                    for x in [b - 1.0, b + 1.0, b - 0.5, b + 0.5, b / 2.0] {
                        push(Val::Num(k, x), &mut cands);
                    }
                }
                if bounds.len() >= 2 {
                    let m = (bounds[0] + bounds[1]) / 2.0;
                    push(Val::Num(k, m), &mut cands);
                    push(Val::Num(k, m.floor()), &mut cands);
                }
            }
            for dt in dts {
                if !dt.is_empty()
                    && in_dt(&Val::Str("a".into()), &dt) != Some(true)
                    && in_dt(&Val::Num(Kind::Dec, 0.0), &dt) != Some(true)
                    && in_dt(&Val::Num(Kind::Dec, 1.0), &dt) != Some(true)
                    && in_dt(&Val::Num(Kind::Dec, -1.0), &dt) != Some(true)
                    && in_dt(&Val::Bool(true), &dt) != Some(true)
                    && in_dt(&Val::Num(Kind::Float, 0.5), &dt) != Some(true)
                    && in_dt(&Val::Num(Kind::Double, 0.5), &dt) != Some(true)
                {
                    push(Val::Other(dt, "x".into()), &mut cands);
                }
            }
        }
        for i in 0..all_bounds.len().min(32) {
            for j in (i + 1)..all_bounds.len().min(32) {
                if all_bounds[i].0 == all_bounds[j].0 && all_bounds[i].1 != all_bounds[j].1 {
                    let k = all_bounds[i].0;
                    let m = (all_bounds[i].1 + all_bounds[j].1) / 2.0;
                    push(Val::Num(k, m), &mut cands);
                    push(Val::Num(k, m.floor()), &mut cands);
                }
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
            Val::Num(Kind::Float, 0.0),
            Val::Num(Kind::Float, 1.0),
            Val::Num(Kind::Float, -1.0),
            Val::Num(Kind::Float, 0.5),
            Val::Num(Kind::Float, 1000.0),
            Val::Num(Kind::Double, 0.0),
            Val::Num(Kind::Double, 1.0),
            Val::Num(Kind::Double, -1.0),
            Val::Num(Kind::Double, 0.5),
            Val::Num(Kind::Double, 1000.0),
            Val::Bool(true),
            Val::Bool(false),
        ] {
            push(v, &mut cands);
        }
        let types: Vec<Option<Vec<u32>>> = cands
            .iter()
            .map(|v| {
                let mut t = Vec::new();
                if let Some(ks) = oneof_by_val.get(&val_key(v)) {
                    t.extend_from_slice(ks);
                }
                for (&atom_str, ks) in &other_atoms {
                    match member(v, atom_str) {
                        Some(true) => t.extend_from_slice(ks),
                        Some(false) => {}
                        None => return None,
                    }
                }
                t.sort_unstable();
                t.dedup();
                Some(t)
            })
            .collect();
        let mut distinct_types: Vec<Vec<u32>> = Vec::new();
        let mut by_atom: HashMap<u32, Vec<usize>> = HashMap::new();
        let mut fcard: HashMap<Vec<u32>, Option<usize>> = HashMap::new();
        let mut fcard_by_idx: Vec<Option<usize>> = Vec::new();
        let mut is_oneof_by_idx: Vec<bool> = Vec::new();
        let mut idx_of_ty: HashMap<Vec<u32>, usize> = HashMap::new();
        for (v, t_opt) in cands.iter().zip(&types) {
            if let Some(t) = t_opt {
                let idx = if let Some(&ix) = idx_of_ty.get(t) {
                    ix
                } else {
                    let ix = distinct_types.len();
                    for &atom_id in t {
                        by_atom.entry(atom_id).or_default().push(ix);
                    }
                    let has_oo = t.iter().any(|k| d.is_oneof_atom.get(k).copied().unwrap_or(false));
                    distinct_types.push(t.clone());
                    fcard.insert(t.clone(), Some(0));
                    fcard_by_idx.push(Some(0));
                    is_oneof_by_idx.push(has_oo);
                    idx_of_ty.insert(t.clone(), ix);
                    ix
                };
                let is_fin = matches!(v, Val::Bool(_)) || lits_set.contains(&val_key(v));
                let entry = fcard.get_mut(t).unwrap();
                if is_fin {
                    if let Some(cnt) = entry {
                        *cnt += 1;
                    }
                    if let Some(cnt) = &mut fcard_by_idx[idx] {
                        *cnt += 1;
                    }
                } else {
                    *entry = None;
                    fcard_by_idx[idx] = None;
                }
            }
        }
        Values { cands, lits, types, distinct_types, by_atom, fcard, fcard_by_idx, is_oneof_by_idx }
    }
}

pub struct Entry {
    pub label: Vec<u32>,
    pub ty: Vec<u32>,
    ty_idx: usize,
    pos: Vec<u32>,
    neg: Vec<u32>,
}

fn has(v: &[u32], x: u32) -> bool {
    v.binary_search(&x).is_ok()
}

/// The data star of an element of type `t` (sorted names), or None: first
/// one entry per requirement, then, if an at-most bound is exceeded, with
/// values shared between requirements.
pub fn star(d: &DataNf, vals: &Values, t: &[u32]) -> Option<Vec<Entry>> {
    star_with(d, vals, t, false).or_else(|| if d.datmost.is_empty() { None } else { star_with(d, vals, t, true) })
}

fn star_with(d: &DataNf, vals: &Values, t: &[u32], share: bool) -> Option<Vec<Entry>> {
    let mut reqs: Vec<(u32, u32, Vec<u32>, Vec<u32>)> = Vec::new();
    for &a in t {
        if let Some(ixs) = d.dsome_by.get(&a) {
            for &i in ixs {
                let c = &d.dsome[i];
                reqs.push((1, c.1, c.2.clone(), c.3.clone()));
            }
        }
        if let Some(ixs) = d.datleast_by.get(&a) {
            for &i in ixs {
                let c = &d.datleast[i];
                reqs.push((c.1, c.2, c.3.clone(), c.4.clone()));
            }
        }
    }
    if reqs.is_empty() {
        return Some(Vec::new());
    }
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
    let mut forbid_by_u: HashMap<u32, Vec<u32>> = HashMap::new();
    let mut alls_by_u: HashMap<u32, Vec<&Vec<Lit>>> = HashMap::new();
    for a in t {
        if let Some(ixs) = d.dall_by.get(a) {
            for &i in ixs {
                let c = &d.dall[i];
                if c.2.len() == 1 {
                    if let Lit::Neg(j) = c.2[0] {
                        forbid_by_u.entry(c.1).or_default().push(j);
                        continue;
                    }
                }
                alls_by_u.entry(c.1).or_default().push(&c.2);
            }
        }
    }
    for fb in forbid_by_u.values_mut() {
        fb.sort_unstable();
        fb.dedup();
    }
    // an entry fits: range of the requirement and every universal over its label
    let fits = |label: &[u32], ty: &[u32], pos: &[u32], neg: &[u32]| -> bool {
        pos.iter().all(|p| has(ty, *p))
            && !neg.iter().any(|n| has(ty, *n))
            && label.iter().all(|u| {
                forbid_by_u
                    .get(u)
                    .map_or(true, |fb| !fb.iter().any(|&j| has(ty, j)))
                    && alls_by_u.get(u).map_or(true, |all_list| {
                        all_list.iter().all(|lits| {
                            lits.iter().any(|l| match l {
                                Lit::Pos(j) => has(ty, *j),
                                Lit::Neg(j) => !has(ty, *j),
                            })
                        })
                    })
            })
    };
    let n_dt = vals.distinct_types.len();
    let mut used_cnt: Vec<u32> = vec![0; n_dt];
    let mut avoid_cnt: Vec<u32> = vec![0; n_dt];
    // a value type already taken by an entry is used again only when no other
    // fits (a type can have few values: the checker bounds the entries per type)
    let pick = |label: &[u32],
                pos: &[u32],
                neg: &[u32],
                avoid_cnt: &[u32],
                used_cnt: &[u32],
                skip_ty: Option<usize>|
     -> Option<usize> {
        let mut again: Option<usize> = None;
        if let Some(&p0) = pos.iter().min_by_key(|&&p| vals.by_atom.get(&p).map_or(0, |v| v.len())) {
            let Some(ixs) = vals.by_atom.get(&p0) else { return None };
            for &idx in ixs {
                let avoid_hit = if Some(idx) == skip_ty && vals.is_oneof_by_idx[idx] {
                    avoid_cnt[idx] > 1
                } else {
                    avoid_cnt[idx] > 0
                };
                if avoid_hit {
                    continue;
                }
                let ty = &vals.distinct_types[idx];
                if fits(label, ty, pos, neg) {
                    let used_hit = if Some(idx) == skip_ty { used_cnt[idx] > 1 } else { used_cnt[idx] > 0 };
                    if !used_hit {
                        return Some(idx);
                    }
                    if again.is_none() {
                        again = Some(idx);
                    }
                }
            }
            return again;
        }
        for (idx, ty) in vals.distinct_types.iter().enumerate() {
            let avoid_hit = if Some(idx) == skip_ty && vals.is_oneof_by_idx[idx] {
                avoid_cnt[idx] > 1
            } else {
                avoid_cnt[idx] > 0
            };
            if avoid_hit {
                continue;
            }
            if fits(label, ty, pos, neg) {
                let used_hit = if Some(idx) == skip_ty { used_cnt[idx] > 1 } else { used_cnt[idx] > 0 };
                if !used_hit {
                    return Some(idx);
                }
                if again.is_none() {
                    again = Some(idx);
                }
            }
        }
        again
    };
    let mut ents: Vec<Entry> = Vec::new();
    if reqs.len() > 1 {
        reqs.sort_by_key(|(n, _u, pos, _neg)| {
            let m = pos
                .iter()
                .map(|p| vals.by_atom.get(p).map_or(usize::MAX, |v| v.len()))
                .min()
                .unwrap_or(usize::MAX);
            (m, *n)
        });
    }
    let cnt = |ents: &[Entry], u: u32, pos: &[u32], neg: &[u32]| -> u32 {
        ents.iter()
            .filter(|e| has(&e.label, u) && pos.iter().all(|p| has(&e.ty, *p)) && !neg.iter().any(|n| has(&e.ty, *n)))
            .count() as u32
    };
    for (n, u, pos, neg) in &reqs {
        while cnt(&ents, *u, pos, neg) < *n {
            let lu = up(*u);
            // extend an existing entry whose value already fits or can be refined
            let mut done = false;
            if *n == 1 {
                for idx in 0..ents.len() {
                    let old_ti = ents[idx].ty_idx;
                    if (share || vals.fcard_by_idx[old_ti].is_some())
                        && pos.iter().all(|p| has(&ents[idx].ty, *p))
                        && !neg.iter().any(|n| has(&ents[idx].ty, *n))
                    {
                        let mut l2 = ents[idx].label.clone();
                        l2.extend_from_slice(&lu);
                        l2.sort_unstable();
                        l2.dedup();
                        if fits(&l2, &ents[idx].ty, pos, neg)
                            && fits(&l2, &ents[idx].ty, &ents[idx].pos, &ents[idx].neg)
                        {
                            ents[idx].label = l2;
                            ents[idx].pos.extend_from_slice(pos);
                            ents[idx].neg.extend_from_slice(neg);
                            done = true;
                            break;
                        }
                    }
                    if share && !d.datmost.is_empty() {
                        let mut l2 = ents[idx].label.clone();
                        l2.extend_from_slice(&lu);
                        l2.sort_unstable();
                        l2.dedup();
                        let mut p2 = ents[idx].pos.clone();
                        p2.extend_from_slice(pos);
                        let mut n2 = ents[idx].neg.clone();
                        n2.extend_from_slice(neg);
                        if let Some(new_ti) = pick(&l2, &p2, &n2, &avoid_cnt, &used_cnt, Some(old_ti)) {
                            used_cnt[old_ti] -= 1;
                            if vals.is_oneof_by_idx[old_ti] {
                                avoid_cnt[old_ti] -= 1;
                            }
                            used_cnt[new_ti] += 1;
                            if vals.is_oneof_by_idx[new_ti] {
                                avoid_cnt[new_ti] += 1;
                            }
                            ents[idx].label = l2;
                            ents[idx].ty = vals.distinct_types[new_ti].clone();
                            ents[idx].ty_idx = new_ti;
                            ents[idx].pos = p2;
                            ents[idx].neg = n2;
                            done = true;
                            break;
                        }
                    }
                }
            }
            if done {
                continue;
            }
            let Some(ti) = pick(&lu, pos, neg, &avoid_cnt, &used_cnt, None) else {
                if std::env::var("KM_HINTS_DEBUG").is_ok() {
                    eprintln!("dstar: no value for u {} pos {:?} neg {:?}; {} candidates, {} understood",
                        u, pos, neg, vals.types.len(), vals.types.iter().flatten().count());
                }
                return None;
            };
            used_cnt[ti] += 1;
            if vals.is_oneof_by_idx[ti] {
                avoid_cnt[ti] += 1;
            }
            ents.push(Entry {
                label: lu,
                ty: vals.distinct_types[ti].clone(),
                ty_idx: ti,
                pos: pos.clone(),
                neg: neg.clone(),
            });
        }
    }
    // finite value types (only booleans or oneOf literals have them among the
    // candidates): at most as many entries as values
    for (ti, &n) in used_cnt.iter().enumerate() {
        if n > 0 {
            if let Some(k) = vals.fcard_by_idx[ti] {
                if n as usize > k {
                    if std::env::var("KM_HINTS_DEBUG").is_ok() {
                        eprintln!("dstar: {} entries of a value type with {} values", n, k);
                    }
                    return None;
                }
            }
        }
    }
    for &a in t {
        if let Some(ixs) = d.datmost_by.get(&a) {
            for &i in ixs {
                let c = &d.datmost[i];
                if cnt(&ents, c.2, &c.3, &c.4) > c.1 {
                    if std::env::var("KM_HINTS_DEBUG").is_ok() {
                        eprintln!("dstar: at-most {:?} exceeded", c);
                    }
                    return None;
                }
            }
        }
    }
    Some(ents)
}
