//! km's answer rows (`km classify --lines --realize --top`).

use std::collections::{HashMap, HashSet};

pub const THING: &str = "http://www.w3.org/2002/07/owl#Thing";
pub const NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";

#[derive(Default)]
pub struct Km {
    pub consistent: Option<bool>,
    pub dropped: u64,
    pub sup: HashMap<String, HashSet<String>>,
    pub unsat: HashSet<String>,
    pub types: HashMap<String, HashSet<String>>,
    pub same: Vec<(String, String)>,
    pub top: HashSet<String>,
}

impl Km {
    pub fn parse(text: &str) -> Km {
        let mut k = Km::default();
        for line in text.lines() {
            let w: Vec<&str> = line.split('\t').collect();
            let h = w[0];
            if h.starts_with("CONSISTENT") {
                k.consistent = Some(h.split_whitespace().last() == Some("1"));
            } else if h.starts_with("DROPPED") {
                k.dropped = h.split_whitespace().last().and_then(|x| x.parse().ok()).unwrap_or(0);
            } else if w.len() >= 3 && h == "SUB" {
                k.sup.entry(w[1].to_string()).or_default().insert(w[2].to_string());
            } else if w.len() >= 2 && h == "UNSAT" {
                k.unsat.insert(w[1].to_string());
            } else if w.len() >= 3 && h == "TYPE" {
                k.types.entry(w[1].to_string()).or_default().insert(w[2].to_string());
            } else if w.len() >= 3 && h == "SAME" {
                k.same.push((w[1].to_string(), w[2].to_string()));
            } else if w.len() >= 2 && h == "TOP" {
                k.top.insert(w[1].to_string());
            }
        }
        k
    }
}
