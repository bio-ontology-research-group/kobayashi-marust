//! `elc`: EL++ completion fast path.
//!
//! Reads `{"clauses":[...]}` on stdin (the same contract the disjunctive context
//! engine binary takes) and, if the clause set lies in EL++, classifies it with
//! the ELK-style completion in `kobayashi_marust::elcomplete` and prints
//! `{"subsumptions":{...}, "inconsistent":<bool>, "dropped":0}`. If the ontology
//! is *not* EL++ it exits with code 3 so the caller falls back to the context
//! engine — exactly mirroring `engine/py/el_route.py`'s `__main__`, but compiled
//! so the large EL ontologies that time out in Python classify in seconds.

use std::io::Read;
use std::process::exit;

use kobayashi_marust::elcomplete;
use kobayashi_marust::json_io::JInput;

#[derive(serde::Serialize)]
struct Output {
    subsumptions: std::collections::BTreeMap<String, Vec<String>>,
    inconsistent: bool,
    dropped: usize,
}

fn main() {
    let mut buf = String::new();
    if let Err(e) = std::io::stdin().read_to_string(&mut buf) {
        eprintln!("failed to read stdin: {}", e);
        exit(1);
    }
    let input: JInput = match serde_json::from_str(&buf) {
        Ok(i) => i,
        Err(e) => {
            eprintln!("bad input JSON: {}", e);
            exit(1);
        }
    };
    match elcomplete::classify(&input.clauses) {
        Some(res) => {
            let out = Output {
                subsumptions: res.subsumptions,
                inconsistent: res.inconsistent,
                dropped: 0,
            };
            let stdout = std::io::stdout();
            let mut w = std::io::BufWriter::new(stdout.lock());
            if let Err(e) = serde_json::to_writer(&mut w, &out) {
                eprintln!("serialise error: {}", e);
                exit(1);
            }
            use std::io::Write;
            let _ = w.flush();
        }
        // not EL++: caller must use the disjunctive context engine.
        None => exit(3),
    }
}
