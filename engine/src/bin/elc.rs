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
use std::time::Instant;

use kobayashi_marust::elcomplete;
use kobayashi_marust::json_io::JInput;

#[derive(serde::Serialize)]
struct Output {
    subsumptions: std::collections::BTreeMap<String, Vec<String>>,
    inconsistent: bool,
    dropped: usize,
}

fn main() {
    // Read the (up to ~750 MB on the ORE giants) clause JSON as raw bytes and
    // parse with `from_slice`: this skips the full-buffer UTF-8 validation that
    // `read_to_string` performs and avoids a second allocation, shaving wall
    // time on the large EL ontologies that classify right at the benchmark
    // timeout (ore_ont_8737: elc ~248 s, just over 240 s).
    let timing = std::env::var("KM_ELC_TIMING").is_ok();
    let t0 = Instant::now();
    let mut buf: Vec<u8> = Vec::new();
    if let Err(e) = std::io::stdin().lock().read_to_end(&mut buf) {
        eprintln!("failed to read stdin: {}", e);
        exit(1);
    }
    if timing {
        eprintln!("KM_ELC_TIMING read={:.2}s ({} MB)", t0.elapsed().as_secs_f64(), buf.len() >> 20);
    }
    let t1 = Instant::now();
    let input: JInput = match serde_json::from_slice(&buf) {
        Ok(i) => i,
        Err(e) => {
            eprintln!("bad input JSON: {}", e);
            exit(1);
        }
    };
    drop(buf);
    if timing {
        eprintln!("KM_ELC_TIMING parse={:.2}s ({} clauses)", t1.elapsed().as_secs_f64(), input.clauses.len());
    }
    let t2 = Instant::now();
    match elcomplete::classify(&input.clauses) {
        Some(res) => {
            if timing {
                eprintln!("KM_ELC_TIMING classify={:.2}s ({} subjects)", t2.elapsed().as_secs_f64(), res.subsumptions.len());
            }
            let t3 = Instant::now();
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
            if timing {
                eprintln!("KM_ELC_TIMING serialise={:.2}s total={:.2}s", t3.elapsed().as_secs_f64(), t0.elapsed().as_secs_f64());
            }
        }
        // not EL++: caller must use the disjunctive context engine.
        None => exit(3),
    }
}
