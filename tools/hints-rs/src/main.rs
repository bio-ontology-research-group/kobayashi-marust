//! km-hints: an untrusted producer of global models for km's negative
//! answers (stage H3). See `tools/hints-rs/README` in the design note
//! `docs/V1.7.0-H3-PRODUCER.md`.
//!
//! ```text
//! km-hints produce --index IDX --clauses CL --km LINES --out DIR [--time S]
//!                  [--max-models K] [--no-loops] [--unsat-checks N] [--no-write]
//! km-hints rowhint --index IDX --clauses CL --km LINES --row-index RIDX
//!                  --row-clauses RCL --class IRI --out HINT [--time S]
//! ```

mod build;
mod check;
mod data;
mod emit;
mod engine;
mod export;
mod km;
mod nf;
mod rowmap;

use std::process::exit;

fn arg(a: &[String], k: &str) -> Option<String> {
    a.iter().position(|x| x == k).and_then(|i| a.get(i + 1)).cloned()
}

fn read(p: &str) -> String {
    match std::fs::read_to_string(p) {
        Ok(s) => s,
        Err(e) => {
            let msg = format!("cannot read {}: {}", p, e).replace('"', "'");
            println!("{{\"ok\":false,\"why\":\"{}\",\"reason\":\"{}\"}}", msg, msg);
            eprintln!("km-hints: {}", msg);
            exit(2)
        }
    }
}

fn load_nf(idx: &str, cl: &str) -> nf::Nf {
    match nf::Nf::parse(&read(idx), &read(cl)) {
        Ok(n) => n,
        Err(e) => {
            let msg = format!("{}", e).replace('"', "'");
            println!("{{\"ok\":false,\"why\":\"{}\",\"reason\":\"{}\"}}", msg, msg);
            eprintln!("km-hints: {}", msg);
            exit(2)
        }
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 2 {
        println!("{{\"ok\":false,\"why\":\"missing subcommand\",\"reason\":\"missing subcommand\"}}");
        eprintln!("usage: km-hints produce|from-export|rowhint ...");
        exit(2);
    }
    let need = |k: &str| {
        arg(&a, k).unwrap_or_else(|| {
            println!("{{\"ok\":false,\"why\":\"missing {}\",\"reason\":\"missing {}\"}}", k, k);
            eprintln!("km-hints: missing {}", k);
            exit(2)
        })
    };
    let default_time = if a.get(1).map(String::as_str) == Some("from-export") { 120.0 } else { 600.0 };
    let time: f64 = arg(&a, "--time").and_then(|s| s.parse().ok()).unwrap_or(default_time);
    let cfg = build::Config {
        max_models: arg(&a, "--max-models").and_then(|s| s.parse().ok()).unwrap_or(4),
        retries: arg(&a, "--retries").and_then(|s| s.parse().ok()).unwrap_or(6),
        split_cap: arg(&a, "--split-cap").and_then(|s| s.parse().ok()).unwrap_or(64),
        unsat_checks: arg(&a, "--unsat-checks").and_then(|s| s.parse().ok()).unwrap_or(200),
        time_limit: time,
        loops: !a.iter().any(|x| x == "--no-loops"),
        write: !a.iter().any(|x| x == "--no-write"),
        data: None,
    };
    match a[1].as_str() {
        "produce" => {
            let t0 = std::time::Instant::now();
            let nf = load_nf(&need("--index"), &need("--clauses"));
            let km = km::Km::parse(&read(&need("--km")));
            let mut cfg = cfg;
            if !a.iter().any(|x| x == "--no-dstar") {
                let d = data::DataNf::parse(&read(&need("--clauses")));
                if !d.is_empty() {
                    cfg.data = Some(d);
                }
            }
            let parse = t0.elapsed().as_secs_f64();
            let out = need("--out");
            let _ = std::fs::create_dir_all(&out);
            let j = build::produce(&nf, &km, &cfg, &out, None);
            let j = format!("{{\"parse_secs\":{:.3},{}", parse, &j[1..]);
            let _ = std::fs::write(format!("{}/producer.json", out), &j);
            println!("{}", j);
        }
        "from-export" => {
            let nf = load_nf(&need("--index"), &need("--clauses"));
            let km = arg(&a, "--km").map(|p| km::Km::parse(&read(&p)));
            let exp_text = read(&need("--export"));
            let mut cfg = cfg;
            if !a.iter().any(|x| x == "--no-dstar") {
                let d = data::DataNf::parse(&read(&need("--clauses")));
                if !d.is_empty() {
                    cfg.data = Some(d);
                }
            }
            let out = need("--out");
            let _ = std::fs::create_dir_all(&out);
            let j = export::from_export(&nf, km.as_ref(), &cfg, &exp_text, &out);
            let _ = std::fs::write(format!("{}/export_producer.json", out), &j);
            println!("{}", j);
        }
        "rowhint" => {
            let nf = load_nf(&need("--index"), &need("--clauses"));
            let rnf = load_nf(&need("--row-index"), &need("--row-clauses"));
            let km = km::Km::parse(&read(&need("--km")));
            let class = arg(&a, "--class");
            let ind = arg(&a, "--individual");
            let out = need("--out");
            let mut cfg = cfg;
            cfg.write = false;
            match rowmap::row_hint(&nf, &rnf, &km, &cfg, class.as_deref(), ind.as_deref(), &out) {
                Ok(msg) => println!("{}", msg),
                Err(e) => {
                    println!("{{\"ok\":false,\"why\":\"{}\"}}", e.replace('"', "'"));
                    exit(3)
                }
            }
        }
        "startype" => {
            // debug: the data star of one type (names on the command line after --type)
            let d = data::DataNf::parse(&read(&need("--clauses")));
            let v = data::Values::new(&d);
            let i = a.iter().position(|x| x == "--type").map(|i| i + 1).unwrap_or(a.len());
            let mut t: Vec<u32> = a[i..].iter().filter_map(|x| x.parse().ok()).collect();
            t.sort_unstable();
            std::env::set_var("KM_HINTS_DEBUG", "1");
            match data::star(&d, &v, &t) {
                Some(es) => {
                    for e in es {
                        println!("entry {:?} / {:?}", e.label, e.ty);
                    }
                }
                None => println!("no star"),
            }
        }
        _ => {
            let msg = format!("unknown command {}", a[1]).replace('"', "'");
            println!("{{\"ok\":false,\"why\":\"{}\",\"reason\":\"{}\"}}", msg, msg);
            eprintln!("km-hints: {}", msg);
            exit(2)
        }
    }
}
