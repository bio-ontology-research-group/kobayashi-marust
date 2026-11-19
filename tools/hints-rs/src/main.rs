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
        no_realize: a.iter().any(|x| x == "--no-realize"),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{Elem, Engine, Model, Opts, NONE};

    fn test_cfg() -> build::Config {
        build::Config {
            max_models: 4,
            retries: 4,
            split_cap: 32,
            unsat_checks: 10,
            time_limit: 10.0,
            loops: true,
            write: false,
            no_realize: false,
            data: None,
        }
    }

    #[test]
    fn test_nominal_placement_and_grouping() {
        let idx = "\
concepts 4
roles 1
concept 0 http://ex/A
concept 1 http://ex/B
concept 2 urn:km:nom:ind1
concept 3 urn:km:nom:ind2
role 0 http://ex/r
nominal 2 http://ex/ind1
nominal 3 http://ex/ind2
";
        // Nominal 2 implies Nominal 3 via 1-to-1 GCI (`gci 2 -> 3`), and ind1 has type A
        let cl = "\
nom 2
nom 3
gci 2 -> 3
gci 2 -> 0
some 0 +0 1
";
        let km_txt = "\
CONSISTENT 1
SUB\thttp://ex/A\thttp://ex/A
SUB\thttp://ex/B\thttp://ex/B
TYPE\thttp://ex/ind1\thttp://ex/A
TYPE\thttp://ex/ind2\thttp://ex/A
";
        let nf = nf::Nf::parse(idx, cl).expect("parse nf");
        let km = km::Km::parse(km_txt);
        let cfg = test_cfg();
        let mut checked_ok = false;
        let out = build::produce(
            &nf,
            &km,
            &cfg,
            "",
            Some(&mut |en, slots, verified| {
                assert!(!slots.is_empty());
                assert_eq!(verified[0].0, 0, "base model must have 0 violations");
                let m = &slots[0].m;
                let e2 = m.find(*m.nom_elem.get(&2).expect("nom 2 placed"));
                let e3 = m.find(*m.nom_elem.get(&3).expect("nom 3 placed"));
                assert_eq!(e2, e3, "nominals linked by gci 2 -> 3 must share canonical element");
                assert!(en.sets.has(m.elems[e2 as usize].ty, 0), "ind1/ind2 element must have class A");
                checked_ok = true;
            }),
        );
        assert!(checked_ok);
        assert!(out.contains("\"ok\":true"), "produce output: {}", out);
    }

    #[test]
    fn test_anonymous_individual_mapping() {
        let idx = "\
concepts 4
roles 1
concept 0 http://ex/Person
concept 1 urn:km:owl-anon:#genid1
concept 2 urn:km:owl-anon:b0
concept 3 urn:km:owl-anon:#anon2
role 0 http://ex/knows
nominal 1 urn:km:owl-anon:#genid1
nominal 2 urn:km:owl-anon:b0
nominal 3 urn:km:owl-anon:#anon2
";
        let cl = "\
nom 1
nom 2
nom 3
gci 1 -> 0
some 1 +0 2
";
        let km_txt = "\
CONSISTENT 1
SUB\thttp://ex/Person\thttp://ex/Person
";
        let export_jsonl = "\
{\"kind\":\"model\",\"route\":\"tableaux\",\"status\":\"ok\"}
{\"kind\":\"element\",\"id\":\"e0\",\"classes\":[\"http://ex/Person\"],\"individuals\":[\"_:genid1\"]}
{\"kind\":\"element\",\"id\":\"e1\",\"classes\":[],\"individuals\":[\"_:b0\",\"#anon2\"]}
{\"kind\":\"edge\",\"from\":\"e0\",\"role\":\"http://ex/knows\",\"to\":\"e1\"}
{\"kind\":\"witness\",\"class\":\"http://ex/Person\",\"element\":\"e0\",\"exact\":true}
";
        let nf = nf::Nf::parse(idx, cl).expect("parse nf");
        let km = km::Km::parse(km_txt);
        let cfg = test_cfg();
        let res = export::from_export(&nf, Some(&km), &cfg, export_jsonl, "");
        assert!(res.contains("\"ok\":true"), "from_export failed: {}", res);
        assert!(res.contains("\"violations\":0"), "from_export had violations: {}", res);
    }

    #[test]
    fn test_data_value_cells_and_whitespace_restrictions() {
        let cl = "\
atom 0 (ContextCalculus.OWL.DataRange.restriction      \"http://www.w3.org/2001/XMLSchema#double\" [(\"http://www.w3.org/2001/XMLSchema#minInclusive\", { lexical :=      \"10.5\", datatype := \"http://www.w3.org/2001/XMLSchema#double\", lang := none })])
atom 1 (ContextCalculus.OWL.DataRange.restriction      \"http://www.w3.org/2001/XMLSchema#double\" [(\"http://www.w3.org/2001/XMLSchema#maxInclusive\", { lexical := \"5.0\", datatype := \"http://www.w3.org/2001/XMLSchema#double\", lang := none })])
atom 2 (ContextCalculus.OWL.DataRange.restriction      \"http://www.w3.org/2001/XMLSchema#double\" [(\"http://www.w3.org/2001/XMLSchema#maxInclusive\", { lexical := \"20.0\", datatype := \"http://www.w3.org/2001/XMLSchema#double\", lang := none })])
atom 3 (ContextCalculus.OWL.DataRange.datatype \"http://www.w3.org/2001/XMLSchema#boolean\")
atom 4 (ContextCalculus.OWL.DataRange.oneOf [{ lexical := \"true\", datatype := \"http://www.w3.org/2001/XMLSchema#boolean\", lang := none }])
dsome 0 0 0 /
dall 1 0 1
dall 2 0 2
dsome 3 1 3 /
dsome 4 1 3 / 4
dall 5 1 4
data-clauses 6
";
        let d = data::DataNf::parse(cl);
        assert!(!d.is_empty(), "DataNf should parse data clauses");
        let v = data::Values::new(&d);
        assert!(v.complete(), "Values should be complete for xsd:double + xsd:boolean");
        // [0, 2] requires a double in [10.5, 20.0] -> satisfiable
        let star_ok = data::star(&d, &v, &[0, 2]);
        assert!(star_ok.is_some(), "double in [10.5, 20.0] must have a data star");
        // [0, 1] requires a double >= 10.5 and <= 5.0 -> unsatisfiable
        let star_conflict = data::star(&d, &v, &[0, 1]);
        assert!(star_conflict.is_none(), "double >= 10.5 and <= 5.0 must have no data star");
        // [3, 4] requires boolean != true (i.e. false) -> satisfiable
        assert!(data::star(&d, &v, &[3, 4]).is_some(), "boolean false cell must be satisfiable");
        // [4, 5] requires boolean != true and in {true} -> unsatisfiable
        assert!(data::star(&d, &v, &[4, 5]).is_none(), "conflicting boolean oneOf cell must fail");
    }

    #[test]
    fn test_split_witness_intersection() {
        let idx = "\
concepts 3
roles 0
concept 0 http://ex/A
concept 1 http://ex/B
concept 2 http://ex/C
";
        // A -> B | C, so no single element can have A without either B or C,
        // but neither B nor C is a superclass of A. Two split witnesses (one with {A, B}
        // and one with {A, C}) intersect to {A}, certifying both nonsub(A, B) and nonsub(A, C).
        let cl = "\
gci 0 -> 1 2
";
        let km_txt = "\
CONSISTENT 1
SUB\thttp://ex/A\thttp://ex/A
SUB\thttp://ex/B\thttp://ex/B
SUB\thttp://ex/C\thttp://ex/C
";
        let nf = nf::Nf::parse(idx, cl).expect("parse nf");
        let km = km::Km::parse(km_txt);
        let cfg = test_cfg();
        let out = build::produce(&nf, &km, &cfg, "", None);
        assert!(out.contains("\"uncovered\":{\"rows\":0,"), "all nonsub rows must be covered: {}", out);
        assert!(out.contains("\"split\":1"), "class A must be certified by split witnesses: {}", out);
    }

    #[test]
    fn test_rejected_hint_fails_verify() {
        let idx = "\
concepts 3
roles 1
concept 0 http://ex/A
concept 1 http://ex/B
concept 2 urn:km:nom:a
role 0 http://ex/r
nominal 2 http://ex/a
";
        let cl = "\
nom 2
gci 0 -> 1
some 1 +0 0
";
        let nf = nf::Nf::parse(idx, cl).expect("parse nf");
        let mut en = Engine::new(&nf, Opts::default());
        let mut m = Model::new();
        // Create an element with A (0) and nom 2, but missing B (1) (violates `gci 0 -> 1`)
        let bad_ty = en.sets.intern(vec![0, 2]);
        let el = m.push_elem(Elem {
            ty: bad_ty,
            forced: bad_ty,
            forbid: 0,
            target: bad_ty,
            edges: Vec::new(),
            pending: Vec::new(),
            nom: true,
            pinned: true,
            owner: NONE,
            alive: true,
        });
        m.set_nom(2, el);
        let rep = check::verify(&mut en, &m);
        assert!(rep.violations > 0, "hint violating GCI 0 -> 1 must be rejected by check::verify");
        assert!(
            rep.first.as_deref().unwrap_or("").contains("gci"),
            "first violation should report GCI failure: {:?}",
            rep.first
        );

        // Now add B (1) to fix the GCI, but leave `some 1 +0 0` unmet (no outgoing +0 edge)
        let ty_with_b = en.sets.intern(vec![0, 1, 2]);
        m.em(el).ty = ty_with_b;
        let rep2 = check::verify(&mut en, &m);
        assert!(rep2.violations > 0, "hint with unmet existential must be rejected by check::verify");
        assert!(
            rep2.first.as_deref().unwrap_or("").contains("existential"),
            "first violation should report unmet existential: {:?}",
            rep2.first
        );
    }
}

