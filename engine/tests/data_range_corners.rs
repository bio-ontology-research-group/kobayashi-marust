//! The data-range corners of docs/DATATYPES.md ("Boolean data ranges and
//! ordered cells", "Open corners"): every probe is either answered exactly
//! as HermiT answers it, or published as not represented (`DROPPED`) or
//! refused, never answered wrongly.
//!
//! Each fixture in `fixtures/data_range_corners/` has its HermiT answer next
//! to it (`<name>.json`). `exact` fixtures must be answered with that answer
//! and `DROPPED 0` on the automatic route and on the two nominal routes;
//! `declined` fixtures must be published with `DROPPED > 0` or refused
//! (exit 3) on every route, unless the answer is an inconsistency, which the
//! sound abstraction may publish next to `DROPPED`.
use std::collections::BTreeSet;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(120);
static NEXT: AtomicUsize = AtomicUsize::new(0);
const ROUTES: [Option<&str>; 3] = [None, Some("certified_nominals"), Some("nominals")];

#[derive(Debug, PartialEq, Eq, Clone)]
struct Answer {
    consistent: bool,
    unsat: BTreeSet<String>,
    subs: BTreeSet<(String, String)>,
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Answer(Answer),
    Dropped(Answer),
    Refused,
}

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/data_range_corners")
}

fn strip(name: &str) -> String {
    name.trim_start_matches(':').rsplit('#').next().unwrap().to_string()
}

fn normal(mut answer: Answer) -> Answer {
    if !answer.consistent {
        answer.unsat.clear();
        answer.subs.clear();
    }
    let unsat = answer.unsat.clone();
    answer.subs.retain(|(a, b)| a != b && !unsat.contains(a) && !unsat.contains(b));
    answer
}

fn expected(name: &str) -> Answer {
    let text = std::fs::read_to_string(fixtures().join(format!("{name}.json"))).unwrap();
    let value: serde_json::Value = serde_json::from_str(&text).unwrap();
    normal(Answer {
        consistent: value["consistent"].as_bool().unwrap(),
        unsat: value["unsatisfiable"].as_array().unwrap().iter().map(|v| strip(v.as_str().unwrap())).collect(),
        subs: value["subsumptions"].as_array().unwrap().iter()
            .map(|p| (strip(p[0].as_str().unwrap()), strip(p[1].as_str().unwrap()))).collect(),
    })
}

fn classify(name: &str, route: Option<&str>) -> Outcome {
    let path = fixtures().join(format!("{name}.ofn"));
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    let scratch = std::env::temp_dir().join(format!("km-dr-corners-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::create_dir_all(&scratch).unwrap();
    command.env("KM_THREADS", "1").env("TMPDIR", &scratch);
    command.args(["classify", "--lines"]).arg(&path).stdout(Stdio::piped()).stderr(Stdio::piped());
    let started = Instant::now();
    let mut child = command.spawn().unwrap();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            let _ = std::fs::remove_dir_all(&scratch);
            panic!("{name} on {route:?}: timeout");
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let _ = std::fs::remove_dir_all(&scratch);
    let mut stdout = String::new();
    child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
    if status.code() == Some(3) {
        return Outcome::Refused;
    }
    assert!(status.success(), "{name} on {route:?}: exit {:?}", status.code());
    let mut answer = Answer { consistent: true, unsat: BTreeSet::new(), subs: BTreeSet::new() };
    let mut dropped = 0u64;
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [first] if first.starts_with("CONSISTENT") => answer.consistent = first.ends_with('1'),
            [first] if first.starts_with("DROPPED") => dropped = first.split_whitespace().last().unwrap().parse().unwrap(),
            ["SUB", a, b] => { answer.subs.insert((strip(a), strip(b))); }
            ["UNSAT", a] => { answer.unsat.insert(strip(a)); }
            _ => {}
        }
    }
    let answer = normal(answer);
    if dropped > 0 { Outcome::Dropped(answer) } else { Outcome::Answer(answer) }
}

fn exact(name: &str) {
    let want = expected(name);
    for route in ROUTES {
        assert_eq!(classify(name, route), Outcome::Answer(want.clone()), "{name} on {route:?}");
    }
}

fn declined(name: &str) {
    let want = expected(name);
    for route in ROUTES {
        match classify(name, route) {
            Outcome::Refused => {}
            // A published inconsistency is sound under the abstraction; it
            // must agree with HermiT.
            Outcome::Dropped(answer) | Outcome::Answer(answer) if !answer.consistent =>
                assert!(!want.consistent, "{name} on {route:?}: inconsistency against HermiT"),
            Outcome::Dropped(_) => {}
            Outcome::Answer(answer) => panic!("{name} on {route:?}: answered without DROPPED: {answer:?}"),
        }
    }
}

macro_rules! exact { ($($test:ident),* $(,)?) => { $( #[test] fn $test() { exact(stringify!($test)); } )* }; }
macro_rules! declined { ($($test:ident),* $(,)?) => { $( #[test] fn $test() { declined(stringify!($test)); } )* }; }

// Boolean structure and ordered cells.
exact!(cell_exhaust_tbox, bool_cell_equiv, bool_union_exhaust, bool_complement_dense,
    bool_complement_top, bool_intersection_abox, bool_intersection_empty, atomic_helly,
    dense_point, float_cells, float_complement, int_cell_exhaust, union_complex, count_complex,
    decimal_mixed_ok, dense_count);
// Named datatypes of the map: decimal/IEEE separation, the string chain,
// rdf:PlainLiteral, dateTimeStamp, the binary types, dateTime identity.
exact!(float_decimal, float_value_decimal, integer_double_sub, plain_literal, datetime_stamp,
    binary_disjoint, datetime_offset);
// HermiT answers `xsd:language ⊓ ¬xsd:NCName` satisfiable; under XSD 1.1
// every language tag is an NCName. The fixture records the datatype-map
// answer (`A` unsatisfiable).
exact!(string_chain);
// Pattern, length and dateTime facets: outside the decided fragment.
declined!(length_empty, length_exhaust, length_value, pattern_value, pattern_subsumption,
    datetime_empty, datetime_value, datetime_subsumption);
// HasKey over data properties: refused (lowered to rules whose data atoms
// fail closed).
declined!(haskey_data, haskey_data_ok);
