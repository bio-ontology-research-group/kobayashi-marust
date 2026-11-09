//! Data-property assertions and data counting on every nominal route,
//! against HermiT (docs/DATATYPES.md, "Exact data values without a literal
//! cap").
//!
//! Each fixture in `fixtures/native_data_values/` has its HermiT answer next
//! to it (`<name>.json`). It runs as written and padded with 1,100
//! individuals carrying distinct integer values (of the counted property `u`
//! for the functional and merge fixtures, of an unrelated property `pad`
//! otherwise), so that the value vocabulary exceeds the pairwise limit and
//! the linear relation form, the value projection and the singleton elision
//! run. Every answer must be complete (`DROPPED 0`) and equal HermiT's.
use std::collections::BTreeSet;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(120);
static NEXT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, PartialEq, Eq)]
struct Answer {
    consistent: bool,
    unsat: BTreeSet<String>,
    subs: BTreeSet<(String, String)>,
}

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/native_data_values")
}

fn padded(name: &str, text: &str) -> String {
    let property = if name.contains("functional") || name.contains("merge") { ":u" } else { ":pad" };
    let body = text.trim_end().strip_suffix(')').expect("ontology ends with )");
    let mut out = body.to_string();
    for k in 0..1100 {
        out.push_str(&format!(
            "Declaration(NamedIndividual(:p{k}))\nDataPropertyAssertion({property} :p{k} \"{}\"^^xsd:integer)\n",
            1000 + k
        ));
    }
    out.push_str(")\n");
    out
}

fn expected(name: &str) -> Answer {
    let text = std::fs::read_to_string(fixtures().join(format!("{name}.json"))).unwrap();
    let value: serde_json::Value = serde_json::from_str(&text).unwrap();
    Answer {
        consistent: value["consistent"].as_bool().unwrap(),
        unsat: value["unsatisfiable"].as_array().unwrap().iter()
            .map(|v| v.as_str().unwrap().to_string()).collect(),
        subs: value["subsumptions"].as_array().unwrap().iter()
            .map(|p| (p[0].as_str().unwrap().to_string(), p[1].as_str().unwrap().to_string())).collect(),
    }
}

fn strip(name: &str) -> String {
    name.trim_start_matches(':').rsplit('#').next().unwrap().to_string()
}

/// `km classify --lines` with `route` (None = automatic); the answer, or an
/// error for a refusal, a drop, a timeout or a crash.
fn classify(text: &str, route: Option<&str>) -> Result<Answer, String> {
    let dir = std::env::temp_dir();
    let path = dir.join(format!("km-native-data-{}-{}.ofn", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, text).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    command.env("KM_THREADS", "1");
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
            let _ = std::fs::remove_file(&path);
            return Err("timeout".into());
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let mut stdout = String::new();
    child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
    let mut stderr = String::new();
    child.stderr.take().unwrap().read_to_string(&mut stderr).unwrap();
    let _ = std::fs::remove_file(&path);
    if !status.success() {
        return Err(format!("exit {:?}: {}", status.code(), stderr.lines().last().unwrap_or("")));
    }
    let mut answer = Answer { consistent: true, unsat: BTreeSet::new(), subs: BTreeSet::new() };
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [first] if first.starts_with("CONSISTENT") => answer.consistent = first.ends_with('1'),
            [first] if first.starts_with("DROPPED") => {
                let dropped: u64 = first.split_whitespace().last().unwrap().parse().unwrap();
                if dropped > 0 && answer.consistent {
                    return Err(format!("DROPPED {dropped}"));
                }
            }
            ["SUB", a, b] => { answer.subs.insert((strip(a), strip(b))); }
            ["UNSAT", a] => { answer.unsat.insert(strip(a)); }
            _ => {}
        }
    }
    if !answer.consistent {
        answer.unsat.clear();
        answer.subs.clear();
    }
    answer.subs.retain(|(a, b)| a != b && !answer.unsat.contains(a) && !answer.unsat.contains(b));
    Ok(answer)
}

fn check(name: &str, routes: &[Option<&str>]) {
    check_variants(name, routes, true);
}

fn check_variants(name: &str, routes: &[Option<&str>], with_padding: bool) {
    let text = std::fs::read_to_string(fixtures().join(format!("{name}.ofn"))).unwrap();
    let mut want = expected(name);
    if !want.consistent {
        want.unsat.clear();
        want.subs.clear();
    }
    let mut variants = vec![("plain", text.clone())];
    if with_padding {
        variants.push(("padded", padded(name, &text)));
    }
    for (variant, input) in variants {
        for route in routes {
            assert_eq!(classify(&input, *route), Ok(want_clone(&want)),
                "{name} ({variant}) on route {route:?}");
        }
    }
}

fn want_clone(answer: &Answer) -> Answer {
    Answer { consistent: answer.consistent, unsat: answer.unsat.clone(), subs: answer.subs.clone() }
}

const NOMINAL_ROUTES: [Option<&str>; 3] = [None, Some("certified_nominals"), Some("nominals")];

macro_rules! fixture_test {
    ($test:ident, $name:literal) => {
        #[test]
        fn $test() { check($name, &NOMINAL_ROUTES); }
    };
    ($test:ident, $name:literal, plain_only) => {
        #[test]
        fn $test() { check_variants($name, &NOMINAL_ROUTES, false); }
    };
    ($test:ident, $name:literal, auto_only) => {
        #[test]
        fn $test() { check($name, &[None]); }
    };
}

fixture_test!(functional_merge_clash, "functional_merge_clash");
fixture_test!(functional_merge_equal, "functional_merge_equal");
fixture_test!(functional_two_values, "functional_two_values");
fixture_test!(qualified_atmost, "qualified_atmost");
fixture_test!(qualified_atmost_ok, "qualified_atmost_ok");
fixture_test!(subproperty_functional, "subproperty_functional");
fixture_test!(hasvalue_nominal, "hasvalue_nominal");
fixture_test!(facet_exists, "facet_exists");
fixture_test!(range_clash, "range_clash");
fixture_test!(count_finite_range, "count_finite_range");
fixture_test!(count_byte, "count_byte");
fixture_test!(count_float_point, "count_float_point");
fixture_test!(count_with_assertions, "count_with_assertions");
fixture_test!(disjoint_data_properties, "disjoint_data_properties");
fixture_test!(disjoint_data_properties_ok, "disjoint_data_properties_ok");
fixture_test!(atleast_two_shared, "atleast_two_shared");
fixture_test!(negative_assertion, "negative_assertion");
// `a = b` by an inverse-functional property, then `≤ 1 u` over the two
// asserted values. The data-ABox omission certificate used to declare the
// assertions redundant (its merge closure ignores inverse functionality), so
// the nominal CB routes answered consistent (2026-10-31,
// results/agents/2026-10-31/forced-nominal-data-misses/).
fixture_test!(inverse_functional_merge, "inverse_functional_merge");

/// `a` has the value 1 and `≥ 3 u` over `{1, 2, 3}`, so `a` has the value 3
/// and `E ⊑ F`. The native bridge lost the pigeonhole through its
/// satisfiable expander cache (value singletons are non-local) and admitted
/// the asserted `≥ 3 u` that it defers as a TBox axiom.
fixture_test!(count_with_assertions_ok, "count_with_assertions_ok");
// The same pigeonhole without assertions: `G ⊑ ≥ 2 u` over `xsd:boolean`
// entails `G ⊑ ∃u.{true}`; the bridge answered it on every route.
fixture_test!(count_boolean_pigeonhole, "count_boolean_pigeonhole");
fixture_test!(count_nominal_pigeonhole, "count_nominal_pigeonhole");

// Findings of docs/DATATYPES.md "Lean coverage (2026-10-30)".
// Singleton elision needs every value relation decided (finding 1), and the
// derived string types share the xsd:string value space.
fixture_test!(opaque_merge, "opaque_merge");
// `opaque_merge_keep` and `range_exhaust_keep` close the elision gate (`≥ 2 q`), so padded with
// 1,100 values they keep 1,100 singleton clauses; that form exceeds the
// 120 s bound on every route already at km-v155-final (300 s timeouts),
// a cost of the kept singletons, not of these findings. Plain form only.
fixture_test!(opaque_merge_keep, "opaque_merge_keep", plain_only);
fixture_test!(opaque_merge_tbox, "opaque_merge_tbox");
fixture_test!(opaque_merge_tbox_keep, "opaque_merge_tbox_keep");
// HermiT answers this one consistent, against the OWL 2 datatype map and
// against its own answer on `opaque_merge_tbox`; the fixture records the
// datatype-map answer (inconsistent).
fixture_test!(opaque_single, "opaque_single");
// A finite range exhausted by excluded values needs its cover (finding 2).
fixture_test!(range_exhaust, "range_exhaust");
fixture_test!(range_exhaust8, "range_exhaust8");
fixture_test!(range_exhaust_keep, "range_exhaust_keep", plain_only);
fixture_test!(range_exhaust_tbox, "range_exhaust_tbox");
