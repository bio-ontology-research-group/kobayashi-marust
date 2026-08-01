//! End-to-end coverage for the certified private negative-existential mirror
//! route.
//!
//! These tests spawn reasoner workers and mutate the process-global `KM_*`
//! configuration the orchestrator is driven by, so they live in their own test
//! binary: run inside the library's test process they would perturb every other
//! test that reads the same environment.
//!
//! The expected taxonomy is stated independently, read off the fixture's axioms
//! rather than produced by another KM run, so the route is checked against the
//! ontology's meaning and not against itself.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use kobayashi_marust::orchestrate::mirror::{self, PROXY_IRI_PREFIX};
use kobayashi_marust::orchestrate::{Classification, Config};

const NS: &str = "http://example.org/mirror#";

fn iri(local: &str) -> String {
    format!("{NS}{local}")
}

fn negative_iri(local: &str) -> String {
    format!("{NS}not_hasPart_{local}")
}

/// A base terminology with an inverse pair, a transitive mirror role, named
/// disjointness, an unrelated role carrying a domain and a range, and one
/// conjunction definition through the mirror role's inverse — the shape that
/// makes a mirror inverse-relevant.
fn base_axioms() -> Vec<String> {
    [
        "Declaration(ObjectProperty(<http://example.org/mirror#hasPart>))",
        "Declaration(ObjectProperty(<http://example.org/mirror#partOf>))",
        "InverseObjectProperties(<http://example.org/mirror#partOf> <http://example.org/mirror#hasPart>)",
        "TransitiveObjectProperty(<http://example.org/mirror#hasPart>)",
        "TransitiveObjectProperty(<http://example.org/mirror#partOf>)",
        "Declaration(Class(<http://example.org/mirror#Thing1>))",
        "Declaration(Class(<http://example.org/mirror#Wheel>))",
        "Declaration(Class(<http://example.org/mirror#Spoke>))",
        "Declaration(Class(<http://example.org/mirror#Bike>))",
        "Declaration(Class(<http://example.org/mirror#Vehicle>))",
        "Declaration(Class(<http://example.org/mirror#Process>))",
        "Declaration(Class(<http://example.org/mirror#Quality>))",
        "Declaration(Class(<http://example.org/mirror#SpokeOfWheel>))",
        "SubClassOf(<http://example.org/mirror#Wheel> <http://example.org/mirror#Thing1>)",
        "SubClassOf(<http://example.org/mirror#Spoke> <http://example.org/mirror#Thing1>)",
        "SubClassOf(<http://example.org/mirror#Bike> <http://example.org/mirror#Vehicle>)",
        "SubClassOf(<http://example.org/mirror#Vehicle> <http://example.org/mirror#Thing1>)",
        "SubClassOf(<http://example.org/mirror#Bike> ObjectSomeValuesFrom(<http://example.org/mirror#hasPart> <http://example.org/mirror#Wheel>))",
        "SubClassOf(<http://example.org/mirror#Wheel> ObjectSomeValuesFrom(<http://example.org/mirror#hasPart> <http://example.org/mirror#Spoke>))",
        "EquivalentClasses(<http://example.org/mirror#SpokeOfWheel> ObjectIntersectionOf(<http://example.org/mirror#Spoke> ObjectSomeValuesFrom(<http://example.org/mirror#partOf> <http://example.org/mirror#Wheel>)))",
        "DisjointClasses(<http://example.org/mirror#Process> <http://example.org/mirror#Quality>)",
        "Declaration(ObjectProperty(<http://example.org/mirror#actsOn>))",
        "ObjectPropertyDomain(<http://example.org/mirror#actsOn> <http://example.org/mirror#Process>)",
        "ObjectPropertyRange(<http://example.org/mirror#actsOn> <http://example.org/mirror#Quality>)",
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

fn mirror_fillers() -> Vec<&'static str> {
    vec![
        "Wheel",
        "Spoke",
        "Bike",
        "Vehicle",
        "SpokeOfWheel",
        "Thing1",
    ]
}

fn mirror_axioms() -> Vec<String> {
    let mut out = Vec::new();
    for filler in mirror_fillers() {
        let negative = negative_iri(filler);
        out.push(format!("Declaration(Class(<{negative}>))"));
        out.push(format!(
            "EquivalentClasses(<{negative}> ObjectComplementOf(ObjectSomeValuesFrom(<{NS}hasPart> <{NS}{filler}>)))"
        ));
    }
    // The owl:Thing mirror: its proxy sits above every other proxy, so its
    // negative sits below every other negative.
    let negative = negative_iri("Thing");
    out.push(format!("Declaration(Class(<{negative}>))"));
    out.push(format!(
        "EquivalentClasses(<{negative}> ObjectComplementOf(ObjectSomeValuesFrom(<{NS}hasPart> owl:Thing)))"
    ));
    out
}

fn document(axioms: &[String]) -> String {
    let mut text = "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n".to_string();
    text.push_str("Ontology(<http://example.org/mirror>\n");
    for axiom in axioms {
        text.push_str(axiom);
        text.push('\n');
    }
    text.push_str(")\n");
    text
}

fn fixture() -> String {
    let mut axioms = base_axioms();
    axioms.extend(mirror_axioms());
    document(&axioms)
}

// ---------------------------------------------------------------------------
// the expected taxonomy, stated independently
// ---------------------------------------------------------------------------
//
//   Wheel, Spoke, Vehicle ⊑ Thing1;  Bike ⊑ Vehicle
//   Bike ⊑ ∃hasPart.Wheel;  Wheel ⊑ ∃hasPart.Spoke;  hasPart transitive
//   SpokeOfWheel ≡ Spoke ⊓ ∃partOf.Wheel
//
// The proxy hierarchy follows from `∃hasPart.F ⊑ ∃hasPart.G` iff `F ⊑ G` or
// `F ⊑ ∃hasPart.G`. The one entry that needs the inverse role is
// `Wheel ⊑ ∃hasPart.SpokeOfWheel`: the spoke a Wheel is forced to have is
// `partOf` that Wheel, hence a SpokeOfWheel.

const EXPECTED_BASE: &[(&str, &str)] = &[
    ("Wheel", "Thing1"),
    ("Spoke", "Thing1"),
    ("Vehicle", "Thing1"),
    ("Bike", "Vehicle"),
    ("Bike", "Thing1"),
    ("SpokeOfWheel", "Spoke"),
    ("SpokeOfWheel", "Thing1"),
];

/// `P_left ⊑ P_right` over the mirror fillers, `Thing` naming the `owl:Thing`
/// mirror.
const EXPECTED_PROXY: &[(&str, &str)] = &[
    ("Wheel", "Spoke"),
    ("Wheel", "SpokeOfWheel"),
    ("Wheel", "Thing1"),
    ("Wheel", "Thing"),
    ("Spoke", "Thing1"),
    ("Spoke", "Thing"),
    ("Bike", "Wheel"),
    ("Bike", "Spoke"),
    ("Bike", "SpokeOfWheel"),
    ("Bike", "Vehicle"),
    ("Bike", "Thing1"),
    ("Bike", "Thing"),
    ("Vehicle", "Thing1"),
    ("Vehicle", "Thing"),
    ("SpokeOfWheel", "Spoke"),
    ("SpokeOfWheel", "Thing1"),
    ("SpokeOfWheel", "Thing"),
    ("Thing1", "Thing"),
];

fn expected_pairs() -> BTreeSet<(String, String)> {
    let mut pairs: BTreeSet<(String, String)> = EXPECTED_BASE
        .iter()
        .map(|(a, b)| (iri(a), iri(b)))
        .collect();
    // Complement contravariance: `P_F ⊑ P_G` becomes `N_G ⊑ N_F`.
    for (left, right) in EXPECTED_PROXY {
        pairs.insert((negative_iri(right), negative_iri(left)));
    }
    pairs
}

// ---------------------------------------------------------------------------
// harness
// ---------------------------------------------------------------------------

/// The orchestrator spawns its workers by re-invoking `km <sub>`, but under
/// `cargo test` the running executable is the test harness. Point each worker
/// at the standalone shim built beside it; `None` means the shims are not
/// present and the tests skip rather than fail spuriously.
fn worker_dir() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    // target/<profile>/deps/<test binary>
    let dir = exe.parent()?.parent()?.to_path_buf();
    ["ofn", "elc", "kobayashi-marust"]
        .iter()
        .all(|b| dir.join(b).is_file())
        .then_some(dir)
}

/// Hard wall-clock bound for anything that spawns a worker. A fixture of this
/// size settles in well under a second on every arm; overrunning means a worker
/// is wedged, and leaving that to the harness would hang the suite.
const TEST_BUDGET: std::time::Duration = std::time::Duration::from_secs(60);

struct Watchdog(std::sync::Arc<std::sync::atomic::AtomicBool>);

impl Drop for Watchdog {
    fn drop(&mut self) {
        self.0.store(true, std::sync::atomic::Ordering::SeqCst);
    }
}

fn watchdog(label: &'static str) -> Watchdog {
    let done = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let flag = done.clone();
    std::thread::spawn(move || {
        let deadline = std::time::Instant::now() + TEST_BUDGET;
        while std::time::Instant::now() < deadline {
            if flag.load(std::sync::atomic::Ordering::SeqCst) {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
        eprintln!("mirror-route test '{label}' exceeded {TEST_BUDGET:?}");
        std::process::exit(101);
    });
    Watchdog(done)
}

/// Restores a key to its captured value on drop.
struct EnvVar(&'static str, Option<std::ffi::OsString>);

impl EnvVar {
    fn set(key: &'static str, value: &str) -> EnvVar {
        let previous = std::env::var_os(key);
        std::env::set_var(key, value);
        EnvVar(key, previous)
    }
}

impl Drop for EnvVar {
    fn drop(&mut self) {
        match self.1.take() {
            Some(value) => std::env::set_var(self.0, value),
            None => std::env::remove_var(self.0),
        }
    }
}

fn worker_env(dir: &Path) -> Vec<EnvVar> {
    vec![
        EnvVar::set("KM_OFN_BIN", &dir.join("ofn").to_string_lossy()),
        EnvVar::set("KM_ELC_BIN", &dir.join("elc").to_string_lossy()),
        EnvVar::set("KM_ENGINE", &dir.join("kobayashi-marust").to_string_lossy()),
        EnvVar::set("KM_TAB_BIN", &dir.join("tableau_cli").to_string_lossy()),
        // The route picks its own arm per projection; leave the portfolio to it.
        EnvVar::set("KM_NO_ABSORB_PORTFOLIO", "1"),
    ]
}

/// `KM_*` configuration is process-global, so these tests take turns.
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Run the mirror route itself, so a test that expects the route to answer also
/// proves the route was *selected*: `None` is a refusal, never a silent
/// fall-through to the ordinary pipeline.
fn route(text: &str, label: &'static str) -> Option<Option<Classification>> {
    let dir = worker_dir()?;
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let _watchdog = watchdog(label);
    let path = std::env::temp_dir().join(format!("km-mirror-{label}-{}.ofn", std::process::id()));
    std::fs::write(&path, text).expect("write fixture");
    let _env = worker_env(&dir);
    let cfg = Config::from_env();
    let answer = mirror::try_classify(&cfg, &path).expect("mirror route");
    let _ = std::fs::remove_file(&path);
    Some(answer)
}

#[test]
fn an_explicit_atomic_route_is_not_intercepted() {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let path = std::env::temp_dir().join(format!(
        "km-mirror-explicit-route-{}.ofn",
        std::process::id()
    ));
    std::fs::write(&path, fixture()).expect("write fixture");
    let _route = EnvVar::set("KM_ROUTE", "cb_plain16");
    let cfg = Config::from_env();
    let answer = mirror::try_classify(&cfg, &path).expect("route gate");
    let _ = std::fs::remove_file(&path);
    assert!(
        answer.is_none(),
        "an explicit atomic route must retain its mechanism contract"
    );
}

fn pair_set(classification: &Classification) -> BTreeSet<(String, String)> {
    classification
        .subsumptions
        .iter()
        .map(|p| (p[0].clone(), p[1].clone()))
        .collect()
}

// ---------------------------------------------------------------------------
// tests
// ---------------------------------------------------------------------------

#[test]
fn the_route_reconstructs_the_expected_taxonomy() {
    let Some(answer) = route(&fixture(), "expected-taxonomy") else {
        return;
    };
    let routed = answer.expect("the mirror route must be selected for the fixture");
    assert!(routed.consistent);
    assert!(
        routed.unsatisfiable.is_empty(),
        "{:?}",
        routed.unsatisfiable
    );
    let pairs = pair_set(&routed);
    let expected = expected_pairs();
    let missing: Vec<_> = expected.difference(&pairs).collect();
    let extra: Vec<_> = pairs.difference(&expected).collect();
    assert!(
        missing.is_empty() && extra.is_empty(),
        "missing={missing:?} extra={extra:?}"
    );
}

/// The one consequence that needs the inverse role, and so the one mirror the
/// route classifies exactly instead of deriving by monotonicity.
#[test]
fn the_inverse_relevant_consequence_is_recovered() {
    let Some(answer) = route(&fixture(), "inverse-relevant") else {
        return;
    };
    let routed = answer.expect("the mirror route must be selected for the fixture");
    let pairs = pair_set(&routed);
    // Wheel ⊑ ∃hasPart.SpokeOfWheel, so ∃hasPart.Wheel ⊑ ∃hasPart.SpokeOfWheel,
    // so not_hasPart_SpokeOfWheel ⊑ not_hasPart_Wheel.
    assert!(pairs.contains(&(negative_iri("SpokeOfWheel"), negative_iri("Wheel"))));
}

#[test]
fn no_cross_region_pair_is_emitted() {
    let Some(answer) = route(&fixture(), "cross-region") else {
        return;
    };
    let routed = answer.expect("the mirror route must be selected for the fixture");
    let negatives: BTreeSet<String> = mirror_fillers()
        .iter()
        .map(|f| negative_iri(f))
        .chain([negative_iri("Thing")])
        .collect();
    for pair in &routed.subsumptions {
        let left = negatives.contains(&pair[0]);
        let right = negatives.contains(&pair[1]);
        assert_eq!(left, right, "cross-region pair {pair:?}");
    }
}

#[test]
fn no_proxy_iri_reaches_the_public_taxonomy() {
    let Some(answer) = route(&fixture(), "proxy-leak") else {
        return;
    };
    let routed = answer.expect("the mirror route must be selected for the fixture");
    for pair in &routed.subsumptions {
        for side in pair {
            assert!(!side.starts_with(PROXY_IRI_PREFIX), "leaked proxy {side}");
        }
    }
}

/// `P_F ≡ ⊥` makes `N_F ≡ ⊤`, so every satisfiable public class falls below it.
#[test]
fn an_empty_filler_makes_its_negative_semantic_top() {
    let mut axioms = base_axioms();
    axioms.push(format!("Declaration(Class(<{NS}Empty>))"));
    axioms.push(format!("SubClassOf(<{NS}Empty> <{NS}Process>)"));
    axioms.push(format!("SubClassOf(<{NS}Empty> <{NS}Quality>)"));
    axioms.extend(mirror_axioms());
    let negative = negative_iri("Empty");
    axioms.push(format!("Declaration(Class(<{negative}>))"));
    axioms.push(format!(
        "EquivalentClasses(<{negative}> ObjectComplementOf(ObjectSomeValuesFrom(<{NS}hasPart> <{NS}Empty>)))"
    ));
    let text = document(&axioms);

    let Some(answer) = route(&text, "semantic-top") else {
        return;
    };
    let routed = answer.expect("the mirror route must be selected");
    // Empty ⊑ Process ⊓ Quality with Process and Quality disjoint.
    assert_eq!(routed.unsatisfiable, vec![iri("Empty")]);
    let pairs = pair_set(&routed);
    // ⊤ ⊑ N_Empty: every satisfiable public class, base and negative alike.
    for base in [
        "Bike",
        "Wheel",
        "Spoke",
        "Vehicle",
        "Thing1",
        "SpokeOfWheel",
    ] {
        assert!(pairs.contains(&(iri(base), negative.clone())), "{base}");
    }
    for filler in mirror_fillers() {
        assert!(pairs.contains(&(negative_iri(filler), negative.clone())));
    }
    // An unsatisfiable class is never a subject or a superclass.
    let empty = iri("Empty");
    assert!(!pairs.iter().any(|(l, r)| *l == empty || *r == empty));
}

/// A broken premise makes the route decline, and declining is the whole of its
/// failure mode: no partial answer, no approximation.
#[test]
fn a_broken_premise_makes_the_route_decline() {
    let mut axioms = base_axioms();
    axioms.extend(mirror_axioms());
    axioms.push(format!(
        "SubClassOf(<{NS}Bike> ObjectUnionOf(<{NS}Process> <{NS}Quality>))"
    ));
    let text = document(&axioms);
    assert!(mirror::detect(&text).is_err());
    let Some(answer) = route(&text, "declined") else {
        return;
    };
    assert!(answer.is_none(), "a refused ontology must not be routed");
}

/// An ontology with no private mirror family is not the route's business at
/// all, and it must say so rather than answer.
#[test]
fn an_ontology_without_the_family_is_not_routed() {
    let text = document(&base_axioms());
    assert!(mirror::detect(&text).expect("no premise failure").is_none());
    let Some(answer) = route(&text, "not-the-family") else {
        return;
    };
    assert!(answer.is_none(), "a plain ontology must not be routed");
}
