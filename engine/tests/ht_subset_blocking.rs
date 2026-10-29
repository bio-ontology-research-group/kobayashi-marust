//! Regression tests for subset blocking in the native hypertableau
//! (docs/HYBRID-CB-HT.md section 8). A node blocked by a strict superset takes
//! its blocker's label in the unravelled model; a gained literal that a clause
//! reads across the edge to the node (`∃r.C ⊑ D` as `C(y) ∧ r(x, y) → D(x)`,
//! a cardinality filler) made `ht_general` and the card arm answer wrongly.
//! The cases were delta-debugged from the ALCHIQ seeds 103, 507 and 639;
//! the expected answers are HermiT 1.4.3.456's (on the seed declarations; the
//! extra declared classes here only add subsumptions into the universal `B`).
use std::collections::BTreeSet;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(60);
static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Answer {
    consistent: bool,
    unsat: BTreeSet<String>,
    subs: BTreeSet<(String, String)>,
}

fn classify(text: &str, route: &str) -> Answer {
    let path = std::env::temp_dir().join(format!(
        "km-subset-blocking-{}-{}.ofn",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, text).unwrap();
    let fixture = Fixture(path);
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command
        .env("KM_ROUTE", route)
        .args(["classify", "--lines"])
        .arg(&fixture.0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let started = Instant::now();
    let mut child = command.spawn().unwrap();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded {BOUND:?} on route {route}:\n{text}");
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let mut stdout = String::new();
    child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
    let mut stderr = String::new();
    child.stderr.take().unwrap().read_to_string(&mut stderr).unwrap();
    assert!(status.success(), "km failed on route {route}: {stderr}\n{stdout}");
    let mut consistent = None;
    let mut unsat = BTreeSet::new();
    let mut subs = BTreeSet::new();
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [single] if single.starts_with("CONSISTENT ") => consistent = Some(single.ends_with(" 1")),
            ["UNSAT", class] => {
                unsat.insert(class.trim_start_matches(':').to_string());
            }
            ["SUB", sub, sup] => {
                subs.insert((sub.trim_start_matches(':').to_string(), sup.trim_start_matches(':').to_string()));
            }
            _ => {}
        }
    }
    let consistent = consistent.unwrap_or_else(|| panic!("no CONSISTENT line on {route}: {stdout}"));
    if !consistent {
        return Answer { consistent, unsat: BTreeSet::new(), subs: BTreeSet::new() };
    }
    let subs = subs
        .into_iter()
        .filter(|(a, b)| a != b && !unsat.contains(a) && !unsat.contains(b))
        .filter(|(a, b)| !a.starts_with("owl:") && !b.starts_with("owl:"))
        .collect();
    Answer { consistent, unsat, subs }
}

const HEADER: &str = "Prefix(:=<http://example.org/g#>)\n\
    Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
    Ontology(<http://example.org/g>\n\
    Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
    Declaration(Class(:E)) Declaration(Class(:Q1)) Declaration(Class(:Q2)) Declaration(Class(:Q3))\n\
    Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:t))\n";

fn ontology(axioms: &str) -> String {
    format!("{HEADER}{axioms}\n)\n")
}

fn inconsistent() -> Answer {
    Answer { consistent: false, unsat: BTreeSet::new(), subs: BTreeSet::new() }
}

fn answer(unsat: &[&str], subs: &[(&str, &str)]) -> Answer {
    Answer {
        consistent: true,
        unsat: unsat.iter().map(|c| c.to_string()).collect(),
        subs: subs.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect(),
    }
}

/// Every element needs a `t`-successor outside `D ≡ ∃t.(A ⊔ ¬A)`, that is
/// one without a `t`-successor: inconsistent (seed 103).
const NO_LAST_SUCCESSOR: &str = "EquivalentClasses(:D ObjectSomeValuesFrom(:t ObjectUnionOf(:A ObjectComplementOf(:A))))\n\
    DisjointClasses(owl:Thing ObjectAllValuesFrom(:t :D))";

#[test]
fn gained_recognition_literal_blocks_no_successor() {
    for route in ["ht_general", "auto"] {
        assert_eq!(classify(&ontology(NO_LAST_SUCCESSOR), route), inconsistent(), "{route}");
    }
}

/// `B ≡ ∃s.A ⊔ ¬B` makes `B` universal, so `∃s.B ⊔ ¬B ≡ ⊤` and `D` is
/// unsatisfiable (seed 507).
#[test]
fn gained_literal_at_an_existential_successor() {
    let text = ontology(
        "EquivalentClasses(:B ObjectUnionOf(ObjectSomeValuesFrom(:s :A) ObjectComplementOf(:B)))\n\
         DisjointClasses(ObjectUnionOf(ObjectSomeValuesFrom(:s :B) ObjectComplementOf(:B)) :D)\n\
         EquivalentClasses(:Q3 ObjectIntersectionOf(ObjectIntersectionOf(:D :A) ObjectMaxCardinality(2 :t :C)))",
    );
    let want = answer(&["D", "Q3"], &[("A", "B"), ("C", "B"), ("E", "B"), ("Q1", "B"), ("Q2", "B")]);
    for route in ["ht_general", "auto"] {
        assert_eq!(classify(&text, route), want, "{route}");
    }
}

/// `C ⊑ ∃r.A`, `A ⊑ B` (from the disjointness), `≥1 r.B ⊑ B` give `C ⊑ B`
/// (seed 639).
#[test]
fn gained_literal_under_an_at_least_recognition() {
    let text = ontology(
        "EquivalentClasses(:D :C)\n\
         SubClassOf(ObjectMinCardinality(1 :r :B) :B)\n\
         SubClassOf(:C ObjectSomeValuesFrom(:r :A))\n\
         DisjointClasses(ObjectComplementOf(ObjectIntersectionOf(:A :B)) :A)\n\
         SubClassOf(owl:Thing ObjectSomeValuesFrom(:s :D))\n\
         EquivalentClasses(:Q3 ObjectUnionOf(:C ObjectComplementOf(ObjectUnionOf(:C ObjectComplementOf(:B)))))",
    );
    let want = answer(
        &[],
        &[
            ("A", "B"), ("A", "Q3"), ("B", "Q3"), ("C", "B"), ("C", "D"), ("C", "Q3"),
            ("D", "B"), ("D", "C"), ("D", "Q3"), ("Q3", "B"),
        ],
    );
    for route in ["ht_general", "auto"] {
        assert_eq!(classify(&text, route), want, "{route}");
    }
}

/// The card arm's subset blocking (mode 5) had the same gap. With the
/// separate inverse pair and the role chain over the asserted edge, the
/// automatic route selects `certified_card_proxy_abox`, whose card arm
/// published `CONSISTENT 1` for this inconsistent ontology.
#[test]
fn card_arm_subset_blocking_on_the_automatic_route() {
    let tbox = format!("{NO_LAST_SUCCESSOR}\nSubClassOf(:E ObjectMinCardinality(2 :r :B))");
    let abox = "Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
        Declaration(ObjectProperty(:u)) Declaration(ObjectProperty(:w)) InverseObjectProperties(:u :w)\n\
        Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q))\n\
        SubObjectPropertyOf(ObjectPropertyChain(:p :q) :q)\n\
        ClassAssertion(:E :a) ObjectPropertyAssertion(:p :a :b) ClassAssertion(:E :b)";
    assert_eq!(classify(&ontology(&tbox), "ht_card"), inconsistent());
    let text = ontology(&format!("{tbox}\n{abox}"));
    for route in ["auto", "certified_card_proxy_abox"] {
        assert_eq!(classify(&text, route), inconsistent(), "{route}");
    }
}
