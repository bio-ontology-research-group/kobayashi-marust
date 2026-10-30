//! A forced route (`KM_ROUTE=<name>`, `--route <name>` or `manual`) bypasses
//! the automatic gate that keeps every input on a mechanism that represents
//! it. When the forced mechanism drops or approximates part of the input, a
//! consistent answer is not the answer for the input, so `km classify` must
//! refuse it (exit 3, naming the route and the dropped constructs). With
//! `KM_ALLOW_APPROXIMATE=1` it may publish the answer, but only with an
//! `APPROXIMATE<TAB>reason` line before the taxonomy and a `DROPPED` count
//! that includes the drops. The automatic route is unaffected.
//!
//! Reproducers: `fixtures/sorts_differential/max2_three*.ofn` (`⊤ ⊑ ≤2 u`, or
//! `K ⊑ ≤2 u` with `K(a)`, and three `u`-values on `a`: inconsistent; HermiT
//! 1.4's answer is the matching `.hermit` file). Before this rule the forced
//! `default` route answered both `CONSISTENT 1`.
use std::collections::BTreeSet;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(120);
static NEXT: AtomicUsize = AtomicUsize::new(0);

fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/sorts_differential")
}

fn reproducers() -> Vec<PathBuf> {
    ["max2_three.ofn", "max2_three_K.ofn"].iter().map(|name| fixture_dir().join(name)).collect()
}

struct Fixture(PathBuf);
impl Fixture {
    fn new(text: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "km-forced-route-{}-{}.ofn",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::write(&path, text).unwrap();
        Self(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

struct Run {
    code: Option<i32>,
    stdout: String,
    stderr: String,
}

/// `km <args> <path>` with every ambient `KM_*` variable removed and `env`
/// added, killed (by its own handle) after `BOUND`.
fn km(args: &[&str], path: &Path, env: &[(&str, &str)]) -> Run {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.envs(env.iter().copied());
    command.args(args).arg(path).stdout(Stdio::piped()).stderr(Stdio::piped());
    let started = Instant::now();
    let mut child = command.spawn().unwrap();
    let mut stdout_pipe = child.stdout.take().unwrap();
    let mut stderr_pipe = child.stderr.take().unwrap();
    let out = std::thread::spawn(move || {
        let mut s = String::new();
        stdout_pipe.read_to_string(&mut s).unwrap();
        s
    });
    let err = std::thread::spawn(move || {
        let mut s = String::new();
        stderr_pipe.read_to_string(&mut s).unwrap();
        s
    });
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km {args:?} {} exceeded {BOUND:?} with {env:?}", path.display());
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    Run { code: status.code(), stdout: out.join().unwrap(), stderr: err.join().unwrap() }
}

#[derive(Debug, PartialEq, Eq)]
struct Answer {
    consistent: bool,
    unsat: BTreeSet<String>,
    /// Pairs whose subject is satisfiable (an unsatisfiable class is below
    /// every class, which the line output may or may not spell out).
    subs: BTreeSet<(String, String)>,
}

/// The `--lines` answer and the `APPROXIMATE` reason, checking the line
/// order: `CONSISTENT`, `DROPPED`, then `APPROXIMATE` (when present) before
/// any taxonomy row.
fn parse_lines(stdout: &str, expand: &dyn Fn(&str) -> String) -> (Answer, usize, Option<String>) {
    let lines: Vec<&str> = stdout.lines().collect();
    assert!(lines.len() >= 2, "short output: {stdout}");
    let consistent = match lines[0] {
        "CONSISTENT 1" => true,
        "CONSISTENT 0" => false,
        other => panic!("first line {other:?}"),
    };
    let dropped: usize = lines[1].strip_prefix("DROPPED ").expect("DROPPED line").trim().parse().unwrap();
    let mut approximate = None;
    let mut unsat = BTreeSet::new();
    let mut subs = BTreeSet::new();
    for (index, line) in lines.iter().enumerate().skip(2) {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["APPROXIMATE", reason] => {
                assert_eq!(index, 2, "APPROXIMATE must directly follow DROPPED: {stdout}");
                approximate = Some(reason.to_string());
            }
            ["UNSAT", class] => {
                unsat.insert(expand(class));
            }
            ["SUB", sub, sup] => {
                subs.insert((expand(sub), expand(sup)));
            }
            _ => {}
        }
    }
    assert!(
        !stdout.lines().skip(3).any(|line| line.starts_with("APPROXIMATE")),
        "APPROXIMATE after the taxonomy: {stdout}"
    );
    let subs = subs.into_iter().filter(|(sub, _)| !unsat.contains(sub)).collect();
    (Answer { consistent, unsat, subs }, dropped, approximate)
}

/// HermiT's answer in the `.hermit` file next to `path` (full IRIs).
fn hermit(path: &Path) -> Answer {
    let reference = std::fs::read_to_string(path.with_extension("hermit")).unwrap();
    let mut answer = Answer { consistent: true, unsat: BTreeSet::new(), subs: BTreeSet::new() };
    for line in reference.lines() {
        match line.split('\t').collect::<Vec<_>>().as_slice() {
            ["C", value] => answer.consistent = *value == "true",
            ["U", class] => {
                answer.unsat.insert(class.to_string());
            }
            ["S", sub, sup] => {
                answer.subs.insert((sub.to_string(), sup.to_string()));
            }
            _ => {}
        }
    }
    if !answer.consistent {
        answer.unsat.clear();
        answer.subs.clear();
    }
    answer
}

fn expander(text: &str) -> impl Fn(&str) -> String {
    let base = text
        .lines()
        .find_map(|l| l.strip_prefix("Prefix(:=<").and_then(|r| r.strip_suffix(">)")))
        .unwrap_or_default()
        .to_string();
    move |name: &str| match name.strip_prefix(':') {
        Some(local) => format!("{base}{local}"),
        None => name.to_string(),
    }
}

fn normalized(mut answer: Answer) -> Answer {
    if !answer.consistent {
        answer.unsat.clear();
        answer.subs.clear();
    }
    answer
}

#[test]
fn forced_default_route_refuses_the_max2_reproducers() {
    for path in reproducers() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        for (args, env) in [
            (vec!["classify", "--lines"], vec![("KM_ROUTE", "default")]),
            (vec!["classify", "--lines", "--route", "default"], vec![]),
            (vec!["classify"], vec![("KM_ROUTE", "default")]),
            // `0` and an empty value do not allow approximation.
            (vec!["classify", "--lines"], vec![("KM_ROUTE", "default"), ("KM_ALLOW_APPROXIMATE", "0")]),
        ] {
            let run = km(&args, &path, &env);
            assert_eq!(run.code, Some(3), "{name} {args:?} {env:?}: {}\n{}", run.stderr, run.stdout);
            assert!(run.stdout.is_empty(), "{name}: refused run published {:?}", run.stdout);
            assert!(run.stderr.contains("route `default` drops"), "{name}: {}", run.stderr);
            // The frontend carries each `u` value as its `DataHasValue` class
            // assertion, which this route then drops with the rest of the ABox.
            assert!(run.stderr.contains("ABox assertion"), "{name}: {}", run.stderr);
            assert!(run.stderr.contains("the answer would be approximate"), "{name}: {}", run.stderr);
            assert!(run.stderr.contains("KM_ALLOW_APPROXIMATE=1"), "{name}: {}", run.stderr);
        }
    }
}

#[test]
fn allowed_approximation_is_marked_and_counted() {
    for path in reproducers() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).unwrap();
        let env = [("KM_ROUTE", "default"), ("KM_ALLOW_APPROXIMATE", "1")];
        let run = km(&["classify", "--lines"], &path, &env);
        assert_eq!(run.code, Some(0), "{name}: {}", run.stderr);
        let (answer, dropped, approximate) = parse_lines(&run.stdout, &expander(&text));
        let reason = approximate.unwrap_or_else(|| panic!("{name}: no APPROXIMATE line: {}", run.stdout));
        assert!(reason.starts_with("route `default` drops "), "{name}: {reason}");
        // The forced route publishes the weakened ontology's answer; the
        // three dropped `u` assertions are counted.
        assert!(answer.consistent, "{name}: the approximate answer is expected to differ from HermiT");
        assert!(dropped >= 3, "{name}: DROPPED {dropped}");

        let run = km(&["classify"], &path, &env);
        assert_eq!(run.code, Some(0), "{name}: {}", run.stderr);
        let json: serde_json::Value = serde_json::from_str(run.stdout.trim()).unwrap();
        assert_eq!(json["approximate"].as_str(), Some(reason.as_str()), "{name}: {json}");
        assert_eq!(json["dropped"].as_u64(), Some(dropped as u64), "{name}: {json}");
    }
}

#[test]
fn automatic_route_matches_hermit_on_the_max2_reproducers() {
    for path in reproducers() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).unwrap();
        let expected = hermit(&path);
        for env in [
            vec![],
            vec![("KM_ROUTE", "auto")],
            // Allowing approximation changes nothing on the automatic route.
            vec![("KM_ALLOW_APPROXIMATE", "1")],
        ] {
            let run = km(&["classify", "--lines"], &path, &env);
            assert_eq!(run.code, Some(0), "{name} {env:?}: {}", run.stderr);
            let (answer, dropped, approximate) = parse_lines(&run.stdout, &expander(&text));
            assert_eq!(approximate, None, "{name} {env:?}");
            assert_eq!(dropped, 0, "{name} {env:?}");
            assert_eq!(normalized(answer), expected, "{name} {env:?}");
        }
    }
}

/// Small inputs with hand-derived OWL 2 Direct Semantics answers, each of
/// which some forced non-nominal route used to answer wrongly: ABox
/// assertions outside nominal clausification, a TBox nominal, a DL-safe rule
/// lowered over nominal proxies, and the data-value reproducers.
fn probes() -> Vec<(&'static str, String, Answer)> {
    const HEAD: &str = "Prefix(:=<http://e.org/p#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
        Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://e.org/p>\n\
        Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:S)) \
        Declaration(ObjectProperty(:r)) Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n";
    let doc = |body: &str| format!("{HEAD}{body}\n)\n");
    let inconsistent = || Answer { consistent: false, unsat: BTreeSet::new(), subs: BTreeSet::new() };
    let mut out = vec![
        (
            "role assertion clash",
            doc("SubClassOf(:A ObjectAllValuesFrom(:r ObjectComplementOf(:B))) \
                 ClassAssertion(:A :a) ClassAssertion(:B :b) ObjectPropertyAssertion(:r :a :b)"),
            inconsistent(),
        ),
        (
            "same-individual clash",
            doc("SameIndividual(:a :b) ClassAssertion(:A :a) ClassAssertion(ObjectComplementOf(:A) :b)"),
            inconsistent(),
        ),
        (
            "different-individuals clash",
            doc("DifferentIndividuals(:a :b) EquivalentClasses(ObjectOneOf(:a) ObjectOneOf(:b))"),
            inconsistent(),
        ),
        (
            "rule over a contradictory ABox",
            doc("ClassAssertion(:A :a) ClassAssertion(ObjectComplementOf(:B) :a) \
                 DLSafeRule(Body(ClassAtom(:A Variable(<urn:x>))) Head(ClassAtom(:B Variable(<urn:x>))))"),
            inconsistent(),
        ),
        (
            "TBox nominal",
            // Both r-successors of an S are a, which is then in A and in B.
            doc("SubClassOf(:A ObjectOneOf(:a)) SubClassOf(:B ObjectOneOf(:a)) \
                 SubClassOf(:S ObjectSomeValuesFrom(:r :A)) SubClassOf(:S ObjectSomeValuesFrom(:r :B)) \
                 SubClassOf(:S ObjectAllValuesFrom(:r ObjectUnionOf(ObjectComplementOf(:A) ObjectComplementOf(:B))))"),
            Answer {
                consistent: true,
                unsat: ["http://e.org/p#S".to_string()].into(),
                subs: BTreeSet::new(),
            },
        ),
    ];
    for path in reproducers() {
        let name = if path.ends_with("max2_three.ofn") { "max2_three" } else { "max2_three_K" };
        out.push((name, std::fs::read_to_string(&path).unwrap(), hermit(&path)));
    }
    out
}

fn routes() -> Vec<String> {
    let output = Command::new(env!("CARGO_BIN_EXE_km")).arg("routes").output().unwrap();
    assert!(output.status.success());
    let routes: Vec<String> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| line.split('\t').next().unwrap().to_string())
        .collect();
    assert!(routes.len() >= 40, "{routes:?}");
    assert_eq!(routes[0], "auto");
    routes
}

/// The contract over the whole route catalog: on every probe, every route
/// either refuses, or publishes the exact answer without `APPROXIMATE`, or
/// (only with `KM_ALLOW_APPROXIMATE=1`) publishes an answer marked
/// `APPROXIMATE` with a positive `DROPPED`. `auto` must answer every probe
/// exactly and never mark it. No route may publish an unmarked wrong answer.
#[test]
fn no_route_publishes_an_unmarked_approximate_answer() {
    let probes = probes();
    let routes = routes();
    let jobs: Vec<(usize, String, bool)> = (0..probes.len())
        .flat_map(|p| routes.iter().flat_map(move |r| [(p, r.clone(), false), (p, r.clone(), true)]))
        .collect();
    let next = AtomicUsize::new(0);
    let failures = std::sync::Mutex::new(Vec::new());
    // Outcome counts, so that the contract cannot hold vacuously.
    let (refused, exact, marked) = (AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0));
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, Ordering::Relaxed);
                let Some((probe, route, allow)) = jobs.get(index) else { break };
                let (name, text, expected) = &probes[*probe];
                let fixture = Fixture::new(text);
                let mut env = vec![("KM_ROUTE", route.as_str())];
                if *allow {
                    env.push(("KM_ALLOW_APPROXIMATE", "1"));
                }
                let run = km(&["classify", "--lines"], &fixture.0, &env);
                let label = format!("{name} on {route} (allow={allow})");
                let mut fail = |why: String| failures.lock().unwrap().push(format!("{label}: {why}"));
                if run.code != Some(0) {
                    if route == "auto" {
                        fail(format!("auto refused: {}", run.stderr));
                    } else if !run.stdout.is_empty() {
                        fail(format!("refusal published output {:?}", run.stdout));
                    }
                    refused.fetch_add(1, Ordering::Relaxed);
                    continue;
                }
                let (answer, dropped, approximate) = parse_lines(&run.stdout, &expander(text));
                match approximate {
                    Some(reason) => {
                        marked.fetch_add(1, Ordering::Relaxed);
                        if !*allow || route == "auto" {
                            fail(format!("APPROXIMATE without KM_ALLOW_APPROXIMATE or on auto: {reason}"));
                        } else if dropped == 0 {
                            fail(format!("APPROXIMATE with DROPPED 0: {reason}"));
                        } else if !reason.starts_with(&format!("route `{route}` drops ")) {
                            fail(format!("reason does not name the route: {reason}"));
                        }
                    }
                    None => {
                        exact.fetch_add(1, Ordering::Relaxed);
                        let answer = normalized(answer);
                        if &answer != expected {
                            fail(format!("unmarked answer {answer:?} (DROPPED {dropped}), expected {expected:?}"));
                        } else if route == "auto" && dropped != 0 {
                            fail(format!("auto published DROPPED {dropped}"));
                        }
                    }
                }
            });
        }
    });
    let failures = failures.into_inner().unwrap();
    assert!(failures.is_empty(), "{} failure(s):\n{}", failures.len(), failures.join("\n"));
    let (refused, exact, marked) = (refused.into_inner(), exact.into_inner(), marked.into_inner());
    assert_eq!(refused + exact + marked, jobs.len());
    eprintln!("refused {refused}, exact {exact}, marked {marked} of {}", jobs.len());
    // The bounds only exclude a vacuous pass.
    assert!(exact >= probes.len() * 4 && marked >= probes.len() * 10 && refused >= probes.len() * 10,
        "refused {refused}, exact {exact}, marked {marked}");
}

/// `km incremental-source` keeps an ambient `KM_ROUTE` (only an unset one
/// defaults to `auto`), so a forced route must fail closed there too, and an
/// allowed approximate answer is still refused: the session's rows, deltas
/// and reuse checks carry no approximation marker. The legacy session
/// (`KM_SOURCE_SESSION=legacy`) always routes the source automatically.
#[test]
fn incremental_source_session_refuses_a_forced_approximate_route() {
    let path = fixture_dir().join("max2_three.ofn");
    let source = std::fs::read_to_string(&path).unwrap();
    let session = |env: &[(&str, &str)]| -> serde_json::Value {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("KM_") {
                command.env_remove(key);
            }
        }
        let mut child = command
            .envs(env.iter().copied())
            .arg("incremental-source")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        {
            let mut stdin = child.stdin.take().unwrap();
            serde_json::to_writer(&mut stdin, &serde_json::json!({"op": "init", "functional_syntax": source}))
                .unwrap();
            stdin.write_all(b"\n").unwrap();
        }
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let stdout = String::from_utf8(output.stdout).unwrap();
        serde_json::from_str(stdout.lines().next().expect("one response")).unwrap()
    };
    let exact = session(&[]);
    assert_eq!(exact["status"], "ok", "{exact}");
    assert_eq!(exact["result"]["consistent"], false, "{exact}");
    for env in [
        vec![("KM_ROUTE", "default")],
        vec![("KM_ROUTE", "default"), ("KM_ALLOW_APPROXIMATE", "1")],
    ] {
        let response = session(&env);
        assert_eq!(response["status"], "error", "{env:?}: {response}");
        let error = response["error"].as_str().unwrap_or_default();
        assert!(error.contains("route `default` drops"), "{env:?}: {error}");
    }
    // The legacy session ignores the ambient route: its answer is its
    // automatic answer. (That automatic answer on this file is a separate
    // open defect of the legacy retained backend, not of forced routing.)
    let legacy = session(&[("KM_SOURCE_SESSION", "legacy"), ("KM_ROUTE", "default")]);
    assert_eq!(legacy["status"], "ok", "{legacy}");
    assert_eq!(legacy, session(&[("KM_SOURCE_SESSION", "legacy")]));
}
