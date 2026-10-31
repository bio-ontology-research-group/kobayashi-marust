//! Worker-only protocol variables never reach a published answer
//! (docs/HYBRID-CB-HT.md section 12). `KM_HT_GLOBAL=1` asks the HT worker for
//! a consistency verdict only; set by the user on
//! `km classify --route ht_general` it used to publish an empty taxonomy, so
//! the entailed `B ⊑ D` below was missing. `km classify` and `km explain`
//! now strip `routing::WORKER_ONLY_KEYS` before any route runs.
use std::process::Command;

const ONTOLOGY: &str = "Prefix(:=<urn:w#>)
Ontology(<urn:w>
Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
Declaration(Class(:D)) Declaration(Class(:E)) Declaration(ObjectProperty(:r))
SubClassOf(:B ObjectUnionOf(:C :E))
SubClassOf(:C :D)
SubClassOf(:E :D)
SubClassOf(:A ObjectSomeValuesFrom(:r :B))
SubClassOf(ObjectSomeValuesFrom(:r :D) :C)
)
";

fn classify(route: Option<&str>, extra: &[(&str, &str)]) -> (String, String) {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"));
    let path = dir.join(format!("worker-only-{}.ofn", std::process::id()));
    std::fs::write(&path, ONTOLOGY).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    for (key, value) in extra {
        command.env(key, value);
    }
    command.arg("classify").arg("--lines");
    if let Some(route) = route {
        command.args(["--route", route]);
    }
    let output = command.arg(&path).output().unwrap();
    assert!(output.status.success(), "{route:?} {extra:?}: {}", String::from_utf8_lossy(&output.stderr));
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn sorted(text: &str) -> Vec<String> {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    lines.sort();
    lines
}

#[test]
fn worker_only_variables_do_not_change_the_published_taxonomy() {
    for route in [Some("ht_general"), None] {
        let (plain, _) = classify(route, &[]);
        assert!(plain.contains("SUB\t:B\t:D") || plain.contains("SUB\turn:w#B\turn:w#D"),
            "{route:?}: entailed B ⊑ D missing: {plain}");
        for key in kobayashi_marust::routing::WORKER_ONLY_KEYS {
            let (leaked, stderr) = classify(route, &[(key, "1")]);
            assert_eq!(sorted(&leaked), sorted(&plain), "{route:?} {key}=1 changed the answer");
            assert!(stderr.contains(key), "{route:?} {key}: no notice on stderr: {stderr}");
        }
    }
}
