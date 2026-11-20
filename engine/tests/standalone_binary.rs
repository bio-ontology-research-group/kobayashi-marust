//! The released `km` binary must work outside a source checkout.
//!
//! A user machine has no `lean/.lake/build/bin/km-el-reference`, no
//! `CARGO_MANIFEST_DIR`, and no `.work/` tree. This test copies the built
//! binary into a fresh empty directory, strips every `KM_*` variable, and
//! exercises the CLI subcommands that must still answer correctly.

use std::process::Command;
use std::sync::Mutex;

static COPY_LOCK: Mutex<()> = Mutex::new(());

const NOCLASS: &str = "Prefix(:=<http://ex.org/>)\nOntology(<http://ex.org/b>\nDeclaration(NamedIndividual(:a))\n)\n";

const SMALL_EL: &str = "Prefix(:=<http://example.org/>)\nOntology(\n  Declaration(Class(:A))\n  Declaration(Class(:B))\n  SubClassOf(:A :B)\n)\n";

const INDIVIDUALS: &str = "Prefix(:=<http://example.org/t#>)\nOntology(<http://example.org/t>\nDeclaration(Class(:A)) Declaration(Class(:B))\nDeclaration(ObjectProperty(:r))\nDeclaration(NamedIndividual(:x)) Declaration(NamedIndividual(:y))\nSubClassOf(:A :B)\nClassAssertion(:A :x)\nObjectPropertyAssertion(:r :x :y)\n)\n";

const LENIENT: &str = "Prefix(:=<http://example.org/t#>)\nOntology(\n  Declaration(Class(:A))\n  Declaration(Class(:B))\n  Declaration(ObjectProperty(:r))\n  Declaration(NamedIndividual(:x))\n  InverseFunctionalObjectProperty(:r)\n  SubClassOf(:A ObjectHasValue(:r _:b1))\n  ClassAssertion(ObjectHasValue(:r _:b1) :x)\n  ClassAssertion(:B :x)\n)\n";

fn tmp_dir() -> std::path::PathBuf {
    let base = std::env::var_os("TMPDIR")
        .map(std::path::PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| std::path::PathBuf::from(h).join("tmp")))
        .unwrap_or_else(|| std::path::PathBuf::from("/tmp"));
    let dir = base.join(format!(
        "km-standalone-test-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn standalone_run(dir: &std::path::Path, args: &[&str], input: Option<&str>) -> (String, String, i32) {
    let bin = env!("CARGO_BIN_EXE_km");
    let copied = dir.join("km");
    {
        let _guard = COPY_LOCK.lock().unwrap();
        std::fs::copy(bin, &copied).unwrap();
    }

    let mut command = Command::new(&copied);
    command.current_dir(dir);
    command.stdout(std::process::Stdio::piped());
    command.stderr(std::process::Stdio::piped());
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(&key);
        }
    }
    command.env("HOME", std::env::var_os("HOME").unwrap_or_default());
    command.env("KM_THREADS", "1");
    command.args(args);
    if input.is_some() {
        command.stdin(std::process::Stdio::piped());
    }
    let mut child = command.spawn().unwrap();
    if let Some(stdin) = input {
        use std::io::Write;
        let mut stdin_pipe = child.stdin.take().unwrap();
        stdin_pipe.write_all(stdin.as_bytes()).unwrap();
    }
    let output = child.wait_with_output().unwrap();
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        output.status.code().unwrap_or(-1),
    )
}

fn write(dir: &std::path::Path, name: &str, content: &str) -> std::path::PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, content).unwrap();
    path
}

#[test]
fn classify_noclass_outside_checkout() {
    let dir = tmp_dir();
    let file = write(&dir, "noclass.ofn", NOCLASS);
    let (out, err, code) = standalone_run(&dir, &["classify", file.to_str().unwrap()], None);
    assert_eq!(code, 0, "stderr: {err}");
    assert_eq!(out.trim(), r#"{"consistent": true, "subsumptions": [], "unsatisfiable": [], "dropped": 0}"#);
}

#[test]
fn classify_small_el_outside_checkout() {
    let dir = tmp_dir();
    let file = write(&dir, "small_el.ofn", SMALL_EL);
    let (out, err, code) = standalone_run(&dir, &["classify", file.to_str().unwrap()], None);
    assert_eq!(code, 0, "stderr: {err}");
    assert!(out.contains("\"consistent\": true"), "stdout: {out}");
    assert!(out.contains("small_el.ofn") || out.contains(":A") || out.contains("http://example.org/A"),
        "missing expected class names in {out}");
}

#[test]
fn classify_individuals_outside_checkout() {
    let dir = tmp_dir();
    let file = write(&dir, "individuals.ofn", INDIVIDUALS);
    let (out, err, code) = standalone_run(
        &dir,
        &["classify", "--lines", "--realize", "--values", file.to_str().unwrap()],
        None,
    );
    assert_eq!(code, 0, "stderr: {err}");
    let lines: Vec<&str> = out.lines().collect();
    assert!(lines.iter().any(|l| l.starts_with("SUB")), "no subsumptions in {out}");
    assert!(lines.iter().any(|l| l.starts_with("TYPE")), "no instance types in {out}");
    assert!(lines.iter().any(|l| l.starts_with("VALUE")), "no property values in {out}");
}

#[test]
fn classify_lenient_outside_checkout() {
    let dir = tmp_dir();
    let file = write(&dir, "lenient.ofn", LENIENT);
    let (out, err, code) = standalone_run(&dir, &["classify", "--lenient", file.to_str().unwrap()], None);
    assert_eq!(code, 0, "stderr: {err}");
    assert!(out.contains("\"consistent\": true"), "stdout: {out}");
}

#[test]
fn incremental_init_outside_checkout() {
    let dir = tmp_dir();
    let (out, err, code) = standalone_run(&dir, &["incremental"], Some(r#"{"op":"init","clauses":[]}"#));
    assert_eq!(code, 0, "stderr: {err}");
    assert!(out.contains("\"status\":\"ok\"") || out.contains("\"status\": \"ok\""), "stdout: {out}");
    assert!(out.contains("\"op\":\"init\"") || out.contains("\"op\": \"init\""), "stdout: {out}");
}
