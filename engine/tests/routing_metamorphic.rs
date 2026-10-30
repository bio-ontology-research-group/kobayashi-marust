//! Metamorphic stability of automatic routing (docs/V1.5.4-ACCEPTANCE.md, G5).
//!
//! Under the general routing policy the selected route may depend only on
//! fragment membership, certificates, and construct presence. Transformations
//! that change counts, names, order, or annotations but none of these must
//! therefore leave the route unchanged. Each test runs `km profile` on the
//! repository's small fixture ontologies and on transformed copies.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("repository root")
        .to_path_buf()
}

fn fixtures() -> Vec<PathBuf> {
    let root = repo_root();
    let mut files = Vec::new();
    for dir in ["examples/ontologies", "oracle/ontologies", "engine/tests/fixtures"] {
        let Ok(entries) = std::fs::read_dir(root.join(dir)) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("ofn") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Route selected by `km profile` under the general policy, or `None` if the
/// frontend rejects the input.
fn route(path: &Path) -> Option<String> {
    let out = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("profile")
        .arg(path)
        .env_remove("KM_ROUTING_POLICY")
        .output()
        .expect("run km profile");
    let row: serde_json::Value = serde_json::from_slice(&out.stdout).ok()?;
    if row["status"] != "ok" {
        return None;
    }
    row["selected_route"].as_str().map(str::to_owned)
}

/// Split an OWL functional-syntax document into its header (prefixes and the
/// `Ontology(` line) and the axiom body, without the final closing paren.
fn split(text: &str) -> Option<(String, String)> {
    let open = text.find("Ontology(")?;
    let header_end = open + text[open..].find('\n')? + 1;
    let close = text.rfind(')')?;
    if close < header_end {
        return None;
    }
    Some((text[..header_end].to_string(), text[header_end..close].to_string()))
}

fn variant(text: &str, transform: impl Fn(&str, &str) -> String) -> Option<String> {
    let (header, body) = split(text)?;
    Some(transform(&header, &body))
}

/// Prefix every default-prefix name `:x` in `body` with `c`, so that the copy
/// uses a disjoint vocabulary declared by `Prefix(c:=...)`.
fn rename_default_prefix(body: &str) -> String {
    let mut out = String::with_capacity(body.len() + 64);
    let mut prev = ' ';
    let mut in_iri = false;
    for ch in body.chars() {
        match ch {
            '<' => in_iri = true,
            '>' => in_iri = false,
            _ => {}
        }
        if ch == ':' && !in_iri && (prev.is_whitespace() || prev == '(') {
            out.push('c');
        }
        out.push(ch);
        prev = ch;
    }
    out
}

fn check(name: &str, make: impl Fn(&str) -> Option<String>) {
    let dir = std::env::temp_dir().join(format!(
        "km-routing-metamorphic-{}-{}",
        std::process::id(),
        name.replace(' ', "-")
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let mut compared = 0;
    let mut changed = Vec::new();
    for path in fixtures() {
        let Some(base) = route(&path) else { continue };
        let text = std::fs::read_to_string(&path).unwrap();
        let Some(new_text) = make(&text) else { continue };
        let out = dir.join(path.file_name().unwrap());
        std::fs::write(&out, new_text).unwrap();
        let Some(after) = route(&out) else { continue };
        compared += 1;
        if after != base {
            changed.push(format!("{}: {base} -> {after}", path.display()));
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(compared >= 20, "{name}: only {compared} fixtures compared");
    assert!(changed.is_empty(), "{name} changed the route:\n{}", changed.join("\n"));
}

#[test]
fn route_is_invariant_under_duplicated_axioms() {
    check("duplication", |text| {
        variant(text, |header, body| format!("{header}{body}\n{body})\n"))
    });
}

#[test]
fn route_is_invariant_under_annotations_and_unused_declarations() {
    check("annotation", |text| {
        variant(text, |header, body| {
            let mut extra = String::new();
            for i in 0..50 {
                extra.push_str(&format!(
                    "Declaration(Class(<urn:km-unused#C{i}>))\n\
                     AnnotationAssertion(<http://www.w3.org/2000/01/rdf-schema#comment> <urn:km-unused#C{i}> \"unused\")\n"
                ));
            }
            format!("{header}{extra}{body})\n")
        })
    });
}

#[test]
fn route_is_invariant_under_axiom_reordering() {
    check("reordering", |text| {
        variant(text, |header, body| {
            let mut lines: Vec<&str> = body.lines().collect();
            lines.reverse();
            format!("{header}{})\n", lines.join("\n"))
        })
    });
}

#[test]
fn route_is_invariant_under_disjoint_union_with_a_renamed_copy() {
    check("disjoint union", |text| {
        if !text.contains("Prefix(:=") {
            return None;
        }
        variant(text, |header, body| {
            let header = header.replacen(
                "Prefix(:=",
                "Prefix(c:=<urn:km-copy#>)\nPrefix(:=",
                1,
            );
            format!("{header}{body}\n{})\n", rename_default_prefix(body))
        })
    });
}
