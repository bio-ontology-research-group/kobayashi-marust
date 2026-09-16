//! Guard: the completion rule bodies must not read the environment inline.
//!
//! `add_concept_to_individual*`, `insert_concepts_to_individual_concept_set`,
//! `create_successor_individual` and the clash/OR sites run once per concept
//! addition, and the KPSet classification phase makes hundreds of millions of
//! those additions (ore_ont_3215: 18,323 satisfiability jobs over a 54,974-class
//! terminology). A `getenv` there, where `std::env::var` additionally takes the
//! process-wide environment lock and allocates a `String`, costs more than the
//! Konclude rule work it guards. That regression cost ore_ont_3215 its
//! 240-second budget once already.
//!
//! Diagnostics stay available: every gate is read once through the cached
//! accessors in `konclude_ht::completion` (and `saturation` for its own hot
//! path), so `KM_BRIDGE_WATCH_TAG=…` behaves exactly as before.

use std::path::{Path, PathBuf};

/// Files whose bodies are the per-concept / per-rule completion hot path.
/// `mod.rs` is where the cached accessors themselves live, so it is exempt.
fn guarded_files(root: &Path) -> Vec<PathBuf> {
    let completion = root.join("src/konclude_ht/completion");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&completion)
        .expect("completion directory")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .filter(|path| {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            // `mod.rs` defines the cached accessors; `selftest.rs`/`classify_test.rs`
            // are test-only and may configure the environment directly.
            name != "mod.rs" && name != "selftest.rs" && name != "classify_test.rs"
        })
        .collect();
    files.push(root.join("src/konclude_ht/process/context.rs"));
    files.sort();
    files
}

/// A `#[cfg(test)]` module inside a guarded file may legitimately read the
/// environment; only the shipping bodies are covered. Cheap approximation:
/// stop scanning at the first `#[cfg(test)]` attribute.
fn shipping_source(text: &str) -> &str {
    match text.find("#[cfg(test)]") {
        Some(at) => &text[..at],
        None => text,
    }
}

/// This process-context accessor already caches its lookup. Recognize only
/// its static initializer, not the whole function/file: an additional read
/// outside the initializer must still fail the guard. Removing the static or
/// get_or_init wrapper must also remove this exemption.
fn cached_threshold_initializer(text: &str) -> Option<std::ops::Range<usize>> {
    let prefix = "fn saturation_label_copy_threshold() -> usize {\n    static THRESHOLD: OnceLock<usize> = OnceLock::new();\n    *THRESHOLD.get_or_init(|| {\n";
    let start = text.find(prefix)? + prefix.len();
    let end = start + text[start..].find("\n    })")?;
    Some(start..end)
}

fn uncached_reads(text: &str) -> Vec<(usize, &str)> {
    let cached = cached_threshold_initializer(text);
    let mut offset = 0;
    text.lines()
        .enumerate()
        .filter_map(|(index, line)| {
            let start = offset;
            offset += line.len() + 1;
            (line.contains("std::env::var")
                && !line.trim_start().starts_with("//")
                && !cached.as_ref().is_some_and(|range| range.contains(&start)))
            .then_some((index, line))
        })
        .collect()
}

#[test]
fn completion_rule_bodies_never_call_getenv_inline() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut offenders: Vec<String> = Vec::new();
    for path in guarded_files(&root) {
        let text = std::fs::read_to_string(&path).expect("read guarded source");
        for (index, line) in uncached_reads(shipping_source(&text)) {
            offenders.push(format!(
                "{}:{}: {}",
                path.file_name().unwrap().to_string_lossy(),
                index + 1,
                line.trim()
            ));
        }
    }
    assert!(
        offenders.is_empty(),
        "inline getenv in the completion hot path; route it through a cached \
         accessor in `konclude_ht::completion` instead:\n{}",
        offenders.join("\n")
    );
}

#[test]
fn guard_distinguishes_static_initializers_from_repeated_reads() {
    let cached = "fn saturation_label_copy_threshold() -> usize {\n    static THRESHOLD: OnceLock<usize> = OnceLock::new();\n    *THRESHOLD.get_or_init(|| {\n        std::env::var(\"LIMIT\").ok().and_then(|s| s.parse().ok()).unwrap_or(128)\n    })\n}\n";
    assert!(uncached_reads(cached).is_empty());
    assert_eq!(
        uncached_reads(&cached.replace("static THRESHOLD", "let THRESHOLD")).len(),
        1
    );
    assert_eq!(
        uncached_reads(&cached.replace("get_or_init", "initialize_again")).len(),
        1
    );
    let with_hot_read = format!("{cached}\nfn apply_rule() {{ std::env::var_os(\"HOT\"); }}\n");
    assert_eq!(uncached_reads(&with_hot_read).len(), 1);
    let after_initializer = cached.replace("\n}\n", "\n    std::env::var_os(\"HOT\");\n}\n");
    assert_eq!(uncached_reads(&after_initializer).len(), 1);
}
