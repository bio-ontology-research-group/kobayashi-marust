//! `KM_FRONTEND_CHECK=1`: compare the answer of `km classify` with the Lean
//! OWL reference procedure (`km-owl-reference`, `lean/KMOWLReferenceCheck.lean`)
//! on the same OFN text (docs/V1.6.2-FRONTEND-PLAN.md, section 7, phase A).
//!
//! The Lean executable parses the text, translates it into the normal forms
//! of the v1.6.0 reference procedures and publishes only through
//! `owlReference`'s equation, so its answer is exact under the OWL 2 direct
//! semantics (`owlReference_sound`, `owlReadout_exact`). When km's answer
//! agrees with it, km's answer is exact too.
//!
//! After km has its final answer (any route), with `KM_FRONTEND_CHECK=1`:
//!
//! * the checker is `KM_OWL_REFERENCE_CHECKER`, else
//!   `lean/.lake/build/bin/km-owl-reference`; it runs on the input file with
//!   `--procedure el-then-alc` under `KM_FRONTEND_CHECK_BUDGET_S` (default
//!   300 s) and a 256 MiB Lean stack, as the reference stage does;
//! * the comparison uses the normal form of the v1.6.0 digest
//!   (`parse_answer_digest` of the checkers-on suite tooling): the
//!   inconsistency verdict; on a consistent ontology the unsatisfiable set
//!   and the subsumptions between named classes with a satisfiable
//!   subclass, reflexive pairs and `owl:Thing`/`owl:Nothing` dropped. km's
//!   names are expanded with the document's prefixes before the comparison,
//!   because the Lean parser compares expanded IRIs;
//! * with `KM_TIMING` it prints `KM_TIMING KM_FRONTEND_CHECK agreed
//!   procedure=<p>`, `... disagreed: <first differing item>` or `...
//!   declined: <reason>`, the checker's phase lines as `KM_TIMING
//!   KM_FRONTEND_CHECK_PHASE phase=<name> ms=<ms>` and its wall time as
//!   `KM_TIMING KM_FRONTEND_CHECK_WALL ms=<ms>`;
//! * a disagreement fails closed the way `KM_LEAN_CHECKERS` does when a
//!   checker rejects a certificate: `km classify` publishes nothing, prints
//!   `KM_FRONTEND_CHECK fail closed: ...; no answer published` and exits with
//!   `lean_checkers::REJECTED_EXIT` (6). A decline (input outside the
//!   fragment, budget, checker failure or unreadable checker output, an
//!   approximate km answer) changes nothing.
//!
//! Off by default; when off, [`gate`] returns at once.

use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

/// The switch.
pub const ENABLE_ENV: &str = "KM_FRONTEND_CHECK";
/// The checker executable.
pub const CHECKER_ENV: &str = "KM_OWL_REFERENCE_CHECKER";
/// Wall-clock budget of the checker in seconds.
pub const BUDGET_ENV: &str = "KM_FRONTEND_CHECK_BUDGET_S";
const DEFAULT_BUDGET_S: f64 = 300.0;
const OUTPUT_FORMAT: &str = "owl-sparse-v1";
const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";

/// Whether `KM_FRONTEND_CHECK=1`.
pub fn enabled() -> bool {
    std::env::var(ENABLE_ENV).as_deref() == Ok("1")
}

/// The result of one check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Agreed { procedure: String },
    Disagreed { procedure: String, first: String },
    Declined { reason: String },
}

/// km's answer as the check reads it. `pairs` calls its argument once per
/// published subsumption `(sub, sup)`.
pub struct KmAnswer<'a> {
    pub consistent: bool,
    pub dropped: usize,
    pub approximate: Option<&'a str>,
    pub unsatisfiable: &'a [String],
    pub pairs: &'a dyn Fn(&mut dyn FnMut(&str, &str)),
}

/// Run the check when it is on, print its `KM_TIMING` lines, and return
/// `Err(message)` when the reference procedure disagrees with the answer (the
/// caller then publishes nothing and exits with
/// `lean_checkers::REJECTED_EXIT`).
pub fn gate(ontology: &Path, answer: &KmAnswer<'_>) -> Result<(), String> {
    if !enabled() {
        return Ok(());
    }
    let timing = std::env::var_os("KM_TIMING").is_some();
    let outcome = check(ontology, answer, timing);
    if timing {
        match &outcome {
            Outcome::Agreed { procedure } => {
                eprintln!("KM_TIMING KM_FRONTEND_CHECK agreed procedure={procedure}")
            }
            Outcome::Disagreed { procedure, first } => {
                eprintln!("KM_TIMING KM_FRONTEND_CHECK disagreed: {first} (procedure={procedure})")
            }
            Outcome::Declined { reason } => {
                eprintln!("KM_TIMING KM_FRONTEND_CHECK declined: {reason}")
            }
        }
    }
    match outcome {
        Outcome::Disagreed { procedure, first } => Err(format!(
            "KM_FRONTEND_CHECK fail closed: km-owl-reference (procedure {procedure}) disagrees with the answer ({first}); no answer published"
        )),
        _ => Ok(()),
    }
}

fn budget() -> std::time::Duration {
    let secs = std::env::var(BUDGET_ENV)
        .ok()
        .and_then(|v| v.parse::<f64>().ok())
        .filter(|v| v.is_finite() && *v >= 0.0)
        .unwrap_or(DEFAULT_BUDGET_S);
    std::time::Duration::from_secs_f64(secs)
}

fn checker_path() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os(CHECKER_ENV).filter(|v| !v.is_empty()) {
        let path = PathBuf::from(p);
        return path.is_file().then_some(path);
    }
    let rel = PathBuf::from("lean/.lake/build/bin/km-owl-reference");
    if rel.is_file() {
        return Some(rel);
    }
    let from_manifest = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(|root| root.join("lean/.lake/build/bin/km-owl-reference"))?;
    from_manifest.is_file().then_some(from_manifest)
}

/// Run the checker and compare.
pub fn check(ontology: &Path, answer: &KmAnswer<'_>, timing: bool) -> Outcome {
    let declined = |reason: String| Outcome::Declined { reason };
    if let Some(reason) = answer.approximate {
        return declined(format!("km answer is approximate: {reason}"));
    }
    if answer.consistent && answer.dropped > 0 {
        return declined(format!("km answer dropped {} axiom(s)", answer.dropped));
    }
    let Some(checker) = checker_path() else {
        return declined("no km-owl-reference checker".to_string());
    };
    let started = std::time::Instant::now();
    let mut command = crate::lean_checkers::CheckerCommand::new(&checker);
    command
        .time_limit(Some(budget()))
        .args(["--procedure", "el-then-alc"])
        .arg(ontology);
    if timing {
        command.env("KM_REFERENCE_TIMING", "1");
    }
    let (output, timed_out) = match command.output_timed() {
        Ok(result) => result,
        Err(error) => return declined(format!("cannot run {}: {error}", checker.display())),
    };
    if timing {
        for line in String::from_utf8_lossy(&output.stderr).lines() {
            if let Some(rest) = line.strip_prefix("KM_REFERENCE_TIMING ") {
                eprintln!("KM_TIMING KM_FRONTEND_CHECK_PHASE {rest}");
            }
        }
        eprintln!(
            "KM_TIMING KM_FRONTEND_CHECK_WALL ms={}",
            started.elapsed().as_millis()
        );
    }
    if timed_out {
        return declined("budget".to_string());
    }
    if !output.status.success() {
        return declined(super::reference_checker_failure_reason(
            &output.stdout,
            &output.stderr,
            &output.status,
        ));
    }
    let reference = match parse_reference(&output.stdout) {
        Ok(reference) => reference,
        Err(reason) => return declined(reason),
    };
    let prefixes = match document_prefixes(ontology) {
        Ok(prefixes) => prefixes,
        Err(reason) => return declined(reason),
    };
    let verbatim = match document_verbatim_names(ontology, &prefixes) {
        Ok(verbatim) => verbatim,
        Err(reason) => return declined(reason),
    };
    compare_with(&reference, answer, &prefixes, &verbatim)
}

/// The full IRIs `<p:x>` of the document whose text starts with a known
/// prefix `p:`. km prints such an IRI as `p:x`, like an abbreviated IRI, but
/// it is the IRI `p:x` itself: `builtin_aliases::canonicalize` respells every
/// abbreviated `p:x` of such a document in full. So the comparison must not
/// expand these names. Empty, without a token scan, when the text has no
/// `<p:` at all.
fn document_verbatim_names(
    ontology: &Path,
    prefixes: &BTreeMap<String, String>,
) -> Result<std::collections::HashSet<String>, String> {
    let mut verbatim = std::collections::HashSet::new();
    let text = std::fs::read_to_string(ontology)
        .map_err(|err| format!("cannot read {}: {err}", ontology.display()))?;
    if !prefixes.keys().any(|prefix| text.contains(&format!("<{prefix}:"))) {
        return Ok(verbatim);
    }
    for token in crate::frontend::sexpr::tokens(&text) {
        let iri = token.strip_prefix("^^").unwrap_or(token);
        if let Some(iri) = iri.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
            if iri.split_once(':').is_some_and(|(prefix, _)| prefixes.contains_key(prefix)) {
                verbatim.insert(iri.to_string());
            }
        }
    }
    Ok(verbatim)
}

#[derive(Debug, serde::Deserialize)]
struct ReferenceRow<'a> {
    #[serde(borrow)]
    sub: Cow<'a, str>,
    #[serde(borrow)]
    sups: Vec<Cow<'a, str>>,
}

/// The `owl-sparse-v1` answer of `km-owl-reference`.
#[derive(Debug, serde::Deserialize)]
pub(crate) struct ReferenceAnswer<'a> {
    format: String,
    procedure: String,
    inconsistent: bool,
    #[serde(borrow)]
    unsat: Vec<Cow<'a, str>>,
    #[serde(borrow)]
    rows: Vec<ReferenceRow<'a>>,
}

pub(crate) fn parse_reference(stdout: &[u8]) -> Result<ReferenceAnswer<'_>, String> {
    let parsed: ReferenceAnswer<'_> = serde_json::from_slice(stdout)
        .map_err(|err| format!("invalid checker output JSON: {err}"))?;
    if parsed.format != OUTPUT_FORMAT {
        let format: String = parsed.format.chars().take(64).collect();
        return Err(format!("unsupported checker output format: {format}"));
    }
    Ok(parsed)
}

/// The prefix map of the document (its `Prefix` declarations and the four
/// standard prefixes), read from the head of the file. The declarations come
/// before `Ontology(`, so a few MiB normally hold them; the whole file is read
/// when they do not.
fn document_prefixes(ontology: &Path) -> Result<BTreeMap<String, String>, String> {
    use std::io::Read;
    const HEAD: u64 = 4 << 20;
    let read_err = |err: std::io::Error| format!("cannot read {}: {err}", ontology.display());
    let mut head = Vec::new();
    std::fs::File::open(ontology)
        .map_err(read_err)?
        .take(HEAD)
        .read_to_end(&mut head)
        .map_err(read_err)?;
    let text = String::from_utf8_lossy(&head);
    if let Ok(map) = crate::frontend::conformance::prefixes(&text) {
        if text.contains("Ontology") || (head.len() as u64) < HEAD {
            return Ok(map);
        }
    }
    let text = std::fs::read_to_string(ontology).map_err(read_err)?;
    crate::frontend::conformance::prefixes(&text).map_err(|err| format!("prefixes: {err}"))
}

/// The expanded IRI of a name as km prints it: `p:local` with a declared
/// prefix `p` expands, anything else (a full IRI) is kept.
pub(crate) fn expand<'n>(name: &'n str, prefixes: &BTreeMap<String, String>) -> Cow<'n, str> {
    let name = name
        .strip_prefix('<')
        .and_then(|s| s.strip_suffix('>'))
        .unwrap_or(name);
    if let Some((prefix, local)) = name.split_once(':') {
        if let Some(namespace) = prefixes.get(prefix) {
            return Cow::Owned(format!("{namespace}{local}"));
        }
    }
    Cow::Borrowed(name)
}

#[derive(Default)]
struct Interner {
    ids: HashMap<String, u32>,
    names: Vec<String>,
}

impl Interner {
    fn id(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.ids.get(name) {
            return id;
        }
        let id = self.names.len() as u32;
        self.ids.insert(name.to_string(), id);
        self.names.push(name.to_string());
        id
    }
}

fn is_builtin(iri: &str) -> bool {
    iri == OWL_THING || iri == OWL_NOTHING
}

/// The first element of exactly one of two sorted, deduplicated lists, with
/// the side that holds it (`true`: the first list).
fn first_difference<T: Ord + Copy>(left: &[T], right: &[T]) -> Option<(T, bool)> {
    let (mut i, mut j) = (0, 0);
    while i < left.len() && j < right.len() {
        match left[i].cmp(&right[j]) {
            std::cmp::Ordering::Equal => {
                i += 1;
                j += 1;
            }
            std::cmp::Ordering::Less => return Some((left[i], true)),
            std::cmp::Ordering::Greater => return Some((right[j], false)),
        }
    }
    if i < left.len() {
        return Some((left[i], true));
    }
    if j < right.len() {
        return Some((right[j], false));
    }
    None
}

fn sides(km_holds: bool) -> &'static str {
    if km_holds {
        "km=yes reference=no"
    } else {
        "km=no reference=yes"
    }
}

/// Compare km's answer with the reference answer in the digest's normal form.
pub(crate) fn compare(
    reference: &ReferenceAnswer<'_>,
    answer: &KmAnswer<'_>,
    prefixes: &BTreeMap<String, String>,
) -> Outcome {
    compare_with(reference, answer, prefixes, &std::collections::HashSet::new())
}

/// [`compare`], keeping the names in `verbatim` (full IRIs that read like
/// abbreviated ones, [`document_verbatim_names`]) unexpanded.
pub(crate) fn compare_with(
    reference: &ReferenceAnswer<'_>,
    answer: &KmAnswer<'_>,
    prefixes: &BTreeMap<String, String>,
    verbatim: &std::collections::HashSet<String>,
) -> Outcome {
    let expand = |name: &'_ str| -> String {
        if verbatim.contains(name) {
            name.to_string()
        } else {
            expand(name, prefixes).into_owned()
        }
    };
    let procedure = reference.procedure.clone();
    let disagreed = |first: String| Outcome::Disagreed {
        procedure: procedure.clone(),
        first,
    };
    let km_inconsistent = !answer.consistent;
    if km_inconsistent != reference.inconsistent {
        return disagreed(format!(
            "inconsistent: km={} reference={}",
            km_inconsistent, reference.inconsistent
        ));
    }
    if reference.inconsistent {
        return Outcome::Agreed { procedure };
    }
    let mut names = Interner::default();
    // Unsatisfiable classes.
    let mut ref_unsat: Vec<u32> = reference.unsat.iter().map(|n| names.id(n)).collect();
    let mut km_unsat: Vec<u32> = answer
        .unsatisfiable
        .iter()
        .map(|n| expand(n))
        .filter(|n| !is_builtin(n))
        .map(|n| names.id(&n))
        .collect();
    ref_unsat.sort_unstable();
    ref_unsat.dedup();
    km_unsat.sort_unstable();
    km_unsat.dedup();
    if let Some((id, km_holds)) = first_difference(&km_unsat, &ref_unsat) {
        return disagreed(format!(
            "unsatisfiable {}: {}",
            names.names[id as usize],
            sides(km_holds)
        ));
    }
    // Subsumptions with a satisfiable subclass.
    let mut ref_pairs: Vec<(u32, u32)> = Vec::new();
    for row in &reference.rows {
        let sub = names.id(&row.sub);
        for sup in &row.sups {
            let sup = names.id(sup);
            if sup != sub {
                ref_pairs.push((sub, sup));
            }
        }
    }
    let unsat: std::collections::HashSet<u32> = km_unsat.iter().copied().collect();
    let mut km_pairs: Vec<(u32, u32)> = Vec::new();
    (answer.pairs)(&mut |sub: &str, sup: &str| {
        let sub = expand(sub);
        let sup = expand(sup);
        if is_builtin(&sub) || is_builtin(&sup) {
            return;
        }
        let sub = names.id(&sub);
        let sup = names.id(&sup);
        if sub != sup && !unsat.contains(&sub) {
            km_pairs.push((sub, sup));
        }
    });
    ref_pairs.sort_unstable();
    ref_pairs.dedup();
    km_pairs.sort_unstable();
    km_pairs.dedup();
    if let Some(((sub, sup), km_holds)) = first_difference(&km_pairs, &ref_pairs) {
        return disagreed(format!(
            "SubClassOf({} {}): {}",
            names.names[sub as usize],
            names.names[sup as usize],
            sides(km_holds)
        ));
    }
    Outcome::Agreed { procedure }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prefixes() -> BTreeMap<String, String> {
        let mut map = BTreeMap::new();
        map.insert(String::new(), "http://ex.org/o#".to_string());
        map.insert("owl".to_string(), "http://www.w3.org/2002/07/owl#".to_string());
        map
    }

    fn reference(json: &str) -> ReferenceAnswer<'_> {
        parse_reference(json.as_bytes()).expect("valid reference answer")
    }

    fn km<'a>(
        consistent: bool,
        unsat: &'a [String],
        pairs: &'a dyn Fn(&mut dyn FnMut(&str, &str)),
    ) -> KmAnswer<'a> {
        KmAnswer {
            consistent,
            dropped: 0,
            approximate: None,
            unsatisfiable: unsat,
            pairs,
        }
    }

    const REF: &str = r#"{"format":"owl-sparse-v1","procedure":"el","inconsistent":false,
        "unsat":["http://ex.org/o#U"],
        "rows":[{"sub":"http://ex.org/o#A","sups":["http://ex.org/o#A","http://ex.org/o#B"]},
                {"sub":"http://ex.org/o#B","sups":["http://ex.org/o#B"]}]}"#;

    #[test]
    fn expand_uses_declared_prefixes_and_keeps_full_iris() {
        let p = prefixes();
        assert_eq!(expand(":A", &p), "http://ex.org/o#A");
        assert_eq!(expand("owl:Thing", &p), OWL_THING);
        assert_eq!(expand("http://x.org/A", &p), "http://x.org/A");
        assert_eq!(expand("<http://x.org/A>", &p), "http://x.org/A");
    }

    #[test]
    fn agreement_in_the_digest_normal_form() {
        let r = reference(REF);
        let unsat = vec![":U".to_string()];
        // km lists the unsatisfiable class's own rows, a pair to owl:Thing and
        // spells names with the prefix: all normalised away.
        let pairs = |f: &mut dyn FnMut(&str, &str)| {
            f(":A", ":B");
            f(":U", ":A");
            f(":U", ":B");
            f(":A", "owl:Thing");
        };
        let got = compare(&r, &km(true, &unsat, &pairs), &prefixes());
        assert_eq!(got, Outcome::Agreed { procedure: "el".into() });
    }

    #[test]
    fn a_missing_or_extra_subsumption_disagrees() {
        let r = reference(REF);
        let unsat = vec![":U".to_string()];
        let missing = |_: &mut dyn FnMut(&str, &str)| {};
        let got = compare(&r, &km(true, &unsat, &missing), &prefixes());
        assert_eq!(
            got,
            Outcome::Disagreed {
                procedure: "el".into(),
                first: "SubClassOf(http://ex.org/o#A http://ex.org/o#B): km=no reference=yes".into()
            }
        );
        let extra = |f: &mut dyn FnMut(&str, &str)| {
            f(":A", ":B");
            f(":B", ":A");
        };
        let got = compare(&r, &km(true, &unsat, &extra), &prefixes());
        assert!(
            matches!(&got, Outcome::Disagreed { first, .. } if first == "SubClassOf(http://ex.org/o#B http://ex.org/o#A): km=yes reference=no"),
            "{got:?}"
        );
    }

    #[test]
    fn unsatisfiable_sets_and_verdicts_are_compared() {
        let r = reference(REF);
        let pairs = |f: &mut dyn FnMut(&str, &str)| f(":A", ":B");
        let none: Vec<String> = Vec::new();
        let got = compare(&r, &km(true, &none, &pairs), &prefixes());
        assert!(
            matches!(&got, Outcome::Disagreed { first, .. } if first == "unsatisfiable http://ex.org/o#U: km=no reference=yes"),
            "{got:?}"
        );
        let got = compare(&r, &km(false, &none, &pairs), &prefixes());
        assert!(
            matches!(&got, Outcome::Disagreed { first, .. } if first == "inconsistent: km=true reference=false"),
            "{got:?}"
        );
    }

    #[test]
    fn inconsistent_answers_agree_on_the_verdict_alone() {
        let r = reference(
            r#"{"format":"owl-sparse-v1","procedure":"alc","inconsistent":true,"unsat":[],"rows":[]}"#,
        );
        let unsat = vec![":A".to_string(), ":B".to_string()];
        let pairs = |f: &mut dyn FnMut(&str, &str)| {
            f(":A", ":B");
            f(":B", ":A");
        };
        let got = compare(&r, &km(false, &unsat, &pairs), &prefixes());
        assert_eq!(got, Outcome::Agreed { procedure: "alc".into() });
    }

    #[test]
    fn malformed_checker_output_is_not_an_answer() {
        assert!(parse_reference(b"{}").unwrap_err().contains("invalid checker output JSON"));
        let err = parse_reference(
            br#"{"format":"sparse-v1","procedure":"el","inconsistent":false,"unsat":[],"rows":[]}"#,
        )
        .unwrap_err();
        assert!(err.contains("unsupported checker output format"), "{err}");
    }

    #[test]
    fn first_difference_reports_the_side() {
        assert_eq!(first_difference(&[1, 2, 3], &[1, 2, 3]), None);
        assert_eq!(first_difference(&[1, 3], &[1, 2, 3]), Some((2, false)));
        assert_eq!(first_difference(&[1, 2, 4], &[1, 2]), Some((4, true)));
    }

    #[test]
    fn off_by_default() {
        if std::env::var_os(ENABLE_ENV).is_none() {
            assert!(!enabled());
        }
    }
}
