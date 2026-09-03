//! Frontend invocation: spawn the `ofn` worker in `--meta` split mode so the
//! (up to ~580 MB) clause set streams straight to a temp file and never enters
//! this process's memory. Port of `owl_classify.run_ofn_split`.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;
use std::process::{Command, Stdio};

use super::tmpfile::TempPath;
use super::{Config, OrchestrateError};

/// Side data from `ofn --meta` (everything needed to map engine output back to
/// OWL, minus the clauses). Mirrors `bin/ofn.rs`'s `Meta`.
#[derive(serde::Deserialize)]
pub struct Meta {
    pub iri_map: BTreeMap<String, String>,
    pub named: Vec<String>,
    pub el_rbox_safe: bool,
    #[serde(default)]
    pub abox_inconsistent: bool,
    #[serde(default)]
    pub asserted_classes: Vec<String>,
    #[serde(default)]
    pub profile: crate::frontend::profile::OntologyProfile,
    #[serde(default = "manual_route")]
    pub route: String,
}

fn manual_route() -> String {
    "manual".to_string()
}

/// Returns the clauses temp file (caller owns it; reasoners read it as stdin)
/// and the parsed meta. The meta temp file is unlinked before returning.
/// The clauses temp file the reasoners consume (`{clauses, cardinalities,
/// rules}` — matches `cli::OfnClausesOnly` exactly, the format the `ofn`
/// subprocess writes).
/// Below this ontology-file size, run the frontend IN-PROCESS (call
/// `ofn_to_clauses` directly) instead of forking the `ofn` subprocess. Measured:
/// on trivial onts the subprocess fork/exec + meta round-trip is ~15-25 ms of
/// the ~0.12 s total — the difference between a WIN and a tie against Konclude on
/// the ~125 near-tie onts. Kept SMALL so the frontend's transient parse peak
/// (multi-GB on the giants) stays isolated in the subprocess: at 4 MB the
/// in-process transient peak is only tens of MB and is freed before the engine
/// runs, so the classify RSS high-water-mark is unaffected.
const IN_PROCESS_OFN_MAX: u64 = 4 << 20;
/// Retain a parsed general-HT input across the frontend/solver boundary only
/// for the measured small-source band.  Large sources that pass the lexical
/// EL screen can still select general HT after full profiling; retaining their
/// typed input makes a declined in-process attempt coexist with the automatic
/// fallback and sharply raises both wall time and peak RSS.  They keep the
/// established serialized, isolated worker path instead.
const IN_PROCESS_GENERAL_HT_MAX: usize = 2 << 20;

fn ht_typed_handoff_candidate(route: Option<crate::routing::Route>, source_bytes: usize) -> bool {
    match route {
        Some(crate::routing::Route::HtShoq) => true,
        Some(crate::routing::Route::HtGeneral | crate::routing::Route::HtBridge) => {
            source_bytes < IN_PROCESS_GENERAL_HT_MAX
        }
        _ => false,
    }
}
/// Upper source size for the in-process frontend on the exact-EL band.
/// The 4 MiB to 60 MB band was screened end to end under explicit threshold
/// experiments: every exact
/// EL member dropped both worker boundaries (frontend subprocess and EL
/// completion subprocess), and its summed process-tree peak stayed flat or
/// fell because the orchestrator no longer sits beside a child that holds
/// the same clause set. Non-EL members retain freed frontend heap beside a
/// CB or HT child instead, so they keep the isolated frontend:
/// `source_looks_exact_el` separates the two cases before parsing.
const MEASURED_IN_PROCESS_EL_OFN_MAX: u64 = 60_000_000;

/// Functional-syntax constructor names that put a source outside the exact
/// EL completion route or on an identity-bearing ABox family that the
/// completion route never serves. Inverse, symmetric, transitive, and
/// chained object properties stay admitted: the EL route accepts them when
/// the relevance slice proves them inert, and every measured exact-EL band
/// member uses at least one of them.
const NON_EL_CONSTRUCTORS: &[&str] = &[
    "ObjectUnionOf",
    "ObjectComplementOf",
    "ObjectAllValuesFrom",
    "ObjectMinCardinality",
    "ObjectMaxCardinality",
    "ObjectExactCardinality",
    "ObjectOneOf",
    "ObjectHasValue",
    "ObjectHasSelf",
    "FunctionalObjectProperty",
    "InverseFunctionalObjectProperty",
    "AsymmetricObjectProperty",
    "IrreflexiveObjectProperty",
    "ReflexiveObjectProperty",
    "DisjointObjectProperties",
    "SameIndividual",
    "DifferentIndividuals",
    "NegativeObjectPropertyAssertion",
    "HasKey",
    "DLSafeRule",
    "Import",
];

/// One-pass lexical screen for the measured exact-EL band. Every functional
/// syntax constructor is the identifier that immediately precedes an opening
/// parenthesis, so the scan jumps between parentheses and inspects only the
/// identifier behind each one. A source is admitted when no identifier names
/// a non-EL constructor and none starts with `Data` (data properties,
/// datatypes, and concrete-domain restrictions). The screen fails closed: a
/// rejected source keeps the isolated frontend and produces byte-identical
/// output through that established path, so a false rejection costs only the
/// worker boundaries it would have removed.
fn source_looks_exact_el(text: &str) -> bool {
    source_looks_el_with_identity(text, false)
}

/// Broader process-boundary screen for the certified positive-EL ABox family.
/// `SameIndividual` and `DifferentIndividuals` are retained by the typed
/// frontend and checked exactly by `positive_abox_classify`; every other
/// non-EL constructor still fails closed here. The parsed profile, not this
/// lexical hint, remains the authority for selecting and publishing ELC.
fn source_looks_positive_el_abox(text: &str) -> bool {
    source_looks_el_with_identity(text, true)
}

fn source_looks_el_with_identity(text: &str, allow_identity: bool) -> bool {
    let bytes = text.as_bytes();
    let mut cursor = 0usize;
    while let Some(offset) = text[cursor..].find('(') {
        let paren = cursor + offset;
        let mut start = paren;
        while start > cursor
            && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_')
        {
            start -= 1;
        }
        let identifier = &bytes[start..paren];
        if !identifier.is_empty()
            && (identifier.starts_with(b"Data")
                || NON_EL_CONSTRUCTORS.iter().any(|token| {
                    token.as_bytes() == identifier
                        && !(allow_identity
                            && matches!(*token, "SameIndividual" | "DifferentIndividuals"))
                }))
        {
            return false;
        }
        cursor = paren + 1;
    }
    true
}

/// The measured exact-EL band between the unconditional small in-process
/// bound and the screened upper size.
fn in_process_el_band(source_bytes: u64) -> bool {
    (IN_PROCESS_OFN_MAX..MEASURED_IN_PROCESS_EL_OFN_MAX).contains(&source_bytes)
}
const GIANT_IN_PROCESS_OFN_MIN: u64 = 300 << 20;
const GIANT_IN_PROCESS_OFN_MAX: u64 = 600 << 20;

fn giant_source_uses_certified_rbox(path: &Path) -> std::io::Result<bool> {
    const TOKENS: &[&[u8]] = &[
        b"InverseObjectProperties(",
        b"SymmetricObjectProperty(",
        b"TransitiveObjectProperty(",
    ];
    const CHUNK: usize = 64 << 10;
    const TAIL: u64 = 1 << 20;
    let overlap = TOKENS.iter().map(|token| token.len()).max().unwrap() - 1;
    let mut file = File::open(path)?;
    let len = file.metadata()?.len();
    if len > TAIL {
        file.seek(SeekFrom::End(-(TAIL as i64)))?;
        let mut tail = Vec::with_capacity(TAIL as usize);
        file.read_to_end(&mut tail)?;
        if TOKENS
            .iter()
            .any(|token| tail.windows(token.len()).any(|window| window == *token))
        {
            return Ok(true);
        }
        file.seek(SeekFrom::Start(0))?;
    }
    let mut buffer = vec![0; CHUNK + overlap];
    let mut carried = 0;
    loop {
        let read = file.read(&mut buffer[carried..])?;
        let available = carried + read;
        if TOKENS.iter().any(|token| {
            buffer[..available]
                .windows(token.len())
                .any(|window| window == *token)
        }) {
            return Ok(true);
        }
        if read == 0 {
            return Ok(false);
        }
        carried = overlap.min(available);
        buffer.copy_within(available - carried..available, 0);
    }
}

fn use_in_process_ofn(path: &Path, source_bytes: u64) -> bool {
    if let Some(max) = std::env::var("KM_INPROC_OFN_MAX")
        .ok()
        .and_then(|value| value.parse().ok())
    {
        return source_bytes < max;
    }
    if source_bytes < IN_PROCESS_OFN_MAX {
        return true;
    }
    GIANT_IN_PROCESS_OFN_MIN <= source_bytes
        && source_bytes < GIANT_IN_PROCESS_OFN_MAX
        && !giant_source_uses_certified_rbox(path).unwrap_or(true)
}

/// In-process port of the `ofn --meta` subprocess: parse + clausify directly,
/// write the clauses file the engine reads, and return the parsed `Meta`. The
/// clause set is dropped before returning, so no frontend memory is held during
/// the engine run. `ofn_to_clauses` is the SAME function the subprocess calls,
/// so the output is byte-for-byte identical.
/// Returns the parsed meta, the typed clause vector when the selected exact
/// EL leaf consumes it in process, and otherwise the compact EL sidecar for
/// an exact EL worker (the same `--elc-binary` handoff the subprocess
/// frontend writes). Every other route reads the serialized JSON file.
fn run_ofn_in_process(
    text: &str,
    clauses_path: &Path,
) -> Result<(Meta, Option<crate::json_io::JInput>, Option<TempPath>), OrchestrateError> {
    let result = match crate::frontend::ofn_to_clauses(text) {
        Ok(r) => r,
        Err(e) => return Err(OrchestrateError::OutOfFragment(e.0)),
    };
    let meta = Meta {
        iri_map: result.iri_map,
        named: result.named,
        el_rbox_safe: result.el_rbox_safe,
        abox_inconsistent: result.abox_inconsistent,
        asserted_classes: result.asserted_classes,
        profile: result.profile,
        route: result.route,
    };
    let mut out = crate::json_io::JInput {
        clauses: result.clauses,
        cb_typed_source: None,
        rbox: result.rbox,
        cardinalities: result.cardinalities,
        definers: result.definers,
        source_axioms: result.source_axioms,
        nominal_abox: result.nominal_abox,
        rules: result.rules,
    };
    // Retain this representation only when the selected leaf consumes it
    // directly. Dropping every other input preserves the old frontend lifetime
    // and avoids making parser allocations part of the classifier high-water.
    let selected_route = meta.route.parse::<crate::routing::Route>().ok();
    let cacheable_el = std::env::var_os("KM_NO_INPROC_ELC").is_none()
        && std::env::var_os("KM_EL_ABOX_CHECK").is_none()
        && meta.el_rbox_safe
        && selected_route.is_some_and(|route| super::use_atomic_inproc_elc(route, &meta.profile));
    let cacheable_ht = std::env::var_os("KM_NO_INPROC_HT").is_none()
        && ht_typed_handoff_candidate(selected_route, text.len());
    let cacheable = cacheable_el || cacheable_ht;
    // The subprocess JSON path rebuilds an exactly-sized outer clause vector.
    // Match that footprint before retaining frontend-owned clauses across the
    // phase boundary; spare parser growth capacity otherwise survives into EL
    // completion and raises the classify process's high-water mark.
    if cacheable {
        out.clauses.shrink_to_fit();
    }
    // Exact Elc consumes `out` directly. CertifiedElProduction also consumes
    // it directly and recursively reruns this frontend under ProductionAll if
    // its certificate declines, so neither needs an eager serialized copy.
    //
    // An exact EL leaf that is NOT retained in process (the flat and
    // unstructured members of the band) still runs the isolated EL worker.
    // Mirror `cli::run_ofn`: hand that worker the compact typed-clause
    // sidecar instead of a JSON stream it would have to re-parse, and skip
    // the JSON entirely under the same conditions the subprocess frontend
    // uses (no positive-ABox materialization, no rules, no ABox check).
    let binary_sidecar = !cacheable
        && selected_route == Some(crate::routing::Route::Elc)
        && meta.el_rbox_safe
        && !meta.profile.positive_el_abox_materializable
        && meta.profile.source.rule_axioms == 0
        && std::env::var_os("KM_EL_ABOX_CHECK").is_none();
    let mut elc_binary = None;
    if binary_sidecar {
        let sidecar = TempPath::new(".elc.bin");
        let f = File::create(sidecar.path())?;
        let mut w = std::io::BufWriter::new(f);
        crate::json_io::write_elc_binary(&mut w, &out.clauses)?;
        std::io::Write::flush(&mut w)?;
        elc_binary = Some(sidecar);
    } else if !cacheable {
        let f = File::create(clauses_path)?;
        let mut w = std::io::BufWriter::new(f);
        serde_json::to_writer(&mut w, &out)?;
        std::io::Write::flush(&mut w)?;
    }
    let cached = cacheable.then_some(out);
    Ok((meta, cached, elc_binary))
}

pub fn run_ofn_split(cfg: &Config, ont: &Path) -> Result<(TempPath, Meta), OrchestrateError> {
    let (clauses, meta, _cached, _elc_binary) = run_ofn_split_cached(cfg, ont)?;
    Ok((clauses, meta))
}

/// Split frontend output while retaining the already-built typed input for the
/// small in-process path. The serialized file remains authoritative for every
/// subprocess fallback; callers consume the cache only when the selected
/// classifier also runs in this process.
pub fn run_ofn_split_cached(
    cfg: &Config,
    ont: &Path,
) -> Result<
    (
        TempPath,
        Meta,
        Option<crate::json_io::JInput>,
        Option<TempPath>,
    ),
    OrchestrateError,
> {
    let prepared = super::input::prepare(ont)?;
    let ont = prepared.path();
    let clauses = TempPath::new(".clauses.json");

    // In-process fast path for small ontologies (avoids the ofn subprocess).
    // Very large inputs in the measured band also benefit: structured exact-EL
    // leaves can pass their already-built clauses directly to completion, while
    // the two certified-EL controls preserve their isolated completion route.
    // Any failure falls through to the subprocess path below (identical output).
    let source_bytes = std::fs::metadata(ont).map(|m| m.len()).unwrap_or(0);
    let small = use_in_process_ofn(ont, source_bytes);
    // Above the small bound, the measured exact-EL band is admitted only
    // after the lexical screen. The explicit size override keeps its
    // unscreened meaning for experiments.
    let screened_el_band = !small
        && std::env::var_os("KM_INPROC_OFN_MAX").is_none()
        && in_process_el_band(source_bytes);
    if (small || screened_el_band) && std::env::var_os("KM_NO_INPROC_OFN").is_none() {
        let timing = std::env::var_os("KM_TIMING").is_some();
        let t_read = std::time::Instant::now();
        if let Ok(text) = std::fs::read_to_string(ont) {
            let read_s = t_read.elapsed().as_secs_f64();
            let t_screen = std::time::Instant::now();
            let admitted = !screened_el_band
                || source_looks_exact_el(&text)
                || source_looks_positive_el_abox(&text);
            let screen_s = t_screen.elapsed().as_secs_f64();
            if admitted {
                let t_parse = std::time::Instant::now();
                match run_ofn_in_process(&text, clauses.path()) {
                    Ok((meta, cached, elc_binary)) => {
                        if timing {
                            eprintln!(
                                "KM_TIMING in-process frontend: read={read_s:.2}s screen={screen_s:.2}s \
                                 parse+clausify+handoff={:.2}s cached={} sidecar={}",
                                t_parse.elapsed().as_secs_f64(),
                                cached.is_some(),
                                elc_binary.is_some()
                            );
                        }
                        return Ok((clauses, meta, cached, elc_binary));
                    }
                    // OutOfFragment is a real verdict (not a transient failure): surface it
                    // exactly as the subprocess exit-3 path does, don't silently retry.
                    Err(e @ OrchestrateError::OutOfFragment(_)) => return Err(e),
                    Err(_) => { /* fall through to the subprocess path */ }
                }
            } else if timing {
                eprintln!(
                    "KM_TIMING in-process frontend declined by the exact-EL screen: bytes={source_bytes} screen={screen_s:.2}s"
                );
            }
        }
    }

    let meta = TempPath::new(".meta.json");
    let elc_binary = TempPath::new(".elc.bin");
    let stderr = TempPath::new(".ofn.err");

    // This process blocks in `status()` while the isolated frontend parses.
    // A declined in-process attempt above, or the caller's outer frontend on
    // the recursive probe and fallback routes, leaves freed pages here that
    // the process-tree watchdog would otherwise count beside the child.
    crate::mem::release_transient_heap();
    let (ofn_prog, ofn_pre) = cfg.ofn_cmd();
    let status = Command::new(&ofn_prog)
        .args(&ofn_pre)
        .arg(ont)
        .arg("--meta")
        .arg(meta.path())
        .arg("--elc-binary")
        .arg(elc_binary.path())
        .stdin(Stdio::null())
        .stdout(File::create(clauses.path())?)
        .stderr(File::create(stderr.path())?)
        .status()
        .map_err(|e| OrchestrateError::Spawn {
            bin: "ofn".into(),
            source: e,
        })?;

    let code = status.code().unwrap_or(-1);
    if code == 3 {
        let msg = std::fs::read_to_string(stderr.path()).unwrap_or_default();
        let msg = msg.trim();
        return Err(OrchestrateError::OutOfFragment(if msg.is_empty() {
            "out of fragment".into()
        } else {
            msg.into()
        }));
    }
    if code != 0 {
        let msg = std::fs::read_to_string(stderr.path()).unwrap_or_default();
        return Err(OrchestrateError::Worker {
            bin: "ofn".into(),
            code,
            stderr: msg,
        });
    }
    // Read the whole meta file and parse with `from_slice`, NOT
    // `from_reader(File)`: serde_json's reader path is unbuffered here and
    // parses a large meta (ore_ont_10073: 21 MB, 473k iri_map entries) ~14 s
    // vs <1 s from a slice — it was the dominant cost of the frontend phase on
    // large ontologies (19 s → 5 s).
    let meta_bytes = std::fs::read(meta.path())?;
    let meta_parsed: Meta = serde_json::from_slice(&meta_bytes)?;
    let elc_binary = std::fs::metadata(elc_binary.path())
        .ok()
        .filter(|metadata| metadata.len() > 8)
        .map(|_| elc_binary);
    Ok((clauses, meta_parsed, None, elc_binary))
}

/// Run `ofn` once with `KM_ABSORB` forced on/off, streaming the (full) clause
/// set to a temp file (the engine ignores the extra meta keys). Used by the
/// absorption portfolio to obtain the *plain* clause set. Port of
/// `_ofn_clauses_file`; returns None on any failure.
pub fn run_ofn_plain(cfg: &Config, ont: &Path, absorb: bool) -> Option<TempPath> {
    let prepared = super::input::prepare(ont).ok()?;
    let ont = prepared.path();
    let clauses = TempPath::new(".clauses.json");
    let (ofn_prog, ofn_pre) = cfg.ofn_cmd();
    let status = Command::new(&ofn_prog)
        .args(&ofn_pre)
        .arg(ont)
        .stdin(Stdio::null())
        .stdout(File::create(clauses.path()).ok()?)
        .stderr(Stdio::null())
        .env("KM_ABSORB", if absorb { "1" } else { "0" })
        .status()
        .ok()?;
    if status.code() == Some(0) {
        Some(clauses)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::{
        giant_source_uses_certified_rbox, ht_typed_handoff_candidate, in_process_el_band,
        run_ofn_in_process, source_looks_exact_el, source_looks_positive_el_abox,
        use_in_process_ofn, TempPath, IN_PROCESS_GENERAL_HT_MAX, IN_PROCESS_OFN_MAX,
        MEASURED_IN_PROCESS_EL_OFN_MAX,
    };

    #[test]
    fn general_ht_typed_handoff_is_bounded_but_shoq_is_not() {
        use crate::routing::Route;

        assert!(ht_typed_handoff_candidate(
            Some(Route::HtGeneral),
            IN_PROCESS_GENERAL_HT_MAX - 1,
        ));
        assert!(!ht_typed_handoff_candidate(
            Some(Route::HtGeneral),
            IN_PROCESS_GENERAL_HT_MAX,
        ));
        assert!(ht_typed_handoff_candidate(
            Some(Route::HtShoq),
            IN_PROCESS_GENERAL_HT_MAX,
        ));
        assert!(ht_typed_handoff_candidate(
            Some(Route::HtBridge),
            IN_PROCESS_GENERAL_HT_MAX - 1,
        ));
        assert!(!ht_typed_handoff_candidate(
            Some(Route::HtBridge),
            IN_PROCESS_GENERAL_HT_MAX,
        ));
        assert!(!ht_typed_handoff_candidate(Some(Route::Elc), 1));
    }

    #[test]
    fn exact_el_screen_admits_inverse_rich_el_and_rejects_non_el_constructors() {
        assert!(source_looks_exact_el(
            "Ontology(SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>)) \
             SubClassOf(ObjectIntersectionOf(<A> <B>) <C>) \
             InverseObjectProperties(<r> <s>) TransitiveObjectProperty(<r>) \
             SymmetricObjectProperty(<s>) \
             SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>) \
             ClassAssertion(<A> <a>) ObjectPropertyAssertion(<r> <a> <b>) \
             DisjointClasses(<A> <B>) EquivalentClasses(<C> <D>))"
        ));
        for source in [
            "Ontology(SubClassOf(<A> ObjectUnionOf(<B> <C>)))",
            "Ontology(SubClassOf(<A> ObjectComplementOf(<B>)))",
            "Ontology(SubClassOf(<A> ObjectAllValuesFrom(<r> <B>)))",
            "Ontology(SubClassOf(<A> ObjectMaxCardinality(1 <r>)))",
            "Ontology(SubClassOf(<A> ObjectOneOf(<a>)))",
            "Ontology(FunctionalObjectProperty(<r>))",
            "Ontology(Declaration(DataProperty(<p>)))",
            "Ontology(Declaration(Datatype(<d>)))",
            "Ontology(SubClassOf(<A> DataSomeValuesFrom(<p> xsd:integer)))",
            "Ontology(DifferentIndividuals(<a> <b>))",
            "Ontology(SameIndividual(<a> <b>))",
            "Ontology(Import(<http://example.org/o>))",
            "Ontology(DLSafeRule(Body() Head()))",
        ] {
            assert!(!source_looks_exact_el(source), "{source}");
        }
        // Identifiers are matched whole and only in constructor position: a
        // class named after a constructor is still an ordinary class.
        assert!(source_looks_exact_el(
            "Ontology(SubClassOf(<ObjectUnionOf> <B>) SubClassOf(<x:ObjectUnionOfThing> <B>))"
        ));
        assert!(source_looks_exact_el(""));
    }

    #[test]
    fn positive_el_abox_screen_admits_identity_but_no_other_non_el_constructor() {
        assert!(source_looks_positive_el_abox(
            "Ontology(ClassAssertion(<A> <a>) SameIndividual(<a> <b>) \
             DifferentIndividuals(<a> <c>))"
        ));
        for source in [
            "Ontology(SubClassOf(<A> ObjectUnionOf(<B> <C>)) SameIndividual(<a> <b>))",
            "Ontology(SubClassOf(<A> ObjectAllValuesFrom(<r> <B>)) SameIndividual(<a> <b>))",
            "Ontology(Declaration(DataProperty(<p>)) SameIndividual(<a> <b>))",
            "Ontology(NegativeObjectPropertyAssertion(<r> <a> <b>))",
            "Ontology(Import(<http://example.org/o>))",
        ] {
            assert!(!source_looks_positive_el_abox(source), "{source}");
        }
    }

    #[test]
    fn in_process_el_band_sits_between_the_small_and_giant_bounds() {
        assert!(!in_process_el_band(IN_PROCESS_OFN_MAX - 1));
        assert!(in_process_el_band(IN_PROCESS_OFN_MAX));
        assert!(in_process_el_band(MEASURED_IN_PROCESS_EL_OFN_MAX - 1));
        assert!(!in_process_el_band(MEASURED_IN_PROCESS_EL_OFN_MAX));
        // The size rule alone never admits the band: the screen decides.
        let path = TempPath::new(".ofn");
        assert!(use_in_process_ofn(path.path(), IN_PROCESS_OFN_MAX - 1));
        assert!(!use_in_process_ofn(path.path(), IN_PROCESS_OFN_MAX));
        assert!(!use_in_process_ofn(
            path.path(),
            MEASURED_IN_PROCESS_EL_OFN_MAX - 1
        ));
    }

    #[test]
    fn in_process_frontend_writes_the_el_binary_sidecar_for_an_uncached_el_route() {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "elc");
        std::env::remove_var("KM_EL_ABOX_CHECK");
        std::env::remove_var("KM_NO_INPROC_ELC");
        // Five declared classes over three axioms sit below the structured
        // ratio, and the existential excludes the small flat admission, so
        // the exact EL leaf is not retained in process. The worker boundary
        // must then receive the compact handoff, not a JSON stream.
        let source = "Ontology(Declaration(Class(<A>)) Declaration(Class(<B>)) \
                      Declaration(Class(<C>)) Declaration(Class(<D>)) Declaration(Class(<E>)) \
                      SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>)) \
                      SubClassOf(ObjectSomeValuesFrom(<r> <B>) <C>) SubClassOf(<D> <E>))";
        let clauses = TempPath::new(".clauses.json");
        let (meta, cached, sidecar) =
            run_ofn_in_process(source, clauses.path()).expect("frontend parses");
        assert_eq!(meta.route, "elc");
        assert!(meta.el_rbox_safe);
        assert!(cached.is_none());
        let sidecar = sidecar.expect("an uncached exact EL leaf writes the binary sidecar");
        assert!(!clauses.path().exists());
        let bytes = std::fs::read(sidecar.path()).unwrap();
        let decoded = crate::json_io::decode_elc_binary(&bytes)
            .unwrap()
            .expect("compact EL handoff header");
        assert!(!decoded.is_empty());
    }

    #[test]
    fn in_process_frontend_retains_certified_positive_el_abox_input() {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "elc");
        std::env::remove_var("KM_EL_ABOX_CHECK");
        std::env::remove_var("KM_NO_INPROC_ELC");
        let source = "Ontology(SubClassOf(ObjectIntersectionOf(<A> <B>) owl:Nothing) \
                      ClassAssertion(<A> <a>) ClassAssertion(<A> <b>) \
                      SameIndividual(<a> <aa>) DifferentIndividuals(<aa> <b> <c>))";
        let clauses = TempPath::new(".clauses.json");
        let (meta, cached, sidecar) =
            run_ofn_in_process(source, clauses.path()).expect("frontend parses");
        assert_eq!(meta.route, "elc");
        assert!(meta.profile.positive_el_abox_materializable);
        assert!(
            cached.is_some(),
            "certified EL ABox must cross typed handoff"
        );
        assert!(sidecar.is_none());
        assert!(!clauses.path().exists());
    }

    #[test]
    fn in_process_frontend_retains_the_selected_shoq_input() {
        let _guard = crate::routing::EnvironmentGuard::capture();
        // Route selection itself has a separate profile regression test. This
        // fixture exercises the typed-handoff contract of a selected leaf.
        std::env::set_var("KM_ROUTE", "ht_shoq");
        std::env::remove_var("KM_NO_INPROC_HT");
        let source = "Ontology(Declaration(Class(<A>)) Declaration(ObjectProperty(<r>)) \
                      EquivalentClasses(<A> ObjectExactCardinality(128 <r>)))";
        let clauses = TempPath::new(".clauses.json");
        let (meta, cached, sidecar) =
            run_ofn_in_process(source, clauses.path()).expect("frontend parses");
        assert_eq!(meta.route, "ht_shoq");
        assert!(cached.is_some(), "SHOQ must cross the typed handoff");
        assert!(sidecar.is_none());
        assert!(!clauses.path().exists());
    }

    #[test]
    fn in_process_frontend_retains_the_selected_general_ht_input() {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "ht_general");
        std::env::remove_var("KM_NO_INPROC_HT");
        let source = "Ontology(Declaration(Class(<A>)) Declaration(Class(<B>)) \
                      SubClassOf(<A> ObjectComplementOf(<B>)))";
        let clauses = TempPath::new(".clauses.json");
        let (meta, cached, sidecar) =
            run_ofn_in_process(source, clauses.path()).expect("frontend parses");
        assert_eq!(meta.route, "ht_general");
        assert!(cached.is_some(), "general HT must cross the typed handoff");
        assert!(sidecar.is_none());
        assert!(!clauses.path().exists());
    }

    #[test]
    fn in_process_frontend_retains_the_selected_bridge_input() {
        let _guard = crate::routing::EnvironmentGuard::capture();
        std::env::set_var("KM_ROUTE", "ht_bridge");
        std::env::remove_var("KM_NO_INPROC_HT");
        let source = "Ontology(Declaration(Class(<A>)) Declaration(Class(<B>)) \
                      SubClassOf(<A> <B>))";
        let clauses = TempPath::new(".clauses.json");
        let (meta, cached, sidecar) =
            run_ofn_in_process(source, clauses.path()).expect("frontend parses");
        assert_eq!(meta.route, "ht_bridge");
        assert!(cached.is_some(), "bridge must cross the typed handoff");
        assert!(sidecar.is_none());
        assert!(!clauses.path().exists());
    }

    #[test]
    fn giant_rbox_scan_detects_tokens_across_chunk_boundaries() {
        let path = TempPath::new(".ofn");
        let token = b"TransitiveObjectProperty(";
        let mut input = vec![b'x'; (64 << 10) - token.len() / 2];
        input.extend_from_slice(token);
        input.extend_from_slice(b"<r>)");
        std::fs::write(path.path(), input).unwrap();
        assert!(giant_source_uses_certified_rbox(path.path()).unwrap());
    }

    #[test]
    fn giant_rbox_scan_accepts_plain_el_source() {
        let path = TempPath::new(".ofn");
        std::fs::write(
            path.path(),
            b"Ontology(SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>)))",
        )
        .unwrap();
        assert!(!giant_source_uses_certified_rbox(path.path()).unwrap());
    }

    #[test]
    fn giant_rbox_scan_checks_tail_then_full_source() {
        let tail_path = TempPath::new(".ofn");
        let mut tail_input = vec![b'x'; (1 << 20) + 4096];
        tail_input.extend_from_slice(b"InverseObjectProperties(<r> <s>)");
        std::fs::write(tail_path.path(), tail_input).unwrap();
        assert!(giant_source_uses_certified_rbox(tail_path.path()).unwrap());

        let prefix_path = TempPath::new(".ofn");
        let mut prefix_input = b"SymmetricObjectProperty(<r>)".to_vec();
        prefix_input.resize((1 << 20) + 4096, b'x');
        std::fs::write(prefix_path.path(), prefix_input).unwrap();
        assert!(giant_source_uses_certified_rbox(prefix_path.path()).unwrap());
    }
}
