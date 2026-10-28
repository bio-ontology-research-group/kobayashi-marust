import sys, re
root = sys.argv[1]
def edit(path, pairs):
    p = root + "/" + path; s = open(p).read()
    for old, new in pairs:
        assert s.count(old) == 1, (path, old[:60], s.count(old))
        s = s.replace(old, new, 1)
    open(p, "w").write(s)

edit("src/frontend/mod.rs", [
('''    drop(ontology); // the syntax AST is dead once clausified''',
 '''    let converted_data_assertions = ontology.data_assertions_as_class();
    drop(ontology); // the syntax AST is dead once clausified'''),
('''        nominal_abox
            .unsupported
            .retain(|reason| reason != &diagnostic);
        nominal_abox.complete = nominal_abox.unsupported.is_empty();
    }
''',
 '''        nominal_abox
            .unsupported
            .retain(|reason| reason != &diagnostic);
        nominal_abox.complete = nominal_abox.unsupported.is_empty();
    }
    // Data-property assertions the clause set does not carry: the source
    // count of positive and negative assertions less the positive ones
    // converted to `DataHasValue` class assertions, unless the drop was
    // certified harmless just above (the diagnostic is then gone). The
    // orchestrator re-runs the frontend with the conversion when this is
    // positive and publishes any remainder as dropped axioms, so a clause
    // worker never publishes a complete-looking taxonomy over a silently
    // dropped assertion.
    let uncarried_data_assertions = if nominal_abox
        .unsupported
        .iter()
        .any(|reason| reason.ends_with(DATA_ASSERTIONS_UNSUPPORTED_SUFFIX))
    {
        let source_count = |kind: &str| profile.source.axiom_types.get(kind).copied().unwrap_or(0);
        (source_count("DataPropertyAssertion") + source_count("NegativeDataPropertyAssertion"))
            .saturating_sub(converted_data_assertions)
    } else {
        0
    };
'''),
('''        profile,
        route: route.as_str().to_string(),
    })
}
''',
 '''        profile,
        route: route.as_str().to_string(),
        uncarried_data_assertions,
    })
}
'''),
('''    pub nominal_abox: crate::json_io::NominalAboxMeta,
    /// KM_HT_CARD: first-class qualified number restrictions''',
 '''    pub nominal_abox: crate::json_io::NominalAboxMeta,
    /// Positive and negative `DataPropertyAssertion` axioms the clause set does
    /// not carry and whose omission is not certified harmless. The orchestrator
    /// re-runs the frontend with `KM_DATA_ASSERTION_AS_CLASS` when this is
    /// positive and publishes the remainder as dropped axioms.
    pub uncarried_data_assertions: u64,
    /// KM_HT_CARD: first-class qualified number restrictions'''),
('''        unsupported.insert(format!(
            "{source_data_role} data-property assertion axiom(s) are unsupported"
        ));''',
 '''        unsupported.insert(format!("{source_data_role}{DATA_ASSERTIONS_UNSUPPORTED_SUFFIX}"));'''),
])
# constant near top of frontend/mod.rs: after the FrontendResult struct doc? put before `pub struct FrontendResult`
edit("src/frontend/mod.rs", [
('''pub struct FrontendResult {''',
 '''/// Coverage diagnostic for data-property assertions the clause set does not
/// carry (`"<n> data-property assertion axiom(s) are unsupported"`).
pub const DATA_ASSERTIONS_UNSUPPORTED_SUFFIX: &str = " data-property assertion axiom(s) are unsupported";

pub struct FrontendResult {'''),
])
edit("src/cli.rs", [
('''    profile: crate::frontend::profile::OntologyProfile,
    route: String,
}
''',
 '''    profile: crate::frontend::profile::OntologyProfile,
    route: String,
    uncarried_data_assertions: u64,
}
'''),
('''            profile: result.profile,
            route: result.route,
        };''',
 '''            profile: result.profile,
            route: result.route,
            uncarried_data_assertions: result.uncarried_data_assertions,
        };'''),
])
edit("src/orchestrate/frontend_run.rs", [
('''    #[serde(default = "manual_route")]
    pub route: String,
}
''',
 '''    #[serde(default = "manual_route")]
    pub route: String,
    /// Data-property assertions the clause set does not carry (see
    /// `FrontendResult::uncarried_data_assertions`).
    #[serde(default)]
    pub uncarried_data_assertions: u64,
}
'''),
('''        profile: result.profile,
        route: result.route,
    };
    let mut out = crate::json_io::JInput {''',
 '''        profile: result.profile,
        route: result.route,
        uncarried_data_assertions: result.uncarried_data_assertions,
    };
    let mut out = crate::json_io::JInput {'''),
('''pub fn run_ofn_split_cached(
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
    // Trust holds only for the registered file itself, read unconverted.''',
 '''pub fn run_ofn_split_cached(
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
    let mut result = run_ofn_split_cached_once(cfg, ont)?;
    // OWL 2 Direct Semantics: `DataPropertyAssertion(p a v)` holds iff `a` is
    // an instance of `DataHasValue(p v)`. The frontend carries positive data
    // assertions as those class assertions only on request, so that inputs
    // whose assertions are certified irrelevant keep their clause output.
    // When it reports assertions it did not carry, and the drop is not
    // certified harmless, re-run it with the conversion for this whole
    // classification (the key is restored by the caller's environment guard).
    // Whatever stays uncarried after that (negative assertions, a literal
    // vocabulary above the cap) is published as dropped axioms.
    if result.1.uncarried_data_assertions > 0 && !data_assertions_as_class_requested() {
        if std::env::var_os("KM_TIMING").is_some() {
            eprintln!(
                "KM_TIMING frontend: {} data-property assertion(s) not carried; \\
                 re-running with the DataHasValue conversion",
                result.1.uncarried_data_assertions
            );
        }
        std::env::set_var("KM_DATA_ASSERTION_AS_CLASS", "1");
        result = run_ofn_split_cached_once(cfg, ont)?;
        if std::env::var_os("KM_TIMING").is_some() && result.1.uncarried_data_assertions > 0 {
            eprintln!(
                "KM_TIMING frontend: {} data-property assertion(s) stay uncarried after the conversion",
                result.1.uncarried_data_assertions
            );
        }
    }
    super::UNCARRIED_DATA_ASSERTIONS.store(result.1.uncarried_data_assertions, std::sync::atomic::Ordering::SeqCst);
    Ok(result)
}

fn data_assertions_as_class_requested() -> bool {
    std::env::var_os("KM_DATA_ASSERTION_AS_CLASS").is_some_and(|value| value != "0")
}

fn run_ofn_split_cached_once(
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
    // Trust holds only for the registered file itself, read unconverted.'''),
])
edit("src/orchestrate/mod.rs", [
('''pub(crate) fn classify_with_evidence(
    initial_cfg: &Config,
    ont: &Path,
) -> Result<ClassificationEvidence, OrchestrateError> {
    classify_with_evidence_mode(initial_cfg, ont, false)
}

fn classify_with_evidence_mode(
    initial_cfg: &Config,
    ont: &Path,
    retain_grouped_output: bool,
) -> Result<ClassificationEvidence, OrchestrateError> {
''',
 '''pub(crate) fn classify_with_evidence(
    initial_cfg: &Config,
    ont: &Path,
) -> Result<ClassificationEvidence, OrchestrateError> {
    classify_with_evidence_mode(initial_cfg, ont, false)
}

/// Data-property assertions the last frontend run of this classification did
/// not carry (`frontend_run::run_ofn_split_cached`). Published as dropped
/// axioms by the outermost classification call.
pub(crate) static UNCARRIED_DATA_ASSERTIONS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Nesting depth of `classify_with_evidence_mode` (fallback and probe routes
/// recurse into it); only the outermost call publishes.
static CLASSIFY_DEPTH: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn classify_with_evidence_mode(
    initial_cfg: &Config,
    ont: &Path,
    retain_grouped_output: bool,
) -> Result<ClassificationEvidence, OrchestrateError> {
    use std::sync::atomic::Ordering;
    let depth = CLASSIFY_DEPTH.fetch_add(1, Ordering::SeqCst);
    if depth == 0 {
        UNCARRIED_DATA_ASSERTIONS.store(0, Ordering::SeqCst);
    }
    let mut result = classify_with_evidence_inner(initial_cfg, ont, retain_grouped_output);
    CLASSIFY_DEPTH.fetch_sub(1, Ordering::SeqCst);
    if depth == 0 {
        // A data-property assertion the clause set does not carry is an
        // omitted axiom of the published answer: count it with the worker's
        // dropped clauses so the taxonomy is never published as complete.
        let uncarried = UNCARRIED_DATA_ASSERTIONS.swap(0, Ordering::SeqCst);
        if let Ok(evidence) = &mut result {
            evidence.classification.dropped += uncarried as usize;
        }
    }
    result
}

fn classify_with_evidence_inner(
    initial_cfg: &Config,
    ont: &Path,
    retain_grouped_output: bool,
) -> Result<ClassificationEvidence, OrchestrateError> {
'''),
])
print("patched")
