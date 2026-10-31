//! `KM_LEAN_CHECKERS=<dir>`: run the applicable Lean checkers from one
//! directory and fail closed on a rejection.
//!
//! The variable names a directory of built checker executables (for example
//! `lean/.lake/build/bin`). `km classify` then:
//!
//! 1. creates a private run directory and exports `KM_LEAN_CHECK_DIR` (where
//!    workers write certificates) and `KM_LEAN_CHECK_LOG` (one JSON line per
//!    checker event) to itself and to every worker it spawns;
//! 2. lets each worker turn on the checkers of its own procedure
//!    ([`configure_elc`], [`configure_cb`], [`configure_ht`]); a variable the
//!    caller already set is never overridden;
//! 3. after classification, prints one `KM_LEAN_CHECK` line per event on
//!    stderr and publishes nothing if any checker rejected a certificate
//!    ([`finish_classify`]).
//!
//! The rule is the maintainer's "exact answers, no silent approximation":
//! an accepted certificate proves the worker's answer exact for the clause set
//! inside the certificate; a run whose certificate cannot be produced or is
//! too large publishes the same answer it publishes without the checkers and
//! says so (`cannot_check`); a rejected certificate is a defect in the worker
//! or in its certificate, so the run publishes no answer. Turning a checker on
//! never changes an answer: every worker computes the answer it computes
//! without the checker, and the checker only decides whether it is published.
//!
//! What acceptance proves is listed per checker in `docs/CHECKERS-ON.md`.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// The checker directory chosen by the caller.
pub const DIR_ENV: &str = "KM_LEAN_CHECKERS";
/// Run directory for certificates (set by `km classify`).
pub const RUN_DIR_ENV: &str = "KM_LEAN_CHECK_DIR";
/// JSON-lines event log (set by `km classify`).
pub const LOG_ENV: &str = "KM_LEAN_CHECK_LOG";
/// Optional size cap in bytes; a larger certificate is `cannot_check`.
pub const MAX_BYTES_ENV: &str = "KM_LEAN_CHECK_MAX_BYTES";
/// Producer-side budget of the ELC certificate in derived facts (subsumptions
/// plus edges). Above it the ELC worker writes no certificate, records
/// `cannot_check` and publishes its unchecked answer. `0` disables the budget.
pub const MAX_ELC_FACTS_ENV: &str = "KM_LEAN_CHECK_MAX_ELC_FACTS";
/// Default ELC budget: `elc-cert-check` needs about 25 s on the 530,000-fact
/// certificate of ore_ont_10254, so this keeps a checked ELC run under a
/// minute.
pub const DEFAULT_MAX_ELC_FACTS: u64 = 1_000_000;
/// `all` also turns on the component checkers (CB closure and terminal-state
/// wires); the default `publication` set turns on only checkers whose theorem
/// concludes that the published answer is exact.
pub const SET_ENV: &str = "KM_LEAN_CHECKERS_SET";
/// Opt-in for the hypertableau checkers (see `configure_ht`).
pub const HT_ENV: &str = "KM_LEAN_CHECKERS_HT";
/// Keep the run directory (certificates) after `km classify` returns.
pub const KEEP_ENV: &str = "KM_LEAN_CHECK_KEEP";

static REJECTED: AtomicBool = AtomicBool::new(false);
static NONCE: AtomicU64 = AtomicU64::new(0);

/// Exactly one ELC checker consumes the ELC publication certificate.
pub const ELC_CHECKERS: &[(&str, &str)] = &[("KM_ELC_LEAN_CERT_CHECKER", "elc-cert-check")];

/// CB checkers: (checker variable, executable, candidate variable, set).
/// The candidate variable names the file the worker writes for that checker.
pub const CB_CHECKERS: &[(&str, &str, Option<&str>, CheckerSet)] = &[
    (
        "KM_CB_SOURCE_EXACT_LEAN_CERT_CHECKER",
        "cb-source-taxonomy-cert-check",
        Some("KM_CB_SOURCE_EXACT_TAXONOMY_CANDIDATE"),
        CheckerSet::Publication,
    ),
    (
        "KM_CB_SOURCE_PRODUCTION_TAXONOMY_CHECKER",
        "cb-source-production-taxonomy-check",
        Some("KM_CB_SOURCE_PRODUCTION_TAXONOMY_CANDIDATE"),
        CheckerSet::Publication,
    ),
    (
        "KM_CB_LEAN_CERT_CHECKER",
        "cb-live-taxonomy-publication-check",
        None,
        CheckerSet::GlobalModel,
    ),
    (
        "KM_CB_EXACT_LEAN_CERT_CHECKER",
        "cb-live-exact-taxonomy-publication-check",
        Some("KM_CB_EXACT_TAXONOMY_CANDIDATE"),
        CheckerSet::GlobalModel,
    ),
    (
        "KM_CB_TERMINAL_STATE_CHECKER",
        "cb-terminal-state-check",
        Some("KM_CB_TERMINAL_STATE_CANDIDATE"),
        CheckerSet::GlobalModel,
    ),
    (
        "KM_CB_STANDALONE_CONTEXT_PROOF_CHECKER",
        "cb-standalone-context-proof-check",
        Some("KM_CB_STANDALONE_CONTEXT_PROOF_CANDIDATE"),
        CheckerSet::All,
    ),
    (
        "KM_CB_SOURCE_LIVE_DERIVATION_CHECKER",
        "cb-source-live-insertion-derivation-check",
        Some("KM_CB_SOURCE_LIVE_DERIVATION_CANDIDATE"),
        CheckerSet::All,
    ),
    (
        "KM_CB_SOURCE_LOCAL_CLOSURE_CHECKER",
        "cb-source-local-closure-check",
        Some("KM_CB_SOURCE_LOCAL_CLOSURE_CANDIDATE"),
        CheckerSet::All,
    ),
    (
        "KM_CB_SOURCE_HYPER_CLOSURE_CHECKER",
        "cb-source-hyper-closure-check",
        Some("KM_CB_SOURCE_HYPER_CLOSURE_CANDIDATE"),
        CheckerSet::All,
    ),
    (
        "KM_CB_SOURCE_JOIN3_CLOSURE_CHECKER",
        "cb-source-join3-closure-check",
        Some("KM_CB_SOURCE_JOIN3_CLOSURE_CANDIDATE"),
        CheckerSet::All,
    ),
    (
        "KM_CB_SOURCE_SUCC_CLOSURE_CHECKER",
        "cb-source-succ-closure-check",
        Some("KM_CB_SOURCE_SUCC_CLOSURE_CANDIDATE"),
        CheckerSet::All,
    ),
    (
        "KM_CB_SOURCE_EQ_CLOSURE_CHECKER",
        "cb-source-eq-closure-check",
        Some("KM_CB_SOURCE_EQ_CLOSURE_CANDIDATE"),
        CheckerSet::All,
    ),
    (
        "KM_CB_SOURCE_ORDINARY_PRED_CLOSURE_CHECKER",
        "cb-source-ordinary-pred-closure-check",
        Some("KM_CB_SOURCE_ORDINARY_PRED_CLOSURE_CANDIDATE"),
        CheckerSet::All,
    ),
    (
        "KM_CB_SOURCE_ROOT_PRED_CLOSURE_CHECKER",
        "cb-source-root-pred-closure-check",
        Some("KM_CB_SOURCE_ROOT_PRED_CLOSURE_CANDIDATE"),
        CheckerSet::All,
    ),
];

/// HT production checker variables and their executables. The mapping
/// follows `lean/run-ht-certification-gate.sh` (where a variable is exported
/// there) and `docs/CHECKERS-ON.md` otherwise.
pub const HT_CHECKERS: &[(&str, &str)] = &[
    ("KM_HT_LEAN_CERT_CHECKER", "ht-cert-check"),
    ("KM_HT_LEAN_TAXONOMY_CERT_CHECKER", "ht-taxonomy-cert-check"),
    ("KM_HT_LEAN_PROJECTION_CHECKER", "ht-projection-cert-check"),
    (
        "KM_HT_LEAN_NATIVE_ABOX_DECISION_CHECKER",
        "ht-native-abox-decision-cert-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER",
        "ht-native-abox-source-decision-cert-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER",
        "ht-native-abox-taxonomy-matrix-cert-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_MATRIX_CHECKER",
        "ht-native-abox-cardinality-taxonomy-cert-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER",
        "ht-native-abox-taxonomy-source-cert-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER",
        "ht-native-abox-cardinality-taxonomy-source-cert-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_JOINT_SOURCE_CLASSIFICATION_CHECKER",
        "ht-joint-native-abox-classification-cert-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_CHECKER",
        "ht-native-abox-taxonomy-cert-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_CHECKER",
        "ht-native-abox-cardinality-taxonomy-decision-check",
    ),
    ("KM_HT_LEAN_FRONTIER_CHECKER", "ht-address-refinement-check"),
    (
        "KM_HT_LEAN_CARDINALITY_FRONTIER_CHECKER",
        "ht-cardinality-frontier-check",
    ),
    (
        "KM_HT_LEAN_ROOTED_CARDINALITY_FRONTIER_CHECKER",
        "ht-rooted-cardinality-frontier-check",
    ),
    (
        "KM_HT_LEAN_DOUBLING_TRACE_CHECKER",
        "ht-doubling-trace-check",
    ),
    (
        "KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER",
        "ht-cardinality-doubling-trace-check",
    ),
    (
        "KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER",
        "ht-rooted-cardinality-doubling-trace-check",
    ),
    (
        "KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER",
        "ht-ordinary-production-run-check",
    ),
    (
        "KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER",
        "ht-ordinary-unsat-production-run-check",
    ),
    (
        "KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER",
        "ht-cardinality-production-run-check",
    ),
    (
        "KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER",
        "ht-rooted-cardinality-production-run-check",
    ),
    (
        "KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER",
        "ht-rooted-ordinary-production-run-check",
    ),
    (
        "KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER",
        "ht-rooted-ordinary-taxonomy-production-run-check",
    ),
    (
        "KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER",
        "ht-rooted-cardinality-taxonomy-production-run-check",
    ),
    (
        "KM_HT_LEAN_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER",
        "ht-cardinality-taxonomy-production-run-check",
    ),
    (
        "KM_HT_LEAN_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER",
        "ht-ordinary-taxonomy-production-run-check",
    ),
    (
        "KM_HT_LEAN_PRODUCTION_BLOCKING_CHECKER",
        "ht-production-blocking-check",
    ),
    (
        "KM_HT_LEAN_PRODUCTION_TRACE_CHECKER",
        "ht-production-trace-check",
    ),
    (
        "KM_HT_LEAN_FINITE_PRODUCTION_TERMINAL_CHECKER",
        "ht-finite-production-terminal-check",
    ),
    (
        "KM_HT_LEAN_REGULAR_PRODUCTION_TERMINAL_CHECKER",
        "ht-regular-production-terminal-check",
    ),
    (
        "KM_HT_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER",
        "ht-equality-production-blocking-check",
    ),
    (
        "KM_HT_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER",
        "ht-equality-production-trace-check",
    ),
    (
        "KM_HT_LEAN_EQUALITY_PRODUCTION_TERMINAL_CHECKER",
        "ht-equality-production-terminal-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER",
        "ht-native-abox-cardinality-taxonomy-run-matrix-check",
    ),
    (
        "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER",
        "ht-native-abox-taxonomy-run-matrix-check",
    ),
    (
        "KM_HT_LEAN_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER",
        "ht-cardinality-taxonomy-run-matrix-check",
    ),
    (
        "KM_HT_LEAN_ORDINARY_TAXONOMY_RUN_MATRIX_CHECKER",
        "ht-ordinary-taxonomy-run-matrix-check",
    ),
    (
        "KM_HT_LEAN_SOURCE_BOUND_ORDINARY_GLOBAL_CHECKER",
        "ht-source-bound-ordinary-global-check",
    ),
    (
        "KM_HT_LEAN_SOURCE_BOUND_CARDINALITY_GLOBAL_CHECKER",
        "ht-source-bound-cardinality-global-check",
    ),
    (
        "KM_HT_LEAN_SOURCE_BOUND_CARDINALITY_TAXONOMY_CHECKER",
        "ht-source-bound-cardinality-taxonomy-check",
    ),
    (
        "KM_HT_LEAN_CARDINALITY_COMMON_TAXONOMY_CHECKER",
        "ht-cardinality-common-taxonomy-check",
    ),
    (
        "KM_HT_LEAN_SOURCE_BOUND_ORDINARY_TAXONOMY_CHECKER",
        "ht-source-bound-ordinary-taxonomy-check",
    ),
    (
        "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_GLOBAL_CHECKER",
        "ht-source-bound-native-abox-global-check",
    ),
    (
        "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_CARDINALITY_GLOBAL_CHECKER",
        "ht-source-bound-native-abox-cardinality-global-check",
    ),
    (
        "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_TAXONOMY_CHECKER",
        "ht-source-bound-native-abox-taxonomy-check",
    ),
    (
        "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_CARDINALITY_TAXONOMY_CHECKER",
        "ht-source-bound-native-abox-cardinality-taxonomy-check",
    ),
    (
        "KM_HT_LEAN_EXECUTABLE_PUBLICATION_CHECKER",
        "ht-executable-publication-check",
    ),
];

/// Which checkers `KM_LEAN_CHECKERS` turns on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckerSet {
    /// Checkers whose theorem concludes the published answer is exact.
    Publication,
    /// Publication checkers plus component wires.
    All,
    /// Legacy wires that decode `production_bound.global_model` as a complete
    /// global-model certificate (`WireCBGlobalModelDocument`: global closure
    /// and blocked ground saturation): the live publication bundle, the live
    /// exact taxonomy that embeds it, and the terminal state (its Pred send
    /// coverage comes from that certificate). No production code builds that
    /// completeness object; production puts the typed source in that slot,
    /// which the source-bound wires check (`CBSourceLiveInsertionDerivation`).
    /// The switch never turns these on; under `all` it records `cannot_check`
    /// for each one present in the directory.
    GlobalModel,
}

/// The outcome of one checker invocation.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Accepted,
    Rejected(String),
    /// The checker did not run (for example: certificate above the cap).
    CannotCheck(String),
}

/// The checker directory, when `KM_LEAN_CHECKERS` names one.
pub fn dir() -> Option<PathBuf> {
    std::env::var_os(DIR_ENV)
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
}

/// True in a process that runs under `KM_LEAN_CHECKERS`.
pub fn active() -> bool {
    dir().is_some()
}

fn selected_set() -> CheckerSet {
    match std::env::var(SET_ENV).as_deref() {
        Ok("all") => CheckerSet::All,
        _ => CheckerSet::Publication,
    }
}

/// Under `KM_LEAN_CHECKERS_SET=all` a worker runs its remaining checkers
/// after a rejection so that every checker's verdict is recorded; the
/// rejection still fails the run closed (the worker refuses to publish and
/// `km classify` publishes nothing).
pub fn continue_after_rejection() -> bool {
    active() && selected_set() == CheckerSet::All
}

/// True once this process recorded a rejection.
pub fn rejected_in_process() -> bool {
    REJECTED.load(Ordering::SeqCst)
}

fn json_escape(text: &str) -> String {
    serde_json::to_string(text).unwrap_or_else(|_| "\"\"".to_string())
}

/// Append one event to the run log (no-op without `KM_LEAN_CHECK_LOG`).
pub fn record(family: &str, checker: &Path, certificate: &str, outcome: &Outcome, bytes: u64) {
    if matches!(outcome, Outcome::Rejected(_)) {
        REJECTED.store(true, Ordering::SeqCst);
    }
    let Some(log) = std::env::var_os(LOG_ENV) else {
        return;
    };
    let (status, detail) = match outcome {
        Outcome::Accepted => ("accepted", String::new()),
        Outcome::Rejected(detail) => ("rejected", detail.clone()),
        Outcome::CannotCheck(detail) => ("cannot_check", detail.clone()),
    };
    let checker_name = checker
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| checker.display().to_string());
    let line = format!(
        "{{\"pid\":{},\"family\":{},\"checker\":{},\"certificate\":{},\"status\":\"{}\",\"bytes\":{},\"detail\":{}}}\n",
        std::process::id(),
        json_escape(family),
        json_escape(&checker_name),
        json_escape(certificate),
        status,
        bytes,
        json_escape(&detail),
    );
    // One write call per line on an O_APPEND file: concurrent workers do not
    // interleave inside a line.
    if let Ok(mut file) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(log)
    {
        let _ = file.write_all(line.as_bytes());
    }
}

/// Record that a family produced no certificate for this run.
pub fn record_cannot_check(family: &str, certificate: &str, reason: &str) {
    record(
        family,
        Path::new("-"),
        certificate,
        &Outcome::CannotCheck(reason.to_string()),
        0,
    );
}

/// A fresh path inside the run directory (or the system temporary
/// directory outside `km classify`).
pub fn fresh_path(stem: &str) -> PathBuf {
    let base = std::env::var_os(RUN_DIR_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let nonce = NONCE.fetch_add(1, Ordering::Relaxed);
    base.join(format!("{stem}-{}-{nonce}.json", std::process::id()))
}

/// The ELC certificate budget under `KM_LEAN_CHECKERS` (`None` outside it,
/// or when the budget is disabled with `0`).
pub fn max_elc_facts() -> Option<u64> {
    if !active() {
        return None;
    }
    let budget = std::env::var(MAX_ELC_FACTS_ENV)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_MAX_ELC_FACTS);
    (budget > 0).then_some(budget)
}

fn max_bytes() -> Option<u64> {
    std::env::var(MAX_BYTES_ENV)
        .ok()
        .and_then(|value| value.parse().ok())
}

/// Run `checker` on `document`, log the outcome, and return it. Checker
/// stdout is discarded (worker stdout is a protocol); its stderr is captured
/// into the log line of a rejection.
pub fn run(family: &str, checker: &Path, certificate: &str, document: &Path) -> Outcome {
    let bytes = std::fs::metadata(document)
        .map(|meta| meta.len())
        .unwrap_or(0);
    if let Some(cap) = max_bytes() {
        if bytes > cap {
            let outcome = Outcome::CannotCheck(format!(
                "certificate has {bytes} bytes, above {MAX_BYTES_ENV}={cap}"
            ));
            record(family, checker, certificate, &outcome, bytes);
            return outcome;
        }
    }
    // Exit 0 accepts and exit 1 rejects (`lean/*Check.lean`); any other
    // status (usage or I/O error, a signal, a runtime abort such as a failed
    // thread creation) is no verdict. Such a run is retried once and then
    // reported as `cannot_check`, never as acceptance.
    let mut outcome = invoke(checker, document);
    // A checker killed at its time limit is not retried.
    if matches!(&outcome, Outcome::CannotCheck(detail) if !detail.contains("SIGKILL")) {
        std::thread::sleep(std::time::Duration::from_millis(500));
        outcome = invoke(checker, document);
    }
    record(family, checker, certificate, &outcome, bytes);
    outcome
}

fn invoke(checker: &Path, document: &Path) -> Outcome {
    match CheckerCommand::new(checker)
        .arg(document)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .output()
    {
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let first = stderr.lines().next().unwrap_or("").trim();
            let first: String = first.chars().take(400).collect();
            // The Lean runtime reports an allocation failure as
            // "INTERNAL PANIC: out of memory" with exit status 1, the code of
            // a rejection. It is no verdict on the document.
            let runtime_panic = stderr.contains("INTERNAL PANIC");
            match output.status.code() {
                Some(0) => Outcome::Accepted,
                Some(1) if runtime_panic => Outcome::CannotCheck(format!(
                    "checker gave no verdict: {} ({})",
                    first, output.status
                )),
                Some(1) => Outcome::Rejected(format!("{} ({})", first, output.status)),
                _ => Outcome::CannotCheck(format!(
                    "checker gave no verdict: {} ({})",
                    first, output.status
                )),
            }
        }
        Err(error) => Outcome::CannotCheck(format!("cannot execute checker: {error}")),
    }
}

// ---------------------------------------------------------------------------
// Process start-up of a Lean checker
// ---------------------------------------------------------------------------
//
// A Lean executable starts its runtime threads before any Lean code runs: the
// thread that runs `main` (stack `LEAN_STACK_SIZE_KB`, default 1 GiB in
// v4.30) and a second runtime thread with a fixed 1 GiB stack. Under strict
// commit accounting (`vm.overcommit_memory = 2`, the workstation `ws`) a
// thread stack is charged in full when the thread starts, so when other
// processes hold most of the commit limit the runtime throws
// `lean::exception: failed to create thread` and the checker aborts (SIGABRT,
// exit 134) without reading its input. The verdict never depends on that
// abort; only the start does.
//
// Every checker process KM starts goes through [`CheckerCommand`]: the `main`
// thread gets a 256 MiB stack unless the caller set `LEAN_STACK_SIZE_KB`
// (halving the commit charge), and the start-up failure, recognised by its
// signal and message, is retried with growing pauses (about 5 s in total).
// Every other exit, including any other abort, is returned unchanged, so a
// caller that requires success still fails closed.

/// Stack of the thread that runs a checker's `main`, in KiB.
const MAIN_STACK_KB: &str = "262144";

/// Pauses between retries of a checker whose runtime could not start a
/// thread (milliseconds).
const RETRY_PAUSES_MS: [u64; 9] = [10, 20, 40, 80, 160, 320, 640, 1280, 2560];

fn startup_thread_failure(output: &std::process::Output) -> bool {
    use std::os::unix::process::ExitStatusExt;
    output.status.signal() == Some(6)
        && String::from_utf8_lossy(&output.stderr).contains("failed to create thread")
}

/// A `std::process::Command` for a Lean checker with the start-up handling
/// described above. It mirrors the `Command` methods the call sites use, so
/// a call site differs from a plain `Command` only in its constructor.
/// `stderr` is always captured (the start-up failure is recognised from it);
/// [`CheckerCommand::status`] forwards it to this process's stderr unless the
/// caller redirected it.
pub struct CheckerCommand {
    command: std::process::Command,
    stdout_set: bool,
    stderr_set: bool,
}

impl CheckerCommand {
    pub fn new<S: AsRef<std::ffi::OsStr>>(checker: S) -> Self {
        let mut command = std::process::Command::new(checker);
        if std::env::var_os("LEAN_STACK_SIZE_KB").is_none() {
            command.env("LEAN_STACK_SIZE_KB", MAIN_STACK_KB);
        }
        Self {
            command,
            stdout_set: false,
            stderr_set: false,
        }
    }

    pub fn arg<S: AsRef<std::ffi::OsStr>>(&mut self, arg: S) -> &mut Self {
        self.command.arg(arg);
        self
    }

    pub fn args<I, S>(&mut self, args: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<std::ffi::OsStr>,
    {
        self.command.args(args);
        self
    }

    pub fn env<K: AsRef<std::ffi::OsStr>, V: AsRef<std::ffi::OsStr>>(
        &mut self,
        key: K,
        value: V,
    ) -> &mut Self {
        self.command.env(key, value);
        self
    }

    pub fn stdin<T: Into<std::process::Stdio>>(&mut self, config: T) -> &mut Self {
        self.command.stdin(config);
        self
    }

    pub fn stdout<T: Into<std::process::Stdio>>(&mut self, config: T) -> &mut Self {
        self.command.stdout(config);
        self.stdout_set = true;
        self
    }

    /// Recorded only: stderr is always captured. A caller that redirects it
    /// does not get it forwarded by [`CheckerCommand::status`].
    pub fn stderr<T: Into<std::process::Stdio>>(&mut self, _config: T) -> &mut Self {
        self.stderr_set = true;
        self
    }

    /// Run to completion and collect the output (stdout is captured unless
    /// the caller configured it), retrying a start-up thread failure.
    pub fn output(&mut self) -> std::io::Result<std::process::Output> {
        self.command.stderr(std::process::Stdio::piped());
        if !self.stdout_set {
            self.command.stdout(std::process::Stdio::piped());
        }
        // The checker dies with the thread that started it, so a worker that
        // is killed (for example by a caller's time limit) leaves no orphan.
        unsafe {
            use std::os::unix::process::CommandExt;
            self.command.pre_exec(|| {
                if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let mut attempt = 0;
        loop {
            let output = run_with_deadline(&mut self.command, checker_time_limit())?;
            if !startup_thread_failure(&output) || attempt == RETRY_PAUSES_MS.len() {
                return Ok(output);
            }
            std::thread::sleep(std::time::Duration::from_millis(RETRY_PAUSES_MS[attempt]));
            attempt += 1;
        }
    }

    /// Run to completion and return the exit status (stdout inherited unless
    /// the caller configured it), retrying a start-up thread failure.
    pub fn status(&mut self) -> std::io::Result<std::process::ExitStatus> {
        if !self.stdout_set {
            self.command.stdout(std::process::Stdio::inherit());
        }
        let output = self.output()?;
        if !self.stderr_set && !output.stderr.is_empty() {
            use std::io::Write;
            let _ = std::io::stderr().write_all(&output.stderr);
        }
        Ok(output.status)
    }
}

/// Wall-clock limit of one checker process (`KM_LEAN_CHECK_TIMEOUT_SECS`,
/// default 900 s, `0` for none). A checker that exceeds it is killed; its
/// status is then a signal, which every caller treats as no verdict.
pub const TIMEOUT_ENV: &str = "KM_LEAN_CHECK_TIMEOUT_SECS";
const DEFAULT_TIMEOUT_SECS: u64 = 900;

fn checker_time_limit() -> Option<std::time::Duration> {
    let secs = std::env::var(TIMEOUT_ENV)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_TIMEOUT_SECS);
    (secs > 0).then(|| std::time::Duration::from_secs(secs))
}

/// `Command::output` with an optional deadline after which the child is
/// killed.
fn run_with_deadline(
    command: &mut std::process::Command,
    limit: Option<std::time::Duration>,
) -> std::io::Result<std::process::Output> {
    use std::io::Read;
    let mut child = command.spawn()?;
    let read_all = |pipe: Option<Box<dyn Read + Send>>| {
        std::thread::spawn(move || {
            let mut buffer = Vec::new();
            if let Some(mut pipe) = pipe {
                let _ = pipe.read_to_end(&mut buffer);
            }
            buffer
        })
    };
    let stdout = read_all(child.stdout.take().map(|p| Box::new(p) as Box<dyn Read + Send>));
    let stderr = read_all(child.stderr.take().map(|p| Box::new(p) as Box<dyn Read + Send>));
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait()? {
            break status;
        }
        if limit.is_some_and(|limit| start.elapsed() >= limit) {
            let _ = child.kill();
            break child.wait()?;
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    };
    Ok(std::process::Output {
        status,
        stdout: stdout.join().unwrap_or_default(),
        stderr: stderr.join().unwrap_or_default(),
    })
}

/// Run `checker DOCUMENT` and collect its output.
pub fn run_document(checker: &Path, document: &Path) -> std::io::Result<std::process::Output> {
    CheckerCommand::new(checker).arg(document).output()
}

/// Executable path for `name` when it exists in the checker directory.
fn executable(dir: &Path, name: &str) -> Option<PathBuf> {
    let path = dir.join(name);
    path.is_file().then_some(path)
}

/// Turn on the ELC checker. Safe to call in `km classify` itself, because
/// the ELC worker also runs in-process there.
pub fn configure_elc() {
    let Some(dir) = dir() else { return };
    for (variable, name) in ELC_CHECKERS {
        if std::env::var_os(variable).is_none() {
            if let Some(path) = executable(&dir, name) {
                std::env::set_var(variable, path);
            }
        }
    }
}

/// Why the switch does not run the `CheckerSet::GlobalModel` wires.
pub const GLOBAL_MODEL_DECLINE: &str = "the legacy live CB wire needs a global-model certificate \
     (global closure and blocked saturation), which production does not build; the \
     source-bound CB checkers cover this run";

/// Turn on the CB checkers for this worker process. Returns false (and
/// records `cannot_check`) when the CB evidence form does not apply; the
/// worker then runs exactly as without the checkers.
///
/// Certified CB mode (`KM_CB_LEAN_REQUIRED`) keeps every query root and runs
/// single-threaded; both are schedule changes of the same saturation and do
/// not change the derived set (see `docs/CB-CERTIFICATION.md`).
pub fn configure_cb(typed_source_ok: Result<(), String>) -> bool {
    let Some(dir) = dir() else { return false };
    if std::env::var_os("KM_CB_LEAN_REQUIRED").is_some() {
        // The caller configured certified CB by hand; leave it alone.
        return true;
    }
    if std::env::var_os("KM_NOMINALS").is_some() {
        // Certified CB keeps the plain unordered regime (state 0), which is
        // known to miss cross-individual entailments in nominal mode
        // (docs/PER-CONTEXT-ORDERING.md section 4). Certifying here would
        // change the computed answer, so the run stays uncertified.
        record_cannot_check(
            "cb",
            "cb-publication",
            "nominal mode: certified CB would use the unordered regime, which is incomplete with nominals",
        );
        return false;
    }
    if let Err(reason) = typed_source_ok {
        record_cannot_check(
            "cb",
            "cb-typed-source",
            &format!("typed source declined: {reason}"),
        );
        return false;
    }
    let set = selected_set();
    let mut any = false;
    for (variable, name, candidate, member) in CB_CHECKERS {
        if *member == CheckerSet::GlobalModel {
            if set == CheckerSet::All
                && std::env::var_os(variable).is_none()
                && executable(&dir, name).is_some()
            {
                record_cannot_check("cb", name, GLOBAL_MODEL_DECLINE);
            }
            continue;
        }
        if *member == CheckerSet::All && set != CheckerSet::All {
            continue;
        }
        if std::env::var_os(variable).is_some() {
            any = true;
            continue;
        }
        let Some(path) = executable(&dir, name) else {
            continue;
        };
        std::env::set_var(variable, path);
        if let Some(candidate) = candidate {
            if std::env::var_os(candidate).is_none() {
                std::env::set_var(candidate, fresh_path(&candidate.to_ascii_lowercase()));
            }
        }
        any = true;
    }
    if !any {
        record_cannot_check(
            "cb",
            "cb-publication",
            "no CB publication checker in the directory",
        );
        return false;
    }
    if std::env::var_os("KM_CB_CERT_BUNDLE").is_none() {
        std::env::set_var("KM_CB_CERT_BUNDLE", fresh_path("km_cb_cert_bundle"));
    }
    std::env::set_var("KM_CB_LEAN_REQUIRED", "1");
    true
}

/// Turn on the HT checkers for a hypertableau worker, only with
/// `KM_LEAN_CHECKERS_HT=1`. Certified HT is a different publication mode
/// (global decision plus checked taxonomy runs); on the automatic route most
/// HT workers then decline and the supervisor's exact fallback answers, so
/// the default leaves HT unchecked and the run reports `cannot_check`.
pub fn configure_ht() -> bool {
    let Some(dir) = dir() else { return false };
    if std::env::var_os("KM_HT").is_none() || std::env::var_os("KM_RULES_CONSISTENCY").is_some() {
        return false;
    }
    if std::env::var_os(HT_ENV).is_none() {
        record_cannot_check(
            "ht",
            "ht-publication",
            "HT checkers not enabled (set KM_LEAN_CHECKERS_HT=1); the HT answer is unchecked",
        );
        return false;
    }
    for (variable, name) in HT_CHECKERS {
        if std::env::var_os(variable).is_none() {
            if let Some(path) = executable(&dir, name) {
                std::env::set_var(variable, path);
            }
        }
    }
    true
}

/// One parsed log event.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct Event {
    pub pid: u32,
    pub family: String,
    pub checker: String,
    pub certificate: String,
    pub status: String,
    pub bytes: u64,
    pub detail: String,
}

/// The per-run state `km classify` keeps.
pub struct Run {
    run_dir: PathBuf,
    log: PathBuf,
    keep: bool,
}

/// Prepare the run directory and export the run variables. Returns `None`
/// without `KM_LEAN_CHECKERS`. Exits with status 2 when the directory is
/// unusable, before any work starts.
pub fn start_classify() -> Option<Run> {
    let dir = dir()?;
    if !dir.is_dir() {
        eprintln!(
            "KM_LEAN_CHECKERS={} is not a directory of Lean checkers",
            dir.display()
        );
        std::process::exit(2);
    }
    let base = std::env::temp_dir();
    let run_dir = base.join(format!(
        "km-lean-check-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    if let Err(error) = std::fs::create_dir_all(&run_dir) {
        eprintln!(
            "KM_LEAN_CHECKERS cannot create {}: {error}",
            run_dir.display()
        );
        std::process::exit(2);
    }
    let log = run_dir.join("events.jsonl");
    std::env::set_var(RUN_DIR_ENV, &run_dir);
    std::env::set_var(LOG_ENV, &log);
    configure_elc();
    // The in-process CB fast path publishes the same bytes as the forked CB
    // worker but has no certificate hook; route small inputs through the
    // worker so its checkers run.
    if std::env::var_os("KM_NO_INPROC_ENGINE").is_none() {
        std::env::set_var("KM_NO_INPROC_ENGINE", "1");
    }
    Some(Run {
        run_dir,
        log,
        keep: std::env::var_os(KEEP_ENV).is_some(),
    })
}

/// Read the events of this run.
pub fn events(log: &Path) -> Vec<Event> {
    let Ok(text) = std::fs::read_to_string(log) else {
        return Vec::new();
    };
    text.lines()
        .filter_map(|line| serde_json::from_str::<Event>(line).ok())
        .collect()
}

impl Run {
    /// Print one `KM_LEAN_CHECK` line per event and a summary on stderr.
    /// Returns `Err(message)` when any checker rejected a certificate; the
    /// caller must then publish nothing.
    pub fn finish(self) -> Result<(), String> {
        let events = events(&self.log);
        let mut accepted = 0usize;
        let mut rejected = Vec::new();
        let mut cannot = 0usize;
        for event in &events {
            match event.status.as_str() {
                "accepted" => accepted += 1,
                "rejected" => rejected.push(event.clone()),
                _ => cannot += 1,
            }
            eprintln!(
                "KM_LEAN_CHECK {} family={} checker={} certificate={} bytes={} worker_pid={}{}",
                event.status,
                event.family,
                event.checker,
                event.certificate,
                event.bytes,
                event.pid,
                if event.detail.is_empty() {
                    String::new()
                } else {
                    format!(" detail={}", json_escape(&event.detail))
                }
            );
        }
        eprintln!(
            "KM_LEAN_CHECK summary accepted={accepted} rejected={} cannot_check={cannot} events={}",
            rejected.len(),
            events.len()
        );
        if self.keep {
            eprintln!("KM_LEAN_CHECK kept {}", self.run_dir.display());
        } else {
            let _ = std::fs::remove_dir_all(&self.run_dir);
        }
        if let Some(first) = rejected.first() {
            return Err(format!(
                "KM_LEAN_CHECKERS fail closed: {} rejected the {} certificate ({}); no answer published",
                first.checker, first.certificate, first.detail
            ));
        }
        Ok(())
    }
}

/// Exit status of a `km classify` run that a checker rejected.
pub const REJECTED_EXIT: i32 = 6;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checker_tables_name_distinct_variables() {
        let mut names: Vec<&str> = ELC_CHECKERS.iter().map(|(v, _)| *v).collect();
        names.extend(CB_CHECKERS.iter().map(|(v, ..)| *v));
        names.extend(HT_CHECKERS.iter().map(|(v, _)| *v));
        let count = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), count);
    }

    #[test]
    fn only_the_legacy_live_wires_need_a_global_model_certificate() {
        let legacy: Vec<&str> = CB_CHECKERS
            .iter()
            .filter(|(.., member)| *member == CheckerSet::GlobalModel)
            .map(|(_, name, ..)| *name)
            .collect();
        assert_eq!(
            legacy,
            [
                "cb-live-taxonomy-publication-check",
                "cb-live-exact-taxonomy-publication-check",
                "cb-terminal-state-check",
            ]
        );
    }

    #[test]
    fn ht_table_covers_every_certification_variable() {
        for variable in crate::tableau::HT_LEAN_CERTIFICATION_ENV {
            if variable.ends_with("_OUT") {
                continue;
            }
            assert!(
                HT_CHECKERS.iter().any(|(name, _)| name == variable),
                "{variable} has no executable in HT_CHECKERS"
            );
        }
    }

    #[test]
    fn run_records_acceptance_rejection_and_no_verdict() {
        let dir =
            std::env::temp_dir().join(format!("km-lean-checkers-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let document = dir.join("doc.json");
        std::fs::write(&document, b"{}").unwrap();
        assert_eq!(
            run("test", Path::new("/bin/true"), "doc", &document),
            Outcome::Accepted
        );
        assert!(matches!(
            run("test", Path::new("/bin/false"), "doc", &document),
            Outcome::Rejected(_)
        ));
        assert!(rejected_in_process());
        assert!(matches!(
            run(
                "test",
                Path::new("/bin/sh"),
                "doc",
                Path::new("/nonexistent/document")
            ),
            Outcome::CannotCheck(_)
        ));
        std::fs::remove_dir_all(&dir).unwrap();
    }
}

#[cfg(test)]
mod checker_start_tests {
    use super::*;

    #[test]
    fn a_start_up_thread_failure_is_recognised_and_other_aborts_are_not() {
        use std::os::unix::process::ExitStatusExt;
        use std::process::Output;
        let abort = |stderr: &str| Output {
            status: std::process::ExitStatus::from_raw(6),
            stdout: Vec::new(),
            stderr: stderr.as_bytes().to_vec(),
        };
        assert!(startup_thread_failure(&abort(
            "libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread"
        )));
        assert!(!startup_thread_failure(&abort("Stack overflow detected. Aborting.")));
        let rejected = Output {
            status: std::process::ExitStatus::from_raw(1 << 8),
            stdout: Vec::new(),
            stderr: b"failed to create thread".to_vec(),
        };
        assert!(!startup_thread_failure(&rejected));
    }

    #[test]
    fn a_checker_over_its_time_limit_is_killed_and_gives_no_success() {
        let mut command = std::process::Command::new("/bin/sleep");
        command.arg("30").stdout(std::process::Stdio::null());
        let start = std::time::Instant::now();
        let output =
            run_with_deadline(&mut command, Some(std::time::Duration::from_millis(200))).unwrap();
        assert!(start.elapsed() < std::time::Duration::from_secs(10));
        assert!(!output.status.success());
        assert_eq!(output.status.code(), None, "killed by a signal");
    }

    #[test]
    fn a_checker_command_keeps_exit_codes_and_sets_the_main_stack() {
        let mut command = CheckerCommand::new("/bin/sh");
        let output = command
            .arg("-c")
            .arg("echo $LEAN_STACK_SIZE_KB; echo rejected >&2; exit 1")
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1));
        if std::env::var_os("LEAN_STACK_SIZE_KB").is_none() {
            assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), MAIN_STACK_KB);
        }
        assert_eq!(String::from_utf8_lossy(&output.stderr).trim(), "rejected");
        let status = CheckerCommand::new("/bin/sh")
            .args(["-c", "exit 0"])
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .unwrap();
        assert!(status.success());
    }
}
