//! Typed configuration, parsed ONCE from the environment (the Rust-spirit
//! replacement for `owl_classify.py`'s scattered, mutated `os.environ` reads).
//!
//! Worker binaries are resolved relative to the running `km` executable
//! (`current_exe().parent()/<name>`) unless overridden by the same `KM_*_BIN`
//! env vars the benchmark harness already sets. Per-spawn settings that Python
//! injected by mutating the global environment (`KM_QUERIES`, `KM_THREADS`,
//! `KM_NO_CENTRAL`) are passed explicitly through the engine runner instead.

use std::path::PathBuf;

pub struct Config {
    /// path of the running multi-call binary (for sibling-worker resolution)
    pub self_exe: PathBuf,
    pub ofn_bin_override: Option<PathBuf>,
    pub elc_bin_override: Option<PathBuf>,
    pub engine_bin_override: Option<PathBuf>,
    pub tab_bin_override: Option<PathBuf>,
    // --- absorption portfolio (KM_ABSORB_PORTFOLIO) ---
    pub absorb_portfolio: bool,
    /// KM_ABSORB present and != "0"
    pub absorb_on: bool,
    pub absorb_probe_s: f64,
    // --- tableau race (KM_TAB_RACE) ---
    pub tab_race: bool,
    pub tab_feat: bool,
    pub tab_max_clauses: usize,
    pub tab_race_delay: f64,
    pub tab_race_nice: bool,
    pub tab_ord: String,
    /// KM_THREADS (the ambient value is inherited by children automatically; we
    /// only need it to know whether the single-threaded retry differs from it).
    pub threads: Option<usize>,
    /// KM_PAR_MEM_GB RSS cap for the parallel attempt (default 18.0)
    pub par_mem_gb: f64,
    /// KM_CENTRAL_TIME_CAP wall cap for the central strategy (default 190.0)
    pub central_time_cap: f64,
    /// KM_NO_RETRY: disable the single-threaded adaptive retry
    pub no_retry: bool,
    /// KM_NO_CENTRAL: start from the legacy per-`f` strategy
    pub no_central: bool,
    // --- certified-elc portfolio (KM_ELC_PORTFOLIO) ---
    pub elc_portfolio: bool,
    /// KM_ELC_FORCE: attempt elc on a non-EL-safe RBox (certificate gate)
    pub elc_force: bool,
    /// KM_ELC_FORCE_BUDGET_S wall budget for the forced attempt (default 100)
    pub elc_force_budget_s: f64,
    /// KM_ELC_FORCE_MEM_GB RSS cap for the forced attempt
    /// (default KM_PAR_MEM_GB raw, else 14 — NOT the 18 par_mem_gb default)
    pub elc_force_mem_gb: f64,
    /// KM_ELC_PORT_MEM_GB RSS cap for the certified-elc racer (default 8)
    pub elc_port_mem_gb: f64,
    // --- HT race (KM_HT_RACE) ---
    pub ht_race: bool,
    /// KM_HT_MODE: "fallback" (monotone-safe, default) | "race" (speed)
    pub ht_mode: String,
    /// KM_HT_BUDGET_S: in fallback mode, HT answers only when CB runs past this
    pub ht_budget_s: f64,
    /// KM_HT_SHOQ_BUDGET_S: shorter fallback budget for the SHOQ route (the fast
    /// Ht is sound+complete on that fragment and decides in <1-3s, so there is no
    /// reason to wait the full ht_budget_s for the doomed CB). CB still wins when
    /// it finishes first (canaries 0.9s), so CB-preference is preserved.
    pub shoq_budget_s: f64,
    /// KM_HT_NICE: scheduling niceness for the HT racer ("0" disables nice)
    pub ht_nice: String,
    /// KM_HT_QO: use the QuasiOrderClassification driver (non-branching
    /// saturation + residual SAT tests) instead of per-concept branching in the
    /// HT racer. Default OFF (opt-in). The validation sweep (job 47644343,
    /// 2026-06-19, qo vs noqo over `km classify`) found it a strict regression:
    /// -2 onts (9024, 12141 lose 623 subsumptions each → incomplete), 0
    /// recoveries. The qo-tally diagnostic proved it gives no leverage on the
    /// disjunction family it targeted (5303 = 0/94 concepts sufficient;
    /// 10702/1603/12653/541 the global model does not even build in budget).
    /// Kept behind this flag for the record; see project_km_qo_deadend.
    pub ht_qo: bool,
    /// KM_HT_QO_ROUTER: route Horn-INVERSE ontologies to the validated QoSat
    /// hybrid certify path (INVCOMPOSE+FPROP+SAT+KPSET) as a RACE arm against CB.
    /// The hybrid is a sound certify-OR-DEFER specialist (KM_HT_QO_CERTIFY_ONLY):
    /// it emits an answer only when kpset certifies (sound+complete by
    /// construction), else defers so CB decides. The router gate is structural —
    /// only onts whose cb_to_ht TInput is faithful, nominal-free, and HAS inverse
    /// roles get the hybrid arm — so the INVCOMPOSE/sat_mode overhead never
    /// touches the CB-territory onts it would slow (corpus-validated: recovers
    /// 7581 in ~31s, 0 regressions). Default ON (opt out: KM_NO_HT_QO_ROUTER).
    pub qo_router: bool,
    /// KM_HT_SHOQ: route the SHOQ/SHOIN/SHON fragment (nominals present, no
    /// datatype) to the fast Ht (nominal o-rule + ≥n recognition + ≤n merge).
    /// Monotone-safe in fallback mode (CB preferred; the fast Ht answers only on
    /// CB timeout). Default ON (opt out: KM_NO_HT_SHOQ) — validated 0 unsound
    /// across the 587-corpus sweep (job 7399); recovers 10908 / 15672.
    pub ht_shoq: bool,
    /// KM_HT_CARD: route the SHQ number fragment (number restrictions, no inverse,
    /// no nominals, no datatype) to the fast Ht with the FIRST-CLASS Konclude
    /// `≥n`/`≤n` rules (cb_to_ht emits `card_defs` and drops the clausal `⋁ Eq`
    /// pigeonhole). The first-class rules FOLD the cardinality model the legacy
    /// Eq-merge cannot (12653 12365→201 nodes, 1603 17182→206, gold-exact).
    /// Monotone-safe in fallback mode (CB preferred; the fast Ht answers only on
    /// CB timeout). Default OFF (opt in: KM_HT_CARD) — the master switch also makes
    /// the frontend emit the cardinality metadata, so it gates the whole feature.
    pub ht_card: bool,
    /// KM_HT_RULES (Stage 2 of SWRL DL-safe rule support): when set AND the
    /// ontology has DL-safe rules, route it to the rule-aware HT consistency check
    /// (ABox seeded as named nominal nodes + rules fired over named individuals).
    /// Default OFF: with the flag unset the whole feature is inert and the output
    /// is byte-identical to the no-rules build.
    pub ht_rules: bool,
}

fn env_f64(key: &str, default: f64) -> f64 {
    std::env::var(key).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

impl Config {
    pub fn from_env() -> Config {
        let self_exe = std::env::current_exe().unwrap_or_else(|_| PathBuf::from("km"));
        Config {
            self_exe,
            ofn_bin_override: std::env::var_os("KM_OFN_BIN").map(PathBuf::from),
            elc_bin_override: std::env::var_os("KM_ELC_BIN").map(PathBuf::from),
            engine_bin_override: std::env::var_os("KM_ENGINE").map(PathBuf::from),
            tab_bin_override: std::env::var_os("KM_TAB_BIN").map(PathBuf::from),
            // Default ON: the sequential plain-then-absorbed CB portfolio. The
            // 2026-06-21 full-corpus ablation (results/benchmarks/2026-06-21-ablation)
            // found it the strictly dominant single lever: +4 ORE onts
            // (6212/10908/15491/16444) over the bare-default 565, with 0 unsound,
            // 0 incomplete, 0 regressions, and it captures every recovery any
            // single flag (or combination of flags) achieves. It is a sequential
            // probe (no memory doubling). Opt out with KM_NO_ABSORB_PORTFOLIO
            // (or KM_ABSORB=0 for just the absorbed clausification gate).
            absorb_portfolio: std::env::var_os("KM_NO_ABSORB_PORTFOLIO").is_none(),
            absorb_on: std::env::var("KM_ABSORB").map(|v| v != "0").unwrap_or(true),
            absorb_probe_s: env_f64("KM_ABSORB_PROBE_S", 8.0),
            tab_race: std::env::var_os("KM_TAB_RACE").is_some(),
            tab_feat: std::env::var_os("KM_TAB_FEAT").is_some(),
            tab_max_clauses: std::env::var("KM_TAB_MAX_CLAUSES").ok().and_then(|v| v.parse().ok()).unwrap_or(20000),
            tab_race_delay: env_f64("KM_TAB_RACE_DELAY", 30.0),
            tab_race_nice: std::env::var("KM_TAB_RACE_NICE").map(|v| v != "0").unwrap_or(true),
            tab_ord: std::env::var("KM_TAB_ORD").unwrap_or_else(|_| "0".to_string()),
            threads: std::env::var("KM_THREADS").ok().and_then(|v| v.parse().ok()),
            par_mem_gb: env_f64("KM_PAR_MEM_GB", 18.0),
            central_time_cap: env_f64("KM_CENTRAL_TIME_CAP", 190.0),
            no_retry: std::env::var_os("KM_NO_RETRY").is_some(),
            no_central: std::env::var_os("KM_NO_CENTRAL").is_some(),
            // Default ON (the validated router): the certified-elc portfolio is
            // sound+complete and, with the giant-exclusion guard in classify(),
            // never regresses. Opt out with KM_NO_ELC_PORTFOLIO.
            elc_portfolio: std::env::var_os("KM_NO_ELC_PORTFOLIO").is_none(),
            elc_force: std::env::var_os("KM_ELC_FORCE").is_some(),
            elc_force_budget_s: env_f64("KM_ELC_FORCE_BUDGET_S", 100.0),
            // Python: float(KM_ELC_FORCE_MEM_GB or KM_PAR_MEM_GB or "14") — the
            // raw KM_PAR_MEM_GB env, falling back to 14 (NOT the 18 par_mem_gb).
            elc_force_mem_gb: env_f64("KM_ELC_FORCE_MEM_GB", env_f64("KM_PAR_MEM_GB", 14.0)),
            elc_port_mem_gb: env_f64("KM_ELC_PORT_MEM_GB", 8.0),
            // Default ON: in fallback mode (the default ht_mode) HT answers only
            // on CB/elc failure, so it is monotone-safe. Opt out with KM_NO_HT_RACE.
            ht_race: std::env::var_os("KM_NO_HT_RACE").is_none(),
            ht_mode: std::env::var("KM_HT_MODE").unwrap_or_else(|_| "fallback".to_string()),
            ht_budget_s: env_f64("KM_HT_BUDGET_S", 225.0),
            shoq_budget_s: env_f64("KM_HT_SHOQ_BUDGET_S", 20.0),
            ht_nice: std::env::var("KM_HT_NICE").unwrap_or_else(|_| "1".to_string()),
            ht_qo: std::env::var_os("KM_HT_QO").is_some(),
            // Promoted default-ON (2026-06-25): the QO router recovers 7581/16444
            // soundly (fallback mode, CB preferred), and the SHOQ route recovers
            // 10908/15672 with 0 unsound across the 587-corpus sweep (job 7399).
            // They target disjoint fragments (qo_candidate requires no nominals;
            // shoq_candidate requires nominals), so they compose cleanly. Opt out
            // with KM_NO_HT_QO_ROUTER / KM_NO_HT_SHOQ.
            qo_router: std::env::var_os("KM_NO_HT_QO_ROUTER").is_none(),
            ht_shoq: std::env::var_os("KM_NO_HT_SHOQ").is_none(),
            ht_card: std::env::var_os("KM_HT_CARD").is_some(),
            ht_rules: std::env::var_os("KM_HT_RULES").is_some(),
        }
    }

    /// A worker invocation as `(program, leading_args)`: the `KM_*_BIN` override
    /// as a standalone program (no leading args), else THIS binary re-invoked
    /// with the worker subcommand (the single-binary `km <sub>` model). Spawn
    /// sites build a `Command` from the program and prepend the leading args.
    fn worker_cmd(&self, ov: &Option<PathBuf>, sub: &str) -> (PathBuf, Vec<String>) {
        match ov {
            Some(p) => (p.clone(), Vec::new()),
            None => (self.self_exe.clone(), vec![sub.to_string()]),
        }
    }
    pub fn ofn_cmd(&self) -> (PathBuf, Vec<String>) {
        self.worker_cmd(&self.ofn_bin_override, "ofn")
    }
    pub fn elc_cmd(&self) -> (PathBuf, Vec<String>) {
        self.worker_cmd(&self.elc_bin_override, "elc")
    }
    pub fn engine_cmd(&self) -> (PathBuf, Vec<String>) {
        self.worker_cmd(&self.engine_bin_override, "engine")
    }
    /// Tableau worker. Unlike the others it is gated at the call site by
    /// `KM_TAB_RACE` / `KM_HT_RACE` (the spawn functions check those), so here it
    /// always resolves — the `KM_TAB_BIN` override, else `km tableau`.
    pub fn tab_cmd(&self) -> (PathBuf, Vec<String>) {
        self.worker_cmd(&self.tab_bin_override, "tableau")
    }
}
