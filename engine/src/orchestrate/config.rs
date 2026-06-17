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
            absorb_portfolio: std::env::var_os("KM_ABSORB_PORTFOLIO").is_some(),
            absorb_on: std::env::var("KM_ABSORB").map(|v| v != "0").unwrap_or(false),
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
        }
    }

    fn sibling(&self, name: &str) -> PathBuf {
        match self.self_exe.parent() {
            Some(dir) => dir.join(name),
            None => PathBuf::from(name),
        }
    }

    pub fn ofn_bin(&self) -> PathBuf {
        self.ofn_bin_override.clone().unwrap_or_else(|| self.sibling("ofn"))
    }
    pub fn elc_bin(&self) -> PathBuf {
        self.elc_bin_override.clone().unwrap_or_else(|| self.sibling("elc"))
    }
    pub fn engine_bin(&self) -> PathBuf {
        self.engine_bin_override
            .clone()
            .unwrap_or_else(|| self.sibling("kobayashi-marust"))
    }
    /// Tableau binary. Unlike the others, `_spawn_tableau` only races when
    /// `KM_TAB_BIN` is explicitly set and exists, so there is no sibling default.
    pub fn tab_bin(&self) -> Option<PathBuf> {
        self.tab_bin_override.clone().filter(|p| p.exists())
    }
}
