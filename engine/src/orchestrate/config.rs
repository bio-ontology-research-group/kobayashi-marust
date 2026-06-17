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
}
