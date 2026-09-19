//! Isolated environment regression for resource policy across route normalization.
use kobayashi_marust::{orchestrate::Config, routing::Route};

#[test]
fn worker_budget_survives_named_routes_and_fallback_normalization() {
    for route in [Route::ProductionAll, Route::Nominals, Route::HtBridge] {
        std::env::remove_var("KM_RESOURCE_WORKER_MEM_GB");
        route.apply_environment();
        let baseline = Config::from_env();
        assert_eq!(baseline.par_mem_gb, 18.0);
        assert_eq!(baseline.ht_mem_gb, 18.0);
        std::env::set_var("KM_RESOURCE_WORKER_MEM_GB", "64");
        // The same normalization runs again when an automatic route defers.
        route.apply_environment();
        let expanded = Config::from_env();
        assert_eq!(expanded.par_mem_gb, 64.0);
        assert_eq!(expanded.ht_mem_gb, 64.0);
        assert_eq!(expanded.mechanism, baseline.mechanism);
        assert_eq!(expanded.threads, baseline.threads);
        for invalid in ["NaN", "inf", "-1", "0", "invalid"] {
            std::env::set_var("KM_RESOURCE_WORKER_MEM_GB", invalid);
            let config = Config::from_env();
            assert_eq!(config.par_mem_gb, 18.0);
            assert_eq!(config.ht_mem_gb, 18.0);
        }
    }
    std::env::remove_var("KM_RESOURCE_WORKER_MEM_GB");
}
