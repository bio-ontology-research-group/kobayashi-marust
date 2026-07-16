// Temporary bootstrap until the completed IBEX matrix replaces this file via
// results/benchmarks/2026-07-15-routing/emit_rust_tree.py.
//
// Automatic routing selects the composed production bundle: the last
// corpus-validated default (2026-07-13 closure sweep, 574 ok / 508 exact
// Konclude matches, zero gold-match regressions). It is the only bundle that
// reaches the proven Konclude KPSet completion bridge — source-TBox trigger
// absorption at normalisation, the saturation pre-pass, the
// all-satisfiability-jobs barrier, the 30 s/0-retry probe budgets, and the
// large-synchronous-bridge thread reservation — while keeping the certified
// CB/EL fallback and CB-preference winner rule. The earlier CbPlain16
// placeholder silently normalized that stack OUT of the environment before
// the frontend ran, so the bridge-closed terminologies (541, 12653, 7914,
// 3215, 9663, 9724) regressed to plain-CB timeouts whenever KM_ROUTE was
// unset (the deployed harness default).
use super::Route;
use crate::frontend::profile::OntologyProfile;

pub(super) fn select(_profile: &OntologyProfile) -> Route {
    Route::ProductionAll
}
