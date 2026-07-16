// Temporary single-mechanism bootstrap. The completed IBEX matrix replaces
// this file via results/benchmarks/2026-07-15-routing/emit_rust_tree.py.
use super::Route;
use crate::frontend::profile::OntologyProfile;

pub(super) fn select(_profile: &OntologyProfile) -> Route {
    Route::CbPlain16
}
