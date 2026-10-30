//! Memo of pure frontend stages across the classifier's two frontend passes.
//!
//! `orchestrate::frontend_run::run_ofn_split_cached` runs the frontend a
//! second time, with the `DataHasValue` conversion of data assertions, when
//! the first pass reports assertions it did not carry. On inputs whose
//! DL-safe rules compare data values (ore_ont_7278, ore_ont_3726) both passes
//! close the same positive ABox under the same rules
//! (`rule_assertions::materialize`), which is nearly all of a pass (the
//! finite-rule grounding before it takes about 0.2 s of 6.6 s on 7278).
//! Inside [`with_scope`] the second pass reads the first pass's closure
//! instead of recomputing it.
//!
//! The memo answers only an input equal to the one it stored, and the closure
//! is a function of that input alone (`rule_assertions::ClosureInput` states
//! why), so a pass inside the scope computes exactly what it computes outside
//! it. The memo lives on the calling thread and is dropped when the outermost
//! scope closes; nothing outside a scope is cached.

use std::cell::{Cell, RefCell};

use super::rule_assertions::{ClosureInput, ClosureOutput};

#[derive(Default)]
struct Memo {
    closure: Option<(ClosureInput, ClosureOutput)>,
    stats: Stats,
}

/// Counters of the open scope, for `KM_TIMING` and the tests.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Stats {
    pub closure_hits: usize,
}

thread_local! {
    static DEPTH: Cell<usize> = const { Cell::new(0) };
    static MEMO: RefCell<Option<Memo>> = const { RefCell::new(None) };
}

/// Run `f` with the memo open on this thread. A nested scope shares the
/// outer one; the memo is dropped when the outermost scope ends.
/// `KM_NO_FRONTEND_PASS_CACHE=1` runs `f` without the memo (A/B checks).
pub(crate) fn with_scope<T>(f: impl FnOnce() -> T) -> T {
    if std::env::var_os("KM_NO_FRONTEND_PASS_CACHE").is_some() {
        return f();
    }
    struct Scope;
    impl Drop for Scope {
        fn drop(&mut self) {
            let depth = DEPTH.with(|d| { d.set(d.get() - 1); d.get() });
            if depth == 0 {
                MEMO.with(|memo| *memo.borrow_mut() = None);
            }
        }
    }
    let outermost = DEPTH.with(|d| { d.set(d.get() + 1); d.get() == 1 });
    if outermost {
        MEMO.with(|memo| *memo.borrow_mut() = Some(Memo::default()));
    }
    let _scope = Scope;
    f()
}

/// Counters of the open scope (all zero outside a scope).
pub(crate) fn stats() -> Stats {
    MEMO.with(|memo| memo.borrow().as_ref().map(|m| m.stats).unwrap_or_default())
}

/// The positive-ABox closure of `input`: the stored one when this scope
/// already closed an equal input, otherwise `compute(&input)` (stored when a
/// scope is open). `compute` must be `rule_assertions::close`.
pub(super) fn closure(
    input: ClosureInput,
    compute: impl FnOnce(&ClosureInput) -> ClosureOutput,
) -> ClosureOutput {
    if DEPTH.with(Cell::get) == 0 {
        return compute(&input);
    }
    let stored = MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        let memo = memo.as_mut()?;
        let output = memo.closure.as_ref().filter(|(key, _)| *key == input).map(|(_, output)| output.clone())?;
        memo.stats.closure_hits += 1;
        Some(output)
    });
    if let Some(output) = stored {
        return output;
    }
    let output = compute(&input);
    MEMO.with(|memo| {
        if let Some(memo) = memo.borrow_mut().as_mut() {
            memo.closure = Some((input, output.clone()));
        }
    });
    output
}
