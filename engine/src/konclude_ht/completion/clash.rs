//! `completion::clash` — the clash / stop propagation mechanism replacing
//! Konclude's `throw CCalculationClashProcessingException` /
//! `throw CCalculationStopProcessingException` control flow
//! (`Source/Reasoner/Kernel/Algorithm/CCalculationClashProcessingException.{h,cpp}`,
//! `CCalculationStopProcessingException.{h,cpp}`).
//!
//! ## The C++ control flow
//! Konclude drives clash and stop decisions with exceptions thrown DEEP inside the
//! `apply*Rule` methods and caught once, in `handleTask`'s `try { … } catch (…)`:
//!
//! ```cpp
//! throw CCalculationClashProcessingException(clashDepDes);   // carries the clash
//! throw CCalculationStopProcessingException(taskCompleted);  // carries completion
//! ```
//!
//! The throw unwinds the whole rule call stack (`tableauRuleProcessing` →
//! `applyXRule` → helper → …) straight to the `handleTask` catch, which routes it
//! (`clashedBacktracking` for a clash, the completion epilogue for a stop).
//!
//! ## The port — a pending signal on the per-task context
//! KONCLUDE-PORT-NOTE[exceptions]: Rust has no exception-as-control-flow, and the
//! two faithful encodings are (A) thread a `Result<…, CalcSignal>` return through
//! every rule method, or (B) store a pending signal on the per-task context that
//! rule methods set and callers check. We choose **(B)**, for two reasons:
//!
//!   1. **Faithfulness.** The clash/stop is per satisfiability task and is raised
//!      and consumed entirely within one `handleTask` invocation; the per-task
//!      `CalculationAlgorithmContext` (threaded as `&mut calc_alg_context` through
//!      every rule method already) is exactly the object whose lifetime the C++
//!      exception's raise→catch spans. The unwind becomes a cooperative early
//!      return that each frame performs after observing the flag — the same set of
//!      frames the C++ stack-unwind passes through, in the same order.
//!   2. **Least invasive.** The ~450 already-compiling rule methods keep their
//!      current signatures (they return what they returned: `()`, `bool`, an `Id`,
//!      …). Option (A) would rewrite every signature in the kernel to return
//!      `Result`, churning units u02..u36 that already compile. Option (B) adds
//!      ONE field to the context plus the helper calls; the rule bodies gain a
//!      `self.…raise_clash(c); return …;` at each C++ `throw` site (the un-defer
//!      wave) and a `if calc_alg_context.has_pending_signal() { return …; }` after
//!      each fallible sub-call. No signature changes.
//!
//! The two C++ exception classes map onto the two non-`Continue` variants of
//! [`CalcSignal`]; `Continue` is the "no pending throw" state (the normal path).
//!
//! ## Bridge to `handleTask` (`u01`)
//! `u01` already models `handleTask`'s OWN `try`/`catch` as an immediately-invoked
//! closure returning `Result<(), HandleTaskException>` (its explicit in-`handleTask`
//! throws become `Err(…)`, its catch clauses the `match` arms). THIS module is the
//! complementary half: the channel for throws raised DEEP in the called rules. In
//! the un-defer wave the closure drains the context after each rule call —
//! `if let Some(sig) = calc_alg_context.take_pending_signal() { return Err(sig.into_handle_task_exception()); }`
//! — converting a deep `CalcSignal` into the `u01` `HandleTaskException` the catch
//! already handles. (The `into_…` adapter lands with that wave; `u01`'s private
//! enum is left untouched here so the compiling driver is not disturbed.)

#![allow(dead_code)]

use super::super::process::ClashDescId;
use super::context::{CalculationAlgorithmContext, CalculationAlgorithmContextBase};

/// The pending clash/stop signal carried on the per-task context — the Rust
/// stand-in for an in-flight `CCalculation{Clash,Stop}ProcessingException`.
///
/// `Continue` is the absence of a pending throw. `Clash`/`Stop` mirror the two
/// exception classes (and their payloads) one-for-one.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CalcSignal {
    /// No pending throw — the normal processing path.
    Continue,
    /// Port of `throw CCalculationClashProcessingException(clashDepDes)`.
    /// Carries the `CClashedDependencyDescriptor*` the `handleTask` catch hands to
    /// `clashedBacktracking` (`mClashDepDes` → `ClashDescId`).
    Clash(ClashDescId),
    /// Port of `throw CCalculationStopProcessingException(taskCompleted)`.
    /// `task_completed` mirrors `mTaskCompleted` / `isTaskCompletedProcessed()`.
    Stop { task_completed: bool },
}

impl Default for CalcSignal {
    /// The default state is "no pending throw".
    fn default() -> Self {
        CalcSignal::Continue
    }
}

impl CalcSignal {
    /// True for any pending throw (i.e. not `Continue`).
    #[inline]
    pub fn is_pending(self) -> bool {
        !matches!(self, CalcSignal::Continue)
    }
}

// ===========================================================================
// The raise / check / consume helpers on the per-task context.
//
// These are the `throw` / catch primitives: `raise_*` plants the pending signal
// (the C++ `throw`), `has_pending_signal` is the per-frame "did something below me
// throw?" check that drives the cooperative early-return (the C++ stack unwind),
// and `take_pending_signal` is the `handleTask` catch that consumes it.
// ===========================================================================

impl CalculationAlgorithmContext {
    /// Port of `throw CCalculationClashProcessingException(clashDepDes)`: record a
    /// pending clash carrying `clash`. The caller returns immediately afterwards;
    /// each enclosing frame observes [`Self::has_pending_signal`] and returns in
    /// turn, reproducing the C++ unwind to the `handleTask` catch.
    #[inline]
    pub fn raise_clash(&mut self, clash: ClashDescId) {
        self.pending_signal = CalcSignal::Clash(clash);
    }

    /// Port of `throw CCalculationStopProcessingException(taskCompleted)`: record a
    /// pending stop. `task_completed` is the C++ `taskCompleted` ctor argument
    /// (default `true` in Konclude).
    #[inline]
    pub fn raise_stop(&mut self, task_completed: bool) {
        self.pending_signal = CalcSignal::Stop { task_completed };
    }

    /// True if a clash or stop is in flight — the per-frame unwind check a caller
    /// runs after each fallible sub-call (`if ctx.has_pending_signal() { return …; }`).
    #[inline]
    pub fn has_pending_signal(&self) -> bool {
        self.pending_signal.is_pending()
    }

    /// Peek at the pending signal without consuming it.
    #[inline]
    pub fn pending_signal(&self) -> CalcSignal {
        self.pending_signal
    }

    /// The `handleTask` catch: consume the pending signal, resetting the context to
    /// `Continue`. Returns `None` when nothing is pending.
    #[inline]
    pub fn take_pending_signal(&mut self) -> Option<CalcSignal> {
        let sig = self.pending_signal;
        self.pending_signal = CalcSignal::Continue;
        if sig.is_pending() {
            Some(sig)
        } else {
            None
        }
    }

    /// Clear any pending signal back to `Continue` (used when a frame deliberately
    /// absorbs a throw, e.g. an inner try that recovers).
    #[inline]
    pub fn clear_pending_signal(&mut self) {
        self.pending_signal = CalcSignal::Continue;
    }
}

// --- Base forwarders (the owned context lives in `base`; same idiom as the other
// `CalculationAlgorithmContextBase` accessors). Rule methods thread the Base, so
// they call these. ---
impl CalculationAlgorithmContextBase {
    /// Forwarder for [`CalculationAlgorithmContext::raise_clash`].
    #[inline]
    pub fn raise_clash(&mut self, clash: ClashDescId) {
        self.base.raise_clash(clash);
    }
    /// Forwarder for [`CalculationAlgorithmContext::raise_stop`].
    #[inline]
    pub fn raise_stop(&mut self, task_completed: bool) {
        self.base.raise_stop(task_completed);
    }
    /// Forwarder for [`CalculationAlgorithmContext::has_pending_signal`].
    #[inline]
    pub fn has_pending_signal(&self) -> bool {
        self.base.has_pending_signal()
    }
    /// Forwarder for [`CalculationAlgorithmContext::pending_signal`].
    #[inline]
    pub fn pending_signal(&self) -> CalcSignal {
        self.base.pending_signal()
    }
    /// Forwarder for [`CalculationAlgorithmContext::take_pending_signal`].
    #[inline]
    pub fn take_pending_signal(&mut self) -> Option<CalcSignal> {
        self.base.take_pending_signal()
    }
    /// Forwarder for [`CalculationAlgorithmContext::clear_pending_signal`].
    #[inline]
    pub fn clear_pending_signal(&mut self) {
        self.base.clear_pending_signal();
    }
}
