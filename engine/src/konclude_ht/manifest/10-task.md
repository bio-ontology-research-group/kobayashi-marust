# Manifest 10 — Task / Job layer (`Reasoner/Kernel/Task/`)

Source of truth: Konclude checkout at `/home/leechuck/Public/software/Konclude`.
READ ONLY of Konclude. This file catalogues C++ for a faithful Rust port.

Covers `Source/Reasoner/Kernel/Task/` — **27 classes across 53 files + 1 settings
header, ~6.5k lines.** This is the **task/job layer** the calculation controller
(manifest 03, `CConcurrentTaskCalculationManager`) schedules and that the
completion + saturation algorithms (manifests 01/03) run against. The central type
is `CSatisfiableCalculationTask` — the unit of work a worker thread dereferences in
`handleTask(...)`. Everything else here either (a) configures it
(`CCalculationConfigurationExtension`), (b) is a scheduler-protocol communicator
(status propagator / callback executer), (c) carries a per-test result
(`C*TaskData`), or (d) is an observer/message **adapter** the algorithm pulls off
the task to emit classification / realization / answering / cache results.

Rust target: `task/` (new subtree). Layering note: this layer sits **above** the
process model (`process/`, manifest 02) and is referenced **by** `completion/`
(manifest 01) via the algorithm context. Port it in **W4/W6** (after the completion
+ saturation algorithm bodies exist), since the adapters are call-out seams the
algorithm bodies invoke; the bare struct-defs can land earlier as stubs.

---

## Part 1 — Class inventory (grouped)

Line counts are `h + cpp`. "purpose" is one line. The scheduler base classes
(`CTask`, `CTaskStatus`, `CTaskResult`, `CBooleanTaskResult`, `CTaskHandleContext`,
`CTaskCallbackExecuter`, `CTaskStatusPropagator`) live OUTSIDE this subtree under
`Source/Scheduler/` — they are a **prerequisite port** (a small `scheduler/`
module) and are noted but not units here.

### Group A — Task base / core (the work item + its config)

| class | h+cpp | purpose |
|---|---:|---|
| **CSatisfiableCalculationTask** | 223+389 | **THE central work item.** `: public CTask, public CSatisfiableCalculationJobInstantiation`. Owns the per-test `CProcessContextBase` + `CProcessingDataBox` (lazily allocated from the task memory pool), the `CCalculationConfigurationExtension`, stats collector, and **18 adapter back-pointers**. Holds the boolean (SAT/UNSAT) result + task status. `initTask` / `initBranchDependedSatisfiableCalculationTask` / `initUndependedSatisfiableCalculationTask` / `makeTaskReference` build the per-branch task tree (branch tasks share the parent's databox/context + copy adapter pointers). `taskType` ∈ {`CALCULATIONTABLEAUCOMPLETIONTASK=0`, `CALCULATIONTABLEAUAPPROXIMATEDSATURATIONTASK=1`}. |
| CSatisfiableCalculationJobInstantiation | 85+45 | Trivial base mixin (`getInstatiation()` returns `this`) co-inherited by the task; marks it as instantiable from a calculation job. |
| **CCalculationConfigurationExtension** | 492+1090 | **The reasoner feature-flag bag.** `: public CLocalConfigurationFixedExtension`. ~130 lazily-read config flags (`mConf*Activated` + a parallel `mConf*Checked` "already-resolved" bit per flag) + ~20 `cint64` numeric limits. Each `is*Activated()` reads-once-then-caches from the config tree. Governs blocking mode, caching, saturation, backjumping, datatype reasoning, backend expansion, etc. Big but mechanical. |
| CCalculationStatisticsCollector | 90+46 | Per-task statistics sink (`addProcessingStatistics(name,value)` into a hash); flushed at `completeTask`. |
| TaskSettings.h | 72 | Forward-decl + one constant `PWORKBACKTRACKINGWORK=1000` (a task priority). Fold into `task/mod.rs`. |

### Group B — Scheduler-protocol communicators (the [threading] seams)

| class | h+cpp | purpose |
|---|---:|---|
| **CSatisfiableCalculationTaskStatusPropagator** | 92+138 | `: public CTaskStatusPropagator`. The **event-driven up/down result propagation** rule. `updateTaskStatus` / `completeTaskStatus`: on a child task finishing, propagate SAT(`true`) UP to the parent (OR-semantics: any satisfiable child ⇒ parent satisfiable), cancel sibling tasks when the parent already resolved, and propagate error/cancel state. This is the core of how the branch task-tree collapses to one boolean. |
| **CSatisfiableCalculationTaskJobCallbackExecuter** | 94+68 | `: public CTaskCallbackExecuter`. `executeCallback(task, cb)` fires the job's `CJobSatisfiableCallbackContextData` with the final boolean when the root task completes — the hand-back to the query/consistency caller. |

### Group C — Per-test result data (record family; `overtakeData()` consumers)

| class | h+cpp | purpose |
|---|---:|---|
| CConsistenceTaskData | 98+70 | `: public CConsistenceData`. Holds the deterministic + completion-graph-cached `CSatisfiableCalculationTask*` for a consistency test; `overtakeData()` pulls the result out. |
| CIncrementalConsistenceTaskData | 119+122 | `: public CConsistenceTaskData`. Adds `mPrevOntology` + `mPrevConsData` for incremental re-consistency (reuse the previous test's completion graph). |
| CSaturationTaskData | 94+64 | `: public CSaturationData`. Holds the saturation `CSatisfiableCalculationTask*`; `overtakeData()` exposes the saturated-model result. |

### Group D — Preying adapter (consistency/saturation observer bridge)

| class | h+cpp | purpose |
|---|---:|---|
| CTaskPreyingAdapter | 102+88 | Holder bridging a task to a `CConsistenceObserver` / `CSaturationObserver` / `CTaskPreyingListner` ("preying" = a follow-up task consuming this task's model). |
| CTaskPreyingListner | 85+44 | Listener interface notified when a preyed task's data is available. |

### Group E — Satisfiable-task message/observer adapters (call-out seams)

All **standalone holder structs (no base class)** — config bundles the algorithm
reads off the task to know *what to extract and where to send it*. 16 classes;
mostly ctor + getters + a few flags. Grouped by phase they serve:

| class | h+cpp | phase / purpose |
|---|---:|---|
| CSatisfiableTaskClassificationMessageAdapter | 117+76 | Classification: testing concept/ontology + `CClassificationMessageDataObserver` + 7 `EFEXTRACT*` extraction flags (subsumers/possible-subsumers/pseudo-model). |
| CSatisfiableTaskClassificationRoleMarkedMessageAdapter | 101+67 | Classification of marked roles. |
| CSatisfiableTaskRealizationMarkedCandidatesMessageAdapter | 100+66 | Realization: marked candidate individuals message. |
| CSatisfiableTaskRealizationPossibleAssertionCollectingAdapter | 95+51 | Realization: collect possible assertions. |
| CSatisfiableTaskRealizationPossibleInstancesMergingAdapter | 96+57 | Realization: merge possible instances. |
| CSatisfiableTaskAnswererSubsumptionMessageAdapter | 102+69 | Query answering: subsumption messages. |
| CSatisfiableTaskAnswererBindingPropagationAdapter | 105+72 | Query answering: variable-binding propagation. |
| CSatisfiableTaskAnswererInstancePropagationMessageAdapter | 108+79 | Query answering: instance propagation. |
| CSatisfiableTaskAnswererQueryingPropagationAdapter | 102+68 | Query answering: querying propagation (base of the two above). |
| CSatisfiableTaskAnswererQueryingMaterializationAdapter | 102+70 | Query answering: materialization. |
| CSatisfiableTaskIncrementalConsistencyTestingAdapter | 98+62 | Incremental consistency test hook. |
| CSatisfiableTaskIndividualDependenceTrackingAdapter | 95+64 | Track individual dependence (for incremental). |
| **CSatisfiableTaskRepresentativeBackendUpdatingAdapter** | 135+153 | **Most-used adapter (12 algo call sites).** Backend representative-cache update: unsat-computed / expansion-limit-reached / propagation-cut flags + counters. The only adapter with non-trivial state logic. |
| CSatisfiableTaskCancellationAdapter | 84+42 | Cancellation hook (cooperative cancel check). |
| CSaturationIndividualsAnalysingAdapter | 90+52 | Saturation: analyse saturated individuals observer. |
| CSaturationOccurrenceStatisticsCollectingAdapter | 84+42 | Saturation: collect concept/role occurrence statistics. |

---

## Part 2 — Which task types the algorithm + controller actually use

**The algorithm holds exactly ONE task type: `CSatisfiableCalculationTask*`.**

- The completion algorithm (`CCalculationTableauCompletionTaskHandleAlgorithm`)
  and saturation algorithm both reach the task **through the per-thread context**,
  not directly: `CCalculationAlgorithmContext::getUsedSatisfiableCalculationTask()`
  returns `mUsedSatCalcTask` (a `CSatisfiableCalculationTask*`), set in
  `CCalculationAlgorithmContextBase::initTaskProcessContext(processContext,
  satCalcTask)`. `handleTask(CTaskProcessorContext*, CTask* task)` down-casts the
  scheduler `CTask*` to `CSatisfiableCalculationTask*` once at entry.
- From that one task the algorithm pulls the **adapters** as call-out seams. Use
  counts in the completion cpp (the ones that MUST be ported with real bodies for
  classification/realization/answering to work; the rest are inert holders unless
  their phase runs):
  `getSatisfiableRepresentativeBackendCacheUpdatingAdapter` ×12,
  `getConsistenceAdapter` ×7, `getSatisfiableAnswererBindingPropagationAdapter` ×6,
  `getClassificationMessageAdapter` ×4, `getSatisfiableTaskIncrementalConsistencyTestingAdapter` ×3,
  `getSatisfiablePossibleInstancesMergingAdapter` ×3, plus answerer-instance ×2,
  individual-dependence/materialization/cancellation ×1 each.
- **The two `taskType` discriminants are the routing fork**: `isCalculationTableauCompletionTask()`
  (→ full branching completion) vs `isCalculationTableauSaturationTask()` (→ the
  cheap saturation pre-pass of manifest 03). Same task class, different `mTaskType`
  + different `CTaskHandleAlgorithm` injected per thread by the builder (manifest 03).
- **The controller** (`CConcurrentTaskCalculationManager::calculateTask(CSatisfiableCalculationTask*)`)
  posts the task to the scheduler; `CSatisfiableCalculationTaskFromCalculationJobGenerator`
  (in `Reasoner/Generator/`, NOT this subtree — a prerequisite) builds the task from
  a job. The env (`CConcurrentTaskCalculationEnvironment`) installs one
  `CSatisfiableCalculationTaskStatusPropagator` + one
  `CSatisfiableCalculationTaskJobCallbackExecuter` shared across worker threads.
- The `C*TaskData` record family is consumed **outside** the kernel (Consistiser /
  Realizer call `overtakeData()` to pull the boolean/model out of the finished task).
  Port them when those callers are ported; for an initial classification-only port
  only `CConsistenceTaskData` + `CSaturationTaskData` are exercised.

**MINIMAL-PORT subset** (what a classification-only completion run actually
dereferences): `CSatisfiableCalculationTask` + `CCalculationConfigurationExtension`
+ `CCalculationStatisticsCollector` + the status propagator + callback executer +
`CSatisfiableTaskClassificationMessageAdapter` +
`CSatisfiableTaskRepresentativeBackendUpdatingAdapter` + `CConsistenceTaskData` +
`CSaturationTaskData`. The 14 answering/realization adapters are dead weight until
query answering / realization is ported (defer as zero-size marker structs, exactly
as `completion/stubs.rs` already does for the 8 message analysers — see W3 note).

---

## Part 3 — Proposed port units (dependency order)

8 units. Sizes are well under the ~800-line cap (this layer is mostly small
holders), so units are grouped by role, not split for size. **Prerequisite (not a
Task unit): a small `scheduler/` port** of `CTask` + `CTaskStatus` + `CTaskResult`
+ `CBooleanTaskResult` + `CTaskHandleContext` + `CTaskCallbackExecuter` +
`CTaskStatusPropagator` from `Source/Scheduler/` — every unit below depends on it.

1. **TASK-1 Config extension** (`task/config.rs`, ~1580 lc): `CCalculationConfigurationExtension`
   — the ~130-flag read-once-cache bag + numeric limits. Self-contained (only depends
   on the config tree, port the `Config/` accessor as an opaque provider). Port FIRST:
   everything reads it. **[ownership]**: the `mConf*Checked` lazy-resolve bits become
   `Option<bool>` per flag, or a `Cell<...>` cache; faithful read-once preserved.
2. **TASK-2 Statistics collector** (`task/stats.rs`, ~136 lc): `CCalculationStatisticsCollector`.
   Trivial; needed by the task ctor.
3. **TASK-3 The task struct** (`task/satisfiable_task.rs`, struct-def + lifecycle
   bodies, ~610 lc): `CSatisfiableCalculationTask` + `CSatisfiableCalculationJobInstantiation`
   + `TaskSettings` constant. Fields = 18 adapter ptrs (→ `Option<Id>`/`Option<Box>`
   markers) + process-context/databox **owned ids** into the per-thread arena
   (**[ownership]**: C++ allocates the databox from the task pool and back-points;
   port as `ProcessContextId` + `DataBoxId` into the context arena, mirroring the
   W3 "context owns the arenas" decision). Methods: `init_task` /
   `init_branch_depended_*` / `init_undepended_*` / `make_task_reference` /
   `complete_task` / the type discriminants / adapter setters+getters.
   **[threading]**: `mActiveTaskReferenceCount` + `mDependedStatusUpdatesCount` on the
   `CTask` base are atomics in the concurrent scheduler — see Part 4.
4. **TASK-4 Status propagator** (`task/status_propagator.rs`, ~138 lc):
   `CSatisfiableCalculationTaskStatusPropagator` — the up/down OR-collapse rule.
   Faithful control-flow port; the interesting logic of the layer.
5. **TASK-5 Callback executer** (`task/callback_executer.rs`, ~68 lc):
   `CSatisfiableCalculationTaskJobCallbackExecuter`. Depends on the Query
   `CJobSatisfiableCallbackContextData` (opaque until Query is ported).
6. **TASK-6 Task result data** (`task/task_data.rs`, ~256 lc): `CConsistenceTaskData`
   + `CIncrementalConsistenceTaskData` + `CSaturationTaskData`. The `overtakeData()`
   record family — see Part 4 enum note.
7. **TASK-7 Preying + saturation observer adapters** (`task/preying.rs`, ~370 lc):
   `CTaskPreyingAdapter` + `CTaskPreyingListner` + `CSaturationIndividualsAnalysingAdapter`
   + `CSaturationOccurrenceStatisticsCollectingAdapter`.
8. **TASK-8 Message/answering adapters** (`task/message_adapters.rs`, ~1100 lc
   across 14 tiny holders): the classification / realization / answering adapter
   bag (Group E rows 1–14). Initially **stub as zero-size markers** (defer real
   bodies to the realization/answering wave); only
   `CSatisfiableTaskClassificationMessageAdapter` +
   `CSatisfiableTaskRepresentativeBackendUpdatingAdapter` need real bodies for a
   classification-only run, so optionally split those two into TASK-8a.

**Total: 8 port units** (+ the `scheduler/` prerequisite, counted under its own
manifest), of which **~3 (TASK-1/3/4) are load-bearing** for a first
classification run and **5 are holder/observer boilerplate**.

---

## Part 4 — Threading model + record-family notes

### [threading] — this layer IS the concurrency/job substrate
- **Event-driven task scheduler, parallelism over independent satisfiability tasks.**
  As manifest 03 established: 1 scheduler thread + 1 completor thread + N worker
  threads; **each worker owns a private `CTaskHandleAlgorithm` + a private
  centralized-but-limited memory pool**. There is **no shared mutable calc state** —
  a `CSatisfiableCalculationTask` and its databox/context are allocated from the
  owning thread's pool and processed by that thread.
- **The cross-thread coupling is the task tree, not shared memory.** Branch tasks
  (`initBranchDependedSatisfiableCalculationTask`) form a parent/child tree sharing
  the parent databox+context by reference. The `CTask` base carries
  `mActiveTaskReferenceCount` + `mDependedStatusUpdatesCount` — **atomic counters**
  (`incActiveReferenceCount`/`dec...`) the scheduler uses to know when a subtree is
  done. **[threading] port note**: these become `AtomicI64` on the ported `CTask`
  base; the status propagator (TASK-4) is the only logic that races on them, and it
  runs under the scheduler's per-task serialization, so a faithful port keeps the
  atomics but does not need extra locks. The OR-collapse (`updateTaskStatus`:
  SAT-up, cancel-siblings) is the message-passing the "event-driven" model rides on.
- **Result installation is single-writer**: `CBooleanTaskResult::installResult` is
  guarded by `hasResult()` checks in the propagator — port faithfully; the
  first-finisher-wins semantics (any satisfiable branch ⇒ parent SAT, then cancel
  the rest) is the load-bearing concurrency behaviour.
- **Memory pool**: every `init*`/`get*Context` call routes through
  `CTaskMemoryPoolAllocationManager` / `CObjectParameterizingAllocator` — the
  per-thread bump pool. **[memory-pool]**: replace with the context-owned arena
  (`Arena<...>` + typed ids), consistent with the W1/W3 global `[ownership]`/`[memory-pool]`
  decision in PORT.md; the task holds ids, not raw pointers.

### Record-family → tagged enum
- **The `C*TaskData` "overtakeData()" family** (`CConsistenceTaskData`,
  `CIncrementalConsistenceTaskData : CConsistenceTaskData`, `CSaturationTaskData`)
  is a small inheritance family with a virtual `overtakeData()`. Port as **one
  tagged enum `TaskData { Consistence{det,graph_cached}, IncrementalConsistence{..,
  prev_ontology, prev_cons_data}, Saturation{task} }`** with a single `overtake_data`
  match — mirroring the W2 `DependencyNode`/`DepKind` enum decision (manifest 02).
  Incremental "extends" Consistence ⇒ flatten its two extra fields into the
  `IncrementalConsistence` variant.
- **The 16 adapters are NOT a polymorphic family** — they are independent holder
  structs co-owned by the task (18 distinct `m*Adapter` pointer fields), each a
  different observer interface. Keep them as **separate structs** held as
  `Option<...>` on the task; do NOT collapse to one enum (they are set/got
  independently and serve different phases). This is the one place a "record family"
  intuition does NOT apply — confirmed by the task holding all 18 simultaneously.
