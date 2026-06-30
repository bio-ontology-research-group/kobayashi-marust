# 08 — `Reasoner/Kernel/Manager/` port-unit manifest

Subtree: `Source/Reasoner/Kernel/Manager/` — 39 files (11 classes as `.h/.cpp`
pairs + `ManagerSettings.h` namespace header), **3,672 LOC** (counted; the ~5.1k
figure includes blank/license lines). This is the **reasoner orchestration /
supervisor layer**, the C++ analogue of KM's `engine/src/orchestrate/`. It sits
*above* the completion/saturation calculus and drives it; it is not part of the
calculus.

All class `\brief` docstrings in the headers are literally "TODO"; purposes below
are inferred from signatures + includes + the `.cpp` bodies.

## 1. Classes by role

### A. Reasoner supervisor (the driver — Qt event-thread)
| class | LOC (.h/.cpp) | purpose |
|-------|------:|---------|
| `CReasonerManager` | 129 / 47 | **abstract base**: pure-virtual reasoner facade — `reasoningSatisfiableCalcualtionJob`, `reasoningQuery`, `prepareOntology`, cache getters, `getCalculationManager`/`getPrecomputationManager`, `initializeManager`. The public reasoner API. |
| `CReasonerManagerThread` | 301 / **1270** | **the concrete supervisor.** Multiply-inherits `CReasonerManager` + `CIntervalThread` + `CTaskHandleAlgorithmBuilder`. Runs a Qt event loop; owns the 7 caches, the calculation/precomputation/preprocessing/realization/answering managers, and `createTaskHandleAlgorithm()` (the factory that instantiates the completion + saturation algorithms + 6 cache handlers). Drives ontology-prep → query → satisfiable-box reasoning, statistics, progress. |
| `CAnalyseReasonerManager` | 96 / 298 | thin subclass adding query-progress analysis (`getQueryProgress`, work-count tallies, progress logging). |
| `CExperimentalReasonerManager` | 95 / 85 | further subclass with experimental `threadStarted`/overrides. |

### B. Per-ontology component-factory managers (lazy cache of workers)
| class | LOC | purpose |
|-------|------:|---------|
| `CPrecomputationManager` | 106 / 77 | `getPrecomputator(ontology, config)` — vends/caches a `CPrecomputator` per ontology. |
| `CPreprocessingManager` | 106 / 69 | `getPreprocessor(ontology, config)` — vends/caches a `CPreprocessor`. |
| `CRealizationManager` | 109 / 108 | `getRealizer(...)` + `getRealizationProgress()` — vends/caches a `CRealizer`. |

### C. Reasoning-task / requirement state holders (plain data)
| class | LOC | purpose |
|-------|------:|---------|
| `CReasoningTaskData` | 104 / 56 | per-query task state: query, callback, timing, statistics handle. |
| `CRequirementPreparingData` | 115 / 62 | tracks in-flight ontology-prep requirements; `getOntologyRequirementPreparingData(ont)`. |
| `COntologyRequirementPreparingData` | 123 / 102 | per-ontology requirement accumulator; `addOntologyRequirement(req)`. |
| `COntologyRequirementPair` | 89 / 45 | tiny `(ontology, requirement)` value pair. |
| `ManagerSettings.h` | 81 / — | forward-decl / namespace settings header (no class body). |

## 2. Algorithm-facing dependency (the cross-ref result)

**The completion + saturation algorithm and the Process layer depend on NONE of
these managers.** Grep over `Algorithm/ Process/ Calculation/` for all 11 class
names returns **0 references** (the only 2 hits — `CReasonerManager{,Thread}` —
are the *reverse* edge: the thread header `#include`s the algorithm headers).

Direction of the pointer is one-way and *downward*:
- `CReasonerManagerThread` → holds `CCalculationManager*` (defined in
  `Kernel/Calculation/`, **not** this subtree), and `createTaskHandleAlgorithm()`
  news up `CCalculationTableauCompletionTaskHandleAlgorithm` +
  `CCalculationTableauApproximationSaturationTaskHandleAlgorithm` + the 6 cache
  handlers and registers them with the calculation environment.
- The algorithm, per type-dag §4, holds a `CCalculationAlgorithmContext` /
  `CProcessContext` — **never** a `CReasonerManager*`.

⇒ **For the in-flight W3/W4 calculus port this entire subtree is out of scope.**
It is the W5/W6 *assembly/driver* layer: KM already has its own supervisor
(`orchestrate/` + `bin/km.rs`), so most of these classes will be **replaced, not
ported** — the Rust core is invoked by KM's existing orchestrator rather than by
a ported `CReasonerManagerThread`. The data-holder classes (group C) and the
factory managers (group B) only become relevant if/when the ported core needs its
own standalone driver.

## 3. Proposed port units (dependency order) — only if a native driver is built

Total = **6 units** (each ≤ ~800 lines). Recommend gating the whole subtree as
**W6-DEFER**: port lazily, only the slice KM's orchestrator can't already supply.

| unit | source | rust target | lines | notes |
|------|--------|-------------|------:|-------|
| MGR-1 data holders | `COntologyRequirementPair`, `CReasoningTaskData`, `CRequirementPreparingData`, `COntologyRequirementPreparingData` | `manager/data.rs` | ~265 | plain structs; no calculus logic. Port first (zero deps). |
| MGR-2 factory managers | `CPrecomputationManager`, `CPreprocessingManager`, `CRealizationManager` | `manager/factories.rs` | ~250 | `get*(ontology,config)` lazy-vend; arena/hash-cache the worker ids. |
| MGR-3 reasoner facade | `CReasonerManager` (abstract) | `manager/reasoner.rs` | ~50 | trait, not struct (pure-virtual base) — `[overload]` the two `reasoningSatisfiableCalcualtionJob` arities. |
| MGR-4 supervisor struct + lifecycle | `CReasonerManagerThread` fields + `initializeManager`/`readConfig`/`threadStarted`/`threadStopped`/`createTaskHandleAlgorithm`/cache+manager getters | `manager/thread_core.rs` | ~330 | struct-def wave; `createTaskHandleAlgorithm` is the wiring keystone. |
| MGR-5 supervisor reasoning flow | `getRequirementsForQuery`/`continueRequirementProcessing`/`prepare*Reasoning`/`initiateQueryReasoning` (lines ~338–959 of the .cpp) | `manager/thread_flow.rs` | ~620 | the event-driven prep→query→box pipeline; the big body. |
| MGR-6 supervisor finish/stats/events + subclasses | `finish*`/`updateBegining/Finishing...Statistics`/`loggingCalculationStatistics`/`processCustomsEvents` + `CAnalyseReasonerManager` + `CExperimentalReasonerManager` | `manager/thread_finish.rs` | ~700 | stats + Qt `CCustomEvent` dispatch; subclasses fold in here. |

## 4. Concerns ([tag] taxonomy)

- **[threading]** — `CReasonerManagerThread` *is* a thread (`CIntervalThread`)
  with a Qt event loop, timers (`processTimer`/`PROGRESSQUERYTIMER`), two
  `QSemaphore`s (`mBlockThreadPoolThreads...`) and a `CWatchDog`. The whole
  supervisor is the threading boundary. In Rust this maps to KM's existing
  process/thread orchestration — **do not** port Qt event dispatch verbatim;
  `[threading]`-note the replacement. `processCustomsEvents` + the `Events/`
  subdirectory (`CCalcQueryEvent`, `CPrepareOntologyEvent`, …) are Qt
  `CCustomEvent` payloads = an inter-thread message family → **tagged enum**
  `ManagerEvent` if a native driver is built.
- **[ownership]** — the thread **owns** 7 caches (`unsatCache`, `mSatExpCache`,
  `mReuseCompGraphCache`, `mSatNodeExpCache`, `mCompConsCache`, `mBackendAssCache`,
  `mOccStatsCache`) + 5 sub-managers (calc/precomp/preproc/realiz/answerer) by raw
  pointer; ported as arena ids / owned fields on one supervisor struct (single
  global ownership decision from PORT.md §5).
- **[memory-pool]** — none local: this layer holds no per-task bump allocators
  (those live in `Calculation/` + `Process/CProcessContext`). The managers only
  hold long-lived `QHash`/`QSet` registries (`mReasoningTaskDataHash`,
  `mQueryCallbackHash`, `mProcessingRequirementsSet`, …) → Rust `HashMap`/`HashSet`
  keyed by arena id.
- **[overload]** — `CReasonerManager` has 2-arity overloads of
  `reasoningSatisfiableCalcualtionJob`/`reasoningQuery`/`prepareOntology`
  (callback vs blocking-result); split into distinct snake_case names.
- **record-family → enum** — the `Events/` payloads (group above) are the one
  record family; no node/dependency-style record family lives in this subtree.
