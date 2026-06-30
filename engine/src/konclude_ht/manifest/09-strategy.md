# 09 — `Reasoner/Kernel/Strategy/` port-unit decomposition

W0 inventory of the priority / cache-retrieval strategy subtree. Source:
`/home/leechuck/Public/software/Konclude/Source/Reasoner/Kernel/Strategy/`
(18 files = 9 classes × `.h`+`.cpp`, 1671 lines total). These are the
rule-application priority and unsatisfiable-cache-retrieval policies the
completion engine consults; they replace the 5 strategy markers stubbed in
`completion/stubs.rs`.

## 1. Class catalogue

Four **abstract interface** classes (pure-virtual seams; `.cpp` = empty
ctor/dtor only) and five **concrete** implementations.

| class | h+cpp | role |
|-------|------:|------|
| **CConceptProcessingPriorityStrategy** (abstract) | 99+44 | interface: priority of a concept descriptor on a node, + disjunction-delay offsets. 4 pure virtuals: `readCalculationConfig`, `getPriorityForConcept`, `getPriorityOffsetForDisjunctionDelayedConsidering`, `getPriorityOffsetForDisjunctionDelayedProcessing`. |
| **CConcreteConceptProcessingOperatorPriorityStrategy** (concrete) | 104+271 | THE substantive one. FaCT++-`IAOEFLG`-style operator-code→priority table: `double priorities[200]`, `symAccessPri = priorities+100` (so signed concept op-codes index ±100 around the midpoint). Ctor fills the table per op-code (CCALL=12, CCSOME=4, CCATMOST=3, CCATLEAST=5, disjunctions=2, …). `getPriorityForConcept` looks up `symAccessPri[cCode]` (cCode negated for negated descriptors) with special-casing for `CCVARBINDPREPARE`, `CCATMOST`, `CCATLEAST` (param-scaled exp offsets). `readCalculationConfig` sets `mVariableBindingsPreparationDelaying` from the answerer propagation steering controller. |
| **CIndividualProcessingPriorityStrategy** (abstract) | 91+45 | interface: priority of a whole individual-process node. 1 pure virtual `getPriorityForIndividual`. |
| **CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy** (concrete) | 94+72 | the sole `CIndividualProcessingPriorityStrategy` subclass (note: filename says "ConceptProcessing" but it extends the *individual* interface). `getPriorityForIndividual` = (next concept-queue priority, ancestor-depth [+ `-1/(10+nodeID)+0.1` if `mAddIDIndiPriorization`], `mStrictIndiNodeProcessing`). `configureStrategy(strict, addID)`. |
| **CTaskProcessingPriorityStrategy** (abstract) | 100+44 | interface: branching/qualifying/merging/reusing task priorities. 4 pure virtuals: `getPriorityForTaskBranching`, `getPriorityForTaskQualifing`, `getPriorityForTaskMerging`, `getPriorityForTaskReusing`. |
| **CEqualDepthTaskProcessingPriorityStrategy** (concrete) | 94+85 | base concrete task strat; all 4 methods = `parentDepth + 1.` with small `+0.1`/`-branchNumber/(10*maxBranchCount)` tweaks. |
| **CEqualDepthCacheOrientatedProcessingPriorityStrategy** (concrete) | 92+113 | extends the above; overrides **only** `getPriorityForTaskBranching` to add (a) a completion-graph-cache hit check (consistence → cached task → node vector → label set) and (b) a branch-statistics learning offset (clash/sat/expanded factors). The other 3 task methods inherited. |
| **CUnsatisfiableCacheRetrievalStrategy** (abstract) | 100+47 | interface: when to consult the unsat cache. 7 pure virtuals `testUnsatisfiableCacheFor{Processing, DisjunctionBranching, MergingInitialization, SuccessorGeneration, BranchedDisjuncts, MergedIndividualNodes, QualifiedIndividualNodes}`. |
| **CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy** (concrete) | 97+79 | the sole subclass; trivial policy: `testUnsatisfiableCacheForProcessing` → `false`, the other six → `true`. |

## 2. Algorithm-facing interface (what the completion engine calls)

The engine `CCalculationTableauCompletionTaskHandleAlgorithm` constructs exactly
**one concrete per interface** (ctor, `.cpp:75–100`):

```
mConceptPriorityStrategy   = new CConcreteConceptProcessingOperatorPriorityStrategy();
mIndiAncDepthMasConProcPriStr = new CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy();
mIndividualPriorityStrategy = mIndiAncDepthMasConProcPriStr;
mTaskProcessingStrategy    = new CEqualDepthCacheOrientatedProcessingPriorityStrategy();   // (CEqualDepthTask… commented out)
mUnsatCachRetStrategy      = new CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy();
```

These pointers are handed to the **per-thread** context
(`CCalculationAlgorithmContextBase::initCalculationAlgorithmContext`), stored as
both `mXxxStrategy` and `mUsedXxxStrategy`. The algorithm invokes them through
the context accessor `ctx->getUsedXxxPriorityStrategy()->method(...)`. The
`mUsed*` indirection is a runtime-swap seam (CB cache reuse can repoint it);
in practice it equals the constructed concrete.

Measured call sites (in `Algorithm/*.cpp`):
- **Concept**: `getPriorityForConcept` ×6, `getPriorityOffsetForDisjunctionDelayedProcessing` ×2, `…DelayedConsidering` ×1, `readCalculationConfig` ×1.
- **Task**: `getPriorityForTaskReusing` ×5, `…Merging` ×2, `…Branching` ×1, `…Qualifing` ×1.
- **Unsat cache**: `testUnsatisfiableCacheFor*` ×11 (all 6 of the seven, `…ForProcessing` unused at these sites).
- **Individual**: `configureStrategy` ×2 on `mIndiAncDepthMasConProcPriStr`; but **`getPriorityForIndividual` has NO call site anywhere in `Reasoner/`** and `getUsedIndividualPriorityStrategy()` is defined-but-never-called. The individual strategy is **constructed + configured but dormant** in this build. Port it for fidelity; flag as currently-unreached.

So the engine-facing surface is **3 live interfaces** (concept, task, unsat
cache) + 1 dormant (individual), 4 ctor sites, ~25 invocation sites.

## 3. Proposed port units — trait vs enum

**Recommendation: tagged-enum dispatch, one enum per interface (4 enums), NOT
trait objects.** Rationale (faithful + idiomatic):
- The concrete set is **closed** and exactly one concrete is instantiated per
  interface — a `Box<dyn Trait>` vtable + heap alloc buys nothing the C++
  `new`-once does not already fix.
- The `mUsed*` swap seam is expressible as reassigning the enum value
  (`ctx.task_strategy = TaskPriorityStrategy::EqualDepthCacheOrientated(_)`),
  preserving the runtime-repoint behaviour.
- Per PORT.md §"Memory model", strategy heap objects owned by the algorithm and
  pointed-at by the per-thread context become **owned-by-value** in the context
  (no arena element, no `Id`) — an enum held by value is the direct realization
  and supersedes the `completion/stubs.rs` `Id<…Strategy>` placeholders.
- The abstract `.cpp` bodies are empty, so the interface contributes only the
  enum + its `match`-dispatch methods; no behaviour is lost.

Keep a thin Rust trait per interface ONLY as documentation of the C++ pure
virtuals if desired, but dispatch concretely via the enum `match`.

**Port units = 4** (one module file per interface family, dir
`konclude_ht/strategy/`; collapsible to a single `strategy.rs` given ~1.7k lines):

| unit | file | C++ sources | enum |
|------|------|-------------|------|
| **STR-1 concept** | `strategy/concept.rs` | CConceptProcessingPriorityStrategy + CConcreteConceptProcessingOperatorPriorityStrategy | `ConceptPriorityStrategy` (variant `ConcreteOperator`) — the 200-slot table + lookup |
| **STR-2 individual** | `strategy/individual.rs` | CIndividualProcessingPriorityStrategy + CIndividualAncestorDepthMaximum… | `IndividualPriorityStrategy` (variant `AncestorDepthMaximum`) — DORMANT, port for fidelity |
| **STR-3 task** | `strategy/task.rs` | CTaskProcessingPriorityStrategy + CEqualDepthTask… + CEqualDepthCacheOrientated… | `TaskPriorityStrategy` (variants `EqualDepth`, `EqualDepthCacheOrientated`; the latter delegates 3 of 4 methods to the former) |
| **STR-4 unsat cache** | `strategy/unsat_cache.rs` | CUnsatisfiableCacheRetrievalStrategy + CGenerativeNonDeterministic… | `UnsatCacheRetrievalStrategy` (variant `GenerativeNonDeterministic`) — trivial const returns |

(STR-1 ≈ 315 lines is the only non-trivial unit; STR-2/3/4 are <120 each.)

## 4. Threading / ownership notes

- **[threading]** Strategies are **per-worker-thread**, owned by that thread's
  context (PORT.md §W3: one context per thread). No cross-thread sharing → no
  `Send`/`Sync`/locking needed; held by value in the context, not in a shared
  arena.
- **[pointer-alias]** `CConcreteConceptProcessingOperatorPriorityStrategy` stores
  `priorities = new double[200]` and `symAccessPri = priorities + 100` (an
  interior alias used so negative op-codes index below the midpoint). Port as a
  single `priorities: [f64; 200]` (or `Box<[f64;200]>`) by value and replace the
  alias with index arithmetic `priorities[(100 + code) as usize]`. Behaviour
  identical; note the alias removal at the site.
- **[ownership]** Every strategy method dereferences `CIndividualProcessNode* /
  CConceptDescriptor* / CSatisfiableCalculationTask*` raw pointers. Per the
  global arena decision these become `Id`s resolved through `&Ctx` threaded as
  params (same as the W3 completion bodies). The dormant
  `getPriorityForIndividual` reads the node's concept-processing queue —
  resolve via the databox/node arena.
- **[api]** Two deep cross-layer derefs must defer until their layers land:
  (a) `CConcrete…::readCalculationConfig` reaches
  `satCalcTask->getSatisfiableAnswererBindingPropagationAdapter()->…
  ->finalizeWithClashing()` (Task + answerer layers, not yet ported);
  (b) `CEqualDepthCacheOrientated::getPriorityForTaskBranching` reaches
  `ontology->getConsistence()->getConsistenceModelData()` → cached task →
  node vector → label set (Consistence/model + Process layers). Port the control
  flow now, stub these reaches with `W?-DEFER[api]` until the dependencies exist.
- These units belong to **W6** in the PORT.md status table (`Cache / Manager /
  Strategy / Task`), but the concept + task + unsat enums are needed by the W3
  completion bodies' priority calls, so STR-1/STR-3/STR-4 are pull-forward
  candidates once the context threading lands.
