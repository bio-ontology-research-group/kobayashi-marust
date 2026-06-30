# 00 — Type-Dependency DAG for the Konclude Completion Engine

Source of truth (READ ONLY):
`Konclude/Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.{h,cpp}`

Target: a faithful Rust port of `CCalculationTableauCompletionTaskHandleAlgorithm`
(the SROIQ tableau completion task handler). This file catalogues its type
closure and the order in which the foundation types must be ported.

NOTE: the `.cpp` (27 686 lines) has exactly ONE `#include` — its own `.h`. The
entire dependency surface therefore flows through the header. All paths below are
relative to `Konclude/Source/`.

---

## 1. Includes

### 1a. Konclude-internal headers (from the `.h`)

**Algorithm namespace (same dir, `Reasoner/Kernel/Algorithm/`)**
- `AlgorithmSettings.h` (container-macro + factory/cache typedefs)
- `CCalculationAlgorithmContextBase.h`  ← the per-thread shared-state context (central)
- `CCalculationStopProcessingException.h`, `CCalculationErrorProcessingException.h`, `CCalculationClashProcessingException.h`
- `CSatisfiableTaskConsistencyPreyingAnalyser.h`, `CSatisfiableTaskIncrementalConsistencyPreyingAnalyser.h`,
  `CSatisfiableTaskClassificationMessageAnalyser.h`, `CSatisfiableTaskMarkerIndividualPropagationAnalyser.h`,
  `CSatisfiableTaskPossibleAssertionCollectingAnalyser.h`, `CSatisfiableTaskPropertyClassificationMessageAnalyser.h`,
  `CSatisfiableTaskComplexAnsweringMessageAnalyser.h`, `CSatisfiableTaskPropagationBindingAnsweringMessageAnalyser.h`
- `CTrackedClashedDependencyLine.h`, `CTrackedClashedDescriptor.h`, `CTrackedClashedDescriptorHasher.h`
- `CDependencyFactory.h`, `CClashDescriptorFactory.h`, `CIndividualNodeManager.h`
- Cache handlers: `CUnsatisfiableCacheHandler.h`, `CSatisfiableExpanderCacheHandler.h`,
  `CReuseCompletionGraphCacheHandler.h`, `CCompletionGraphCacheHandler.h`,
  `CSaturationNodeExpansionCacheHandler.h`, `CComputedConsequencesCacheHandler.h`,
  `CIndividualNodeBackendCacheHandler.h`, `COccurrenceStatisticsCacheHandler.h`
- `CConceptNominalSchemaGroundingHandler.h`, `CDatatypeIndividualProcessNodeHandler.h`,
  `CIncrementalCompletionGraphCompatibleExpansionHandler.h`, `CIndexedIndividualAssertionConvertionVisitor.h`

**Task (`Reasoner/Kernel/Task/`)**
- `CSatisfiableCalculationTask.h`, `CCalculationConfigurationExtension.h`

**Process (`Reasoner/Kernel/Process/`)** — node/descriptor/queue/clash/blocking layer
- `CIndividualProcessNode.h`, `CConceptProcessDescriptor.h`, `CConceptProcessingQueue.h`
- restriction specs: `CLinkProcessingRestrictionSpecification.h`, `CBranchingORProcessingRestrictionSpecification.h`,
  `CBranchingMergingProcessingRestrictionSpecification.h`, `CTriggeredImplicationProcessingRestrictionSpecification.h`
- `CIndividualNodeBlockingTestData.h`, `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData.h`
- clashed descriptors: `CClashedConceptDescriptor.h`, `CClashedIndividualLinkDescriptor.h`,
  `CClashedIndividualDistinctDescriptor.h`, `CClashedNegationDisjointLinkDescriptor.h`
- `CBlockingAlternativeData.h`, `CBlockingAlternativeSignatureBlockingCandidateData.h`,
  `CExtendedCondensedReapplyConceptDescriptorATMOSTReactivation.h`, `CBranchingInstructionAddIndividualConcepts.h`

**Dependency nodes (`Reasoner/Kernel/Process/Dependency/`)** — ~30 explicit `#include`s,
one per tableau-rule dependency-node kind (AND/SOME/VALUE/NEGVALUE/ALL/ATLEAST/OR/
AUTOMATTRANSACTION/AUTOMATCHOOSE/SELF/DISTINCT/NOMINAL/FUNCTIONAL/ATMOST/MERGE/QUALIFY/
MERGEDCONCEPT/MERGEDLINK/IMPLICATION/CONNECTION/REUSEINDIVIDUAL/REUSECONCEPTS/
REUSECOMPLETIONGRAPH/MERGEPOSSIBLEINSTANCEINDIVIDUAL …), plus `CORDisjunctDependencyTrackPoint.h`
and `CDependencyTrackPoint.h`.

**Strategy (`Reasoner/Kernel/Strategy/`)**
- `CConceptProcessingPriorityStrategy.h`, `CIndividualProcessingPriorityStrategy.h`,
  `CTaskProcessingPriorityStrategy.h`, `CEqualDepthCacheOrientatedProcessingPriorityStrategy.h`,
  `CConcreteConceptProcessingOperatorPriorityStrategy.h`,
  `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy.h`,
  `CEqualDepthTaskProcessingPriorityStrategy.h`, `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy.h`

**Cache (`Reasoner/Kernel/Cache/`)**: `CExpanderBranchedLinker.h`, `CSignatureSatisfiableExpanderCacheEntry.h`
**Scheduler (`Scheduler/`)**: `CTask.h`, `CTaskHandleAlgorithm.h` (base class)
**Ontology (`Reasoner/Ontology/`)**: `CConceptProcessData.h`, `CConceptTextFormater.h`,
  `CDisjunctionBranchingStatistics.h`, `CConceptNegationPair.h`
**Memory (`Utilities/Memory/`)**: `CObjectMemoryPoolAllocator.h`, `CMemoryAllocationException.h`
**Other**: `Test/CCompletionGraphRandomWalkQueryGenerator.h` (debug only), `Logger/CLogger.h`

### 1b. Qt / std headers
None included directly. Qt types (`QString`, `QSet`, `QHash`, `QMap`, `QList`,
`QStringList`, `QTime`, `QVector`) arrive transitively via `AlgorithmSettings.h`
and the container macros. `cint64` (the project's `qint64`/`long long` alias) is
the pervasive scalar type. No `<...>` std includes appear in the `.h`.

---

## 2. External Konclude types referenced (219 distinct)

Full `type :: defining-header` table is in `scratchpad/typeloc.txt`. Distribution
of defining headers by directory:

| Directory | # types |
|---|---|
| `Reasoner/Kernel/Process/` | 72 |
| `Reasoner/Kernel/Process/Dependency/` | 68 |
| `Reasoner/Kernel/Algorithm/` | 32 |
| `Reasoner/Ontology/` | 13 |
| `Reasoner/Kernel/Strategy/` | 9 |
| `Reasoner/Kernel/Cache/` | 5 |
| `Utilities/{Memory,Container}/` | 6 |
| `Scheduler/` | 3 |
| container macros (`CPROCESSINGSET/LIST/HASH`, `CPROCESSHASH`) | 4 |
| `Test`, `Realizer`, `Task`, `Answerer`, `Logger` | 1 each |

Container macros resolve to Qt-managed wrappers:
- `CPROCESSINGSET` → `CQtManagedRestrictedModificationSet` (`AlgorithmSettings.h:65`)
- `CPROCESSINGLIST` → `CQtManagedRestrictedModificationList` (`AlgorithmSettings.h:64`)
- `CPROCESSINGHASH`/`CPROCESSHASH` → `CQtManagedRestrictedModificationHash` (`AlgorithmSettings.h:66`, `ProcessSettings.h:84`)

Several "types" are actually declared inside `*Settings.h` umbrella headers, not
their own file — port-relevant note:
- `CIndividual`, `CRole`, `CVariable` → `Reasoner/Ontology/OntologySettings.h`
- `CIndividualLinkEdge`, `CIndividualSaturationProcessNode`,
  `CRepresentativeVariableBindingPathSetData` → `Reasoner/Kernel/Process/ProcessSettings.h`
- `CDependency`, `CDependencyNode`, `CNonDeterministicDependencyNode`, `CBranchTreeNode`
  → `Reasoner/Kernel/Process/Dependency/DependencySettings.h`
- `CDependencyFactory`, `CSatisfiableExpanderCacheHandler`,
  `CSaturationNodeExpansionCacheHandler`, `CUnsatisfiableCacheHandler`
  → `Reasoner/Kernel/Algorithm/AlgorithmSettings.h` (typedef/alias)
- `CPossibleInstancesIndividualsMergingData` → `Reasoner/Realizer/RealizerSettings.h`
- `CSatisfiableCalculationTask` is forward-declared in
  `Reasoner/Kernel/Process/Dependency/CBranchTreeNode.h` (real def in Task/).

---

## 3. Dependency-ordered foundation layers (port FIRST → LAST)

### Layer 0 — Utilities / memory / containers (leaf; no Konclude deps)
`CAllocationObject`, `CMemoryManager`, `CMemoryAllocationManager`,
`CMemoryAllocationException`, `CObjectMemoryPoolAllocator`,
`CObjectParameterizingAllocator`; intrusive linkers `CXLinker`(`CLinker.h`),
`CXNegLinker`(`CNegLinker.h`), `CSortedLinker`, `CSortedNegLinker`,
`CXSortedNegLinker`; the Qt-managed container macros (`CPROCESSING{SET,LIST,HASH}`).
**Rust mapping:** linkers → `Vec`/intrusive slab; pool allocators → an arena
(`bumpalo`/typed-arena) — see §4. This layer is the [memory-pool] foundation.

### Layer 1 — Ontology core (depends only on Layer 0)
`CConcept`, `CRole`, `CIndividual`, `CVariable`, `CIRIName`,
`CConceptNegationPair`, `CConceptTextFormater`, `CConceptProcessData`,
`CConceptAssertionLinker`, `CRoleAssertionLinker`, `CReverseRoleAssertionLinker`,
`CDataAssertionLinker`, `CConceptRoleBranchingTrigger`,
`CDisjunctionBranchingStatistics`. These are the term/signature vocabulary the
whole calculus reads.

### Layer 2 — Process context & data box (depends 0–1)
`CProcessContext` (the per-task memory-pool + queue context),
`CProcessingDataBox` (the completion-graph container),
`CContext`/`CTaskContext` (Scheduler base of the context).

### Layer 3 — Process nodes, edges, descriptors, queues (depends 0–2)
Graph node: `CIndividualProcessNode` (+`CIndividualProcessNodeVector`,
`CIndividualSaturationProcessNode`); edges `CIndividualLinkEdge`,
`CDistinctEdge`, `CNegationDisjointEdge`; iterators `CRoleSuccessorLinkIterator`,
`CBlockingIndividualNodeCandidateIterator`, `CReapplyQueueIterator`,
`CCondensedReapplyQueueIterator`. Concept descriptors `CConceptDescriptor`,
`CConceptProcessDescriptor`, `CCondensedReapplyConceptDescriptor`,
`CPropagationBindingReapplyConceptDescriptor`,
`CExtendedCondensedReapplyConceptDescriptorATMOSTReactivation`. Label sets
`CReapplyConceptLabelSet`, `CReapplyConceptSaturationLabelSet`. Restriction specs
(`CLinkProcessingRestrictionSpecification`, `CBranchingOR…`, `CBranchingMerging…`,
`CTriggeredImplication…`, `CProcessingRestrictionSpecification`). Queues
(`CConceptProcessingQueue`, `CIndividualProcessingQueue`,
`CIndividualDepthProcessingQueue`, `CIndividualUnsortedProcessingQueue`,
`CIndividualReactivationProcessingQueue`, `CIndividualConceptBatchProcessingQueue`,
`CIndividualCustomPriorityProcessingQueue`, `CIndividualLinkerRotationProcessingQueue`).
Blocking/representative/variable-binding data (`CBlockingAlternativeData`,
`CSignatureBlockingReviewSet`, `CSignatureBlockingIndividualNodeConceptExpansionData`,
`CIndividualNodeAnalizedConceptExpansionData`, `CIndividualNodeBlockingTestData`,
`CReusingReviewData`, `CRepresentative*`, `CVariableBinding*`,
`CConceptVariableBindingPathSetHash`, `CSuccessorConnectedNominalSet`,
`CBackendNeighbourExpansion*`, the `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisation*` family).

### Layer 4 — Dependency / proof-tracking layer (depends 0–3)
`CDependency`, `CDependencyNode`, `CNonDeterministicDependencyNode`,
`CDependencyTrackPoint` (3rd most-referenced type overall),
`CNonDeterministicDependencyTrackPoint`, `CORDisjunctDependencyTrackPoint`,
`CBranchTreeNode`, and the ~50 concrete `*DependencyNode` rule records
(`CAND/COR/CSOME/CALL/CVALUE/CNEGVALUE/CATLEAST/CATMOST/CMERGE/CQUALIFY/CSELF/
CDISTINCT/CNOMINAL/CFUNCTIONAL/CIMPLICATION/CCONNECTION/CAUTOMAT*/CREUSE*/
CMERGED*/CPROPAGATE*/CREPRESENTATIVE*/CVARBIND*/CBINDPROPAGATE*/…`). These encode
why each fact was derived; they drive backjumping. Clash descriptors
(`CClashedDependencyDescriptor`, `CClashedConceptDescriptor`,
`CClashedIndividualLinkDescriptor`, `CClashedIndividualDistinctDescriptor`,
`CClashedNegationDisjointLinkDescriptor`) sit on top of these.

### Layer 5 — Strategies, factories, cache handlers (depends 0–4)
Priority strategies (`CConceptProcessingPriorityStrategy`,
`CIndividualProcessingPriorityStrategy`, `CTaskProcessingPriorityStrategy`,
`CEqualDepth*`, `CConcreteConceptProcessingOperatorPriorityStrategy`,
`CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy`,
`CUnsatisfiableCacheRetrievalStrategy`,
`CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy`).
Factories (`CDependencyFactory`, `CClashDescriptorFactory`,
`CIndividualNodeManager`). Cache handlers (`CUnsatisfiableCacheHandler`,
`CSatisfiableExpanderCacheHandler`, `CReuseCompletionGraphCacheHandler`,
`CCompletionGraphCacheHandler`, `CSaturationNodeExpansionCacheHandler`,
`CComputedConsequencesCacheHandler`, `CIndividualNodeBackendCacheHandler`,
`COccurrenceStatisticsCacheHandler`, `CConceptNominalSchemaGroundingHandler`,
`CDatatypeIndividualProcessNodeHandler`,
`CIncrementalCompletionGraphCompatibleExpansionHandler`) + cache entry types
(`CExpanderBranchedLinker`, `CSignatureSatisfiableExpanderCacheEntry`,
`CBackendRepresentativeMemoryLabelCacheItem`,
`CSaturationNodeAssociatedDependentNominalSet`).

### Layer 6 — Task, scheduler, message analysers (depends 0–5)
`CTask`, `CTaskHandleAlgorithm` (the base class to implement),
`CTaskProcessorContext`, `CSatisfiableCalculationTask`,
`CCalculationConfigurationExtension`, and the 8 `CSatisfiableTask*Analyser`
message analysers (post-processing of a finished completion graph).

### Layer 7 — The completion algorithm itself (depends on ALL above)
`CCalculationAlgorithmContextBase` (per-thread mutable state aggregator;
2nd most-referenced type — nearly every method takes
`CCalculationAlgorithmContextBase* calcAlgContext`) and
`CCalculationAlgorithmContext`, then the port target
`CCalculationTableauCompletionTaskHandleAlgorithm`.

### Cycles
Expect cycles WITHIN a layer, not across layers:
- **Layer 3 graph cycle:** `CIndividualProcessNode` ↔ `CIndividualLinkEdge`
  (nodes hold edges, edges point to nodes) and node ↔ its label/descriptor sets.
  In Rust resolve with arena indices / `id: cint64` handles rather than `&`/`Rc`.
- **Layer 4 cycle:** a `*DependencyNode` references the `CIndividualProcessNode`
  it annotates, while nodes carry their dependency descriptors. Same handle fix.
- **Layer 7 cycle:** `CCalculationAlgorithmContextBase` ↔ the algorithm (the
  context caches back-pointers to the handler's queues/strategies). Keep the
  context as the owner; pass the algorithm `&mut` to it, or split state out.
The header→header `#include` graph is otherwise a clean DAG (settings umbrella
headers are the only fan-in hubs).

---

## 4. Qt-heavy types & the memory-pool / context-allocator pattern  [ownership]/[memory-pool]

**Qt containers used directly as fields** (`grep` of the field block):
`QString` (dozens of debug-string fields), `QStringList`, `QSet<cint64>`,
`QSet<QString>`, `QSet<QSet<CConcept*>>`, `QHash<cint64,cint64>`,
`QHash<CIndividualProcessNode*, …>`, `QMap<cint64,cint64>`, `QList<cint64>`,
`QTime` (3 timers). Most are debugging/stats; the load-bearing ones are
`QSet<cint64>` (id sets: `mUnsatCachingSignatureSet`, `mPropCuttedIndiIds`) and
the `QHash` id→id maps. **Rust mapping:** `QSet<cint64>`→`HashSet<i64>`/`FxHashSet`,
`QHash`→`HashMap`, `QString`→`String` (debug fields can be dropped or
feature-gated), `QList/QVector`→`Vec`.

**The memory-pool / context-allocator pattern (critical to replicate):**
- Konclude does NOT use `new`/`delete` in the hot loop. Process objects
  (nodes, edges, descriptors, dependency nodes, label-set links) are bump-
  allocated from a per-task pool reached via the context:
  `CProcessContext`/`CCalculationAlgorithmContextBase::...->getMemoryAllocationManager()`
  returning a `CMemoryAllocationManager*` (`Utilities/Memory/`), then
  `CObjectMemoryPoolAllocator` / `CObjectParameterizingAllocator` placement-
  construct into it. `CMemoryAllocationException` is the OOM signal. Several
  methods take an explicit `CMemoryAllocationManager* tmpMemMan = nullptr` arg
  (e.g. `createTrackedClashesDescriptor`, `getCollectedFilteredClashedDescriptorsFromBranch`)
  to allocate scratch in a temporary pool that is dropped wholesale on backtrack.
- Lifetime model: pools are **task-scoped and reset on backtrack**, so individual
  objects are never freed — they die when the branch/task pool is rolled back.
  This is why raw `CXxx*` pointers are stored everywhere (no ref-counting).
- **Rust port consequence:** model each pool as an arena owned by the
  `CalculationAlgorithmContext`. Inter-object references become arena indices
  (`cint64` ids are already used as stable handles throughout — `getCorespondingIndividualNodeFromDependency`,
  the `QSet<cint64>`/`QHash<cint64,…>` id maps), so the port should standardise on
  index handles + arena, NOT `Rc<RefCell>`. Backtracking = truncate/reset the
  arena and the descriptor stacks to a saved watermark.

---

## Most-referenced types (top 10, by identifier occurrences in the `.h`)

| # | type | refs | defining header (`Source/…`) |
|---|---|---|---|
| 1 | `CIndividualProcessNode` | 563 | `Reasoner/Kernel/Process/CIndividualProcessNode.h` |
| 2 | `CCalculationAlgorithmContextBase` | 546 | `Reasoner/Kernel/Algorithm/CCalculationAlgorithmContextBase.h` |
| 3 | `CDependencyTrackPoint` | 202 | `Reasoner/Kernel/Process/Dependency/CDependencyTrackPoint.h` |
| 4 | `CConceptDescriptor` | 107 | `Reasoner/Kernel/Process/CConceptDescriptor.h` |
| 5 | `CConceptProcessDescriptor` | 72 | `Reasoner/Kernel/Process/CConceptProcessDescriptor.h` |
| 6 | `CConcept` | 66 | `Reasoner/Ontology/CConcept.h` |
| 7 | `CRole` | 36 | `Reasoner/Ontology/CRole.h` |
| 8 | `CTrackedClashedDescriptor` | 30 | `Reasoner/Kernel/Algorithm/CTrackedClashedDescriptor.h` |
| 9 | `CSortedNegLinker` (tmpl) | 28 | `Utilities/Container/CSortedNegLinker.h` |
| 10 | `CReapplyConceptLabelSet` | 25 | `Reasoner/Kernel/Process/CReapplyConceptLabelSet.h` |

(`CIndividualLinkEdge` 21, `CTrackedClashedDependencyLine` 19,
`CClashedDependencyDescriptor` 19, `CBlockingAlternativeData` 16, `CDependency` 14
round out the next tier.)
