# Manifest 03 — Approximate Saturation pre-pass + Calculation controllers

Source of truth: Konclude checkout at `/home/leechuck/Public/software/Konclude`.
READ ONLY of Konclude. This file catalogues C++ for a faithful Rust port.

Covers:
- `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.{h,cpp}`
  (header 610 lines, cpp 8486 lines).
- `Source/Reasoner/Kernel/Calculation/*` (18 files, ~1903 lines).

---

## Part 1 — CCalculationTableauApproximationSaturationTaskHandleAlgorithm

### What it is / how it relates to full completion

This class is the **approximate saturation pre-pass**. It runs a *non-branching,
deterministic* tableau-style saturation over a single merged ("approximated")
individual-node model: it applies the tableau expansion rules (AND, OR-as-merge,
SOME, ALL, ATLEAST, ATMOST, VALUE, NOMINAL, SELF, datatype, automaton/chain
transitions, ...) but **never case-splits** — disjunctions are folded into a
common-disjunct over-approximation and successors are merged rather than branched.
It computes, per concept/individual, a saturated label plus *insufficiency /
criticality* flags marking exactly where the cheap over-approximation is unsound
(the spots a real branching completion must revisit). It runs **before** the full
backtracking tableau completion (it is itself a `CTaskHandleAlgorithm` driven by
the same `CTaskProcessorUnit` machinery as the real completion). Its output —
saturated node labels + backend association cache entries + the critical-concept
worklists — **feeds** the consistency/classification phase: nodes proven
saturation-consistent are cached and skipped, and only the flagged-critical
fragment is handed to the complete (branching) algorithm. This is Konclude's
"lazy" cheap-saturation-first design that KM has been trying to replicate
(elc = saturation core, `cert_round` = residue check).

### Method inventory

~195 method definitions in the cpp (248 raw `Class::` token hits incl. the
`TableauRuleFunction` typedef and member refs). The header declares ~200 methods.
Grouped below; line numbers are the **definition start line in the .cpp**, ranges
inferred from the next definition.

#### A. Task entry / lifecycle / config (driver)
| line | method | ~len |
|---|---|---|
| 43 | ctor (rule jump-table setup) | 132 |
| 175 | dtor | 4 |
| 179 | readCalculationConfig | 66 |
| 245 | createCalculationAlgorithmContext | 9 |
| 254 | **handleTask** (main saturation loop driver) | **278** |
| 8025 | writeGeneratedExtendedDebugIndiModelStringList | 29 |

#### B. Main loop / worklist management
hasRemainingProcessingNodes(788), hasRemainingExtensionProcessingNodes(689),
hasRemainingMergingCriticalExtensionProcessingNodes(702),
continueNominalDelayedIndividualNodeProcessing(718),
completeSaturatedIndividualNodes(760), processNextSuccessorExtensions(2646),
addSuccessorExtensionToProcessingQueue(2717), addIndividualToProcessingQueue(7119),
addUninitializedIndividualToProcessingQueue(7127), addIndividualToCompletionQueue(7135),
setDelayedNominalProcessingOccured(6910), setInsufficientNodeOccured(6915),
setProblematicEQCandidateOccured(6920).

#### C. Node initialization
individualNodeInitializing(796), individualNodeConclusion(5709),
initializeInitializationConcepts(5464, **245**),
resolveSpecialInitializationIndividualNode(5424), isProcessingCritical(5403),
countConceptsOfReferredNodes(5369), initializeRoleAssertions(5079),
initializeDataAssertions(5145), createRoleAssertionLink(5024),
createSuccessorForDataLiteral(5174), createSuccessorForConcept(6931, 170),
initializeIndividualNodeByCoping(2022), getCorrectedNode(6461).

#### D. Tableau saturation rules (the calculus rules — 20 apply* + dispatch)
applyTableauSaturationRule(5718, dispatch), applyAutomatChooseRule(5743),
applyNONERule(5983), applyDATATYPERule(5760), applyNotDATATYPERule(5998),
applyDATALITERALRule(5795), applyANDRule(5973), applyORRule(6032),
applySOMERule(6925), applySELFRule(6856), applyALLRule(6154),
applyATMOSTRule(6108), applyATLEASTRule(6132), applyIMPLICATIONRule(5987),
applyEQCANDRule(6145), applyBOTTOMRule(6150), applyVALUERule(6474, 200),
applyNOMINALRule(6731, 118), applyELSERule(6102),
applyBackwardPropagationConcepts(7101). Helpers: getDisjunctCheckingConcept(6006),
addAutomateTransitionOperands(6682), testAutomateTransitionOperandsAddable(6703).

#### E. Datatype / value-space handling
handleDatatypeValueSpaceTriggers(5806), tryHandleDatatypeValueSpaceTriggers(5826),
associateDataLiteralWithNode(5850, 123).

#### F. Successor ALL / FUNCTIONAL extension propagation
getSucessorExtensionData(908), initializeSuccessorALLConceptsExtensions(919),
updateSuccessorRoleALLConceptsExtensions(943 & 1831),
updateSuccessorALLConceptsExtensions(1852), addSuccessorExtensionsALLConcept(2531),
processSuccessorALLConceptsExtensions(2670),
addALLProcessRoleExtensionToDependentIndividuals(2738),
addProcessExtensionToDependentIndividuals(2729),
installSuccessorPredecessorRoleFunctionalityConceptsExtension(1018),
updateSuccessorRoleFUNCTIONALConceptsExtensions(1047 & 1514, 176),
updateSuccessorRoleQualifiedFUNCTIONALConceptsExtensions(1064 & 1690, 141),
updatePredecessorRoleFUNCTIONALConceptsExtensions(1079 & 1113),
processSuccessorFUNCTIONALConceptsExtensions(2557),
addFUNCTIONAL*ToDependentIndividuals (2757/2778/2790/2808),
addALLConceptExtensionProcessingRole(6209),
addFUNCTIONALConceptExtensionProcessingRole(6238),
addNewLinkedExtensionProcessingRole(6271),
addQualifiedFUNCTIONALAtmostConceptExtensionProcessing(6255),
installBackwardPropagationLink(1974), collectLinkedSuccessorNodes(3194),
addLinkedSuccessorNodeForConcept(3250), addLinkedSuccessorNodeForRoleAssertion(3234).

#### G. ATMOST / cardinality merging (the SHIQ-hard core)
createAncestorSuccessorMergingExtension(1202, 133), getInverseRole(1175),
isLinkedIndividualSuccessorNodeMergingSubset(1335 & 1343),
isSuccessorCreationRoleMergingSubset(1370 & 1382),
isIndividualNodeLabelMergingSubset(1393), deactivateSubsetMergeableSuccessorLinks(1421),
collectATMOSTConceptRelevantSuccessors(3779, 190),
tryATMOSTConceptSuccessorMerging(3969), reconnectMergedLinkedSuccessors(4034, 102),
testMergedSuccessorLinkingProblematic(4136),
tryIndividiualATMOSTConceptSuccessorMerging(4250, 217),
isIndividualSuccessorLinkCardinalityMergeable(4467 & 4473),
getSuccessorLinkSimplyMergeableCardinalityCount(4498, 101),
isIndividualSuccessorLinkCardinalityExtendedMergeable(4599 & 4605),
getIndividualNodeQualifiedSuccessorCount(4637),
isIndividualNodeLabelMergingProblematic(4716, 92),
getSuccessorLinkExtendedMergeableCardinalityCount(4808),
markATMOSTRestrictedAncestorsAsInsufficient(2852),
markNominalATMOSTRestrictedAncestorsAsInsufficient(2824).

#### H. Critical-concept detection (insufficiency / unsoundness markers)
hasNextCriticalConcepts(838), checkNextCriticalConcepts(850),
checkCriticalIndividuals(872), checkCriticalConceptsForNode(3002, **192**),
addCriticalConceptDescriptor(3386), addCriticalConceptForDependentNodes(2985),
addCriticalORConceptTestedForDependentNodes(2933),
isCriticalALLConceptDescriptorInsufficient(3462, 120),
isCriticalORConceptDescriptorInsufficient(3582),
isCriticalATMOSTConceptDescriptorInsufficient(3625, 154),
isCriticalVALUEConceptDescriptorInsufficient(4876),
isCriticalNOMINALConceptDescriptorInsufficient(4843),
isCriticalEQCANDConceptDescriptorProblematic(3606),
testInsufficientALLConcepts(3412).

#### I. Disjunct-common-concept extraction (OR over-approximation)
updateExtractDisjunctCommonConcept(4936),
initializeExtractDisjunctCommonConcept(4970),
addDisjunctCommonConceptExtractionToProcessingQueue(5009).

#### J. Node-extension resolve / copy-on-write (substitution machinery)
getResolvedIndividualNodeAssertion(2258),
getResolvedIndividualNodeRepresentativeAssertion(2186),
getResolvedIndividualNodeRepresentativeRangeAssertion(2088),
createResolvedIndividualNode(2342), preprocessResolvedIndividualNode(2070),
getResolvedIndividualNodeExtensionSuccessor(2297),
getResolvedNeighbourIndividualNodeExtension(2497),
getResolvedIndividualNodeExtension(2401/2405/2443/2449/2512, 5 overloads),
collectResolveIndividualExtendableConceptMap(2371),
getSeparatedSaturationConceptAssertionResolveNode(5270),
getIndividualNodeForConcept(5301), getIndividualNodeForIndividual(5336),
getSaturationIDForIndividualNode(5319).

#### K. Concept-add / label mutation
addConceptsFilteredToIndividual(7145/7155/7165/7175, 4 overloads),
addConceptFilteredToIndividual(7186/7192/7200, 3 overloads),
addConceptToIndividual(7228), insertConceptToIndividualConceptSet(7424, 116),
processModificationUpdateLinkers(7540),
updateImplicationReapplyConceptSaturationDescriptor(7552), hasConceptLocalImpact(7579).

#### L. Status-flag propagation + nominal/cardinality candidate tracking
updateDirectAddingIndividualStatusFlags(7626 & 7653),
updateDirectNotDependentAddingIndividualStatusFlags(7633 & 7685),
updateIndirectAddingIndividualStatusFlags(7721, 75),
requiresDirect/IndirectAddingIndividualStatusFlagsUpdate(7640/7647),
addNominalDependentIndividualNode(6431), addInfluencedNominal(6444),
delayNominalSaturationConceptProcessing(6674),
propagateUnloadedABoxCompletionGraphDependentIndividualNodeFlag(6849),
requiresAddingSuccessorConnectedNominals(7796),
updateAddingSuccessorConnectedNominal(7809 & 7819),
requiresMaxCardinalityCandidatePropagation(7897),
updateMaxCardinalityCandidates(7907).

#### M. Allocation pool helpers (object reuse)
create/release ConceptSaturationDescriptor(7291/7302),
ConceptSaturationProcessLinker(7330/7308), RoleSaturationProcessLinker(7320/7314),
IndividualSaturationNodeLinker(7348/7358),
IndividualSaturationSuccessorLinkDataLinker(7368/7378),
IndividualSaturationUpdateLinker(7392/7402), createModifiedProcessUpdateLinker(7409),
createImplicationReapplyConceptSaturationDescriptor(7415).

#### N. Caching / consistency-model hand-off
tryAssociateIndividualNodesWithBackendCache(615),
loadConsistenceModelData(6362), loadConsistenceRepresentativeData(6403),
isConsistenceDataAvailable(6421) — interface to
`CSaturationNodeBackendAssociationCacheHandler` (`mBackendAssCaceHandler`).

#### O. Statistics / debug (port-optional / drop)
writeIndividualSaturationStatistics(532), testInsufficientIndividuls(591),
testRelevantConceptRoleRatio(632), getApplied*RuleCount (7993-8017),
generateExtendedDebugIndiModelStringList(8054, **279**),
generateDebugIndiModelStringList(8394), generateStatusFlagsStringList(8333),
getDebugIndividualConceptName(8380), testDebugSaturationTaskContainsConcept(s)(8439/8456).

### 3 largest methods
1. `generateExtendedDebugIndiModelStringList` — lines 8054–8333 (~279). Debug-only.
2. `handleTask` — lines 254–532 (~278). The main saturation loop / task driver.
3. `initializeInitializationConcepts` — lines 5464–5709 (~245). Seeds the start node label.

(runners-up: `handleTask`-adjacent `checkCriticalConceptsForNode` ~192,
`createSuccessorForConcept` ~170, `tryIndividiualATMOSTConceptSuccessorMerging` ~217.)

### Proposed port units (~11, each <~800 src lines)

1. **PU-SAT-1 Driver + config + lifecycle** (~430 lc): ctor rule jump-table,
   readCalculationConfig, createCalculationAlgorithmContext, handleTask, the
   has*/complete*/continue* loop predicates, addIndividualTo*Queue,
   set*Occured flags. (group A + B)
2. **PU-SAT-2 Node initialization** (group C, ~700 lc): individualNodeInitializing,
   initializeInitializationConcepts (245), resolve/count/critical-init,
   role+data assertion init, createSuccessorForConcept, initializeIndividualNodeByCoping.
3. **PU-SAT-3 Tableau rules core** (group D non-cardinality: AND/OR/SOME/SELF/
   IMPLICATION/NONE/BOTTOM/EQCAND/ELSE + dispatch + automaton transitions, ~500 lc).
4. **PU-SAT-4 ALL + ATMOST/ATLEAST rules + VALUE/NOMINAL rules** (~520 lc):
   applyALLRule, applyATMOST/ATLEASTRule, applyVALUERule (200), applyNOMINALRule (118).
5. **PU-SAT-5 Datatype rules** (group E + DATATYPE/DATALITERAL applies, ~330 lc).
6. **PU-SAT-6 Successor ALL/FUNCTIONAL extension propagation** (group F part 1:
   the update*ALL/FUNCTIONAL* + backward-prop link install, ~700 lc).
7. **PU-SAT-7 Extension processing queue + dependent-individual fan-out**
   (group F part 2: process*Extensions, add*ToDependentIndividuals,
   add*ConceptExtensionProcessingRole, collectLinkedSuccessorNodes, ~600 lc).
8. **PU-SAT-8 ATMOST cardinality merging** (group G, ~780 lc).
9. **PU-SAT-9 Critical-concept / insufficiency detection** (group H + I, ~700 lc).
10. **PU-SAT-10 Node-extension resolve / copy-on-write** (group J, ~600 lc).
11. **PU-SAT-11 Label mutation + status-flag + nominal/card propagation + pools
    + cache hand-off** (groups K + L + M + N, ~700 lc).
12. **PU-SAT-DBG (optional/drop)** Statistics + debug string generation (group O).

---

## Part 2 — Calculation/ controllers (18 files, ~1903 lines)

| file | lines | purpose |
|---|---|---|
| CCalculationManager.h | 104 | Abstract manager interface: `calculateJob(s)`, `calculateTask`, `initializeManager`, statistics. |
| CCalculationManager.cpp | 56 | Default impls (calculateJobs loop). |
| CConcurrentTaskCalculationManager.h | 110 | **Entry-point controller** (concrete manager). |
| CConcurrentTaskCalculationManager.cpp | 161 | Drives calculation: posts tasks to the scheduler thread, collects stats. |
| CConcurrentTaskCalculationEnvironment.h | 153 | Holds the processor-unit/thread pool + callback executer + status propagator. |
| CConcurrentTaskCalculationEnvironment.cpp | 324 | init single/multi task processors, append worker threads, aggregate per-thread stats. |
| CCalculationEnviroment.h | 89 | Abstract environment base. |
| CCalculationEnviroment.cpp | 47 | Trivial base impl. |
| CCalculationEnvironmentFactory.h | 91 | Abstract env factory: `createCalculationContext(configProvider)`. |
| CCalculationEnvironmentFactory.cpp | 47 | Base impl. |
| CConfigDependedCalculationEnvironmentFactory.h | 103 | Concrete env factory holding a `CTaskHandleAlgorithmBuilder`. |
| CConfigDependedCalculationEnvironmentFactory.cpp | 149 | **Wires the threading model** — reads ProcessorCount/Memory config, builds the thread pool, installs a fresh task-handle-algorithm per thread. |
| CCalculationFactory.h | 92 | Abstract factory: create/initialize a `CCalculationManager`. |
| CCalculationFactory.cpp | 47 | Base impl. |
| CConfigDependedCalculationFactory.h | 100 | Concrete factory holding a `CTaskHandleAlgorithmBuilder`. |
| CConfigDependedCalculationFactory.cpp | 91 | Creates `CConcurrentTaskCalculationManager` + env factory from config. |
| CTaskHandleAlgorithmBuilder.h | 92 | Abstract builder: `createTaskHandleAlgorithm()` — the seam that yields a tableau-completion or saturation `CTaskHandleAlgorithm` per worker thread. |
| CTaskHandleAlgorithmBuilder.cpp | 47 | Base impl. |

### Entry point and control flow into the completion algorithm

**Entry-point class: `CConcurrentTaskCalculationManager`** (the concrete
`CCalculationManager`). Flow:

1. `CConfigDependedCalculationFactory::createCalculationManager(config)` →
   `new CConcurrentTaskCalculationManager`, then `initializeManager(...)` is
   handed a `CConfigDependedCalculationEnvironmentFactory` (constructed with a
   `CTaskHandleAlgorithmBuilder` — the builder that produces the completion /
   saturation `CTaskHandleAlgorithm`, e.g. `CCalculationTableauApproximation...`
   or the full tableau handler).
2. `CConcurrentTaskCalculationManager::initializeManager` calls the env factory's
   `createCalculationContext(configProvider)` →
   `CConfigDependedCalculationEnvironmentFactory::createCalculationContext`
   (cpp lines 42–148). This reads `Konclude.Calculation.ProcessorCount`
   (`AUTO` ⇒ `CThread::idealThreadCount()`) and `Konclude.Calculation.Memory`,
   then builds a `CConcurrentTaskCalculationEnvironment`:
   - **single-thread** (`count<=1`): one `CSingleThreadTaskProcessorUnit(taskHandleAlg, memPoolProvider)`.
   - **multi-thread**: a `CTaskProcessorSchedulerThread` + `CTaskProcessorCompletorThread`,
     then `count-2` `CTaskProcessorThread` workers — **each gets its own freshly
     built `CTaskHandleAlgorithm` (`mTaskHandleAlgBuilder->createTaskHandleAlgorithm()`)
     and its own `CNewCentralizedLimitedAllocationMemoryPoolProvider`** (per-thread
     memory pool bounded by a shared `CCentralizedAllocationConfigProvidedDependendLimitation`).
     Workers `installScheduler/installCallbackExecuter/installStatusPropagator`
     then `startProcessing()`.
3. Per job: `calculateJob` → `calculateTask(CSatisfiableCalculationTask*)`, which
   `CTaskEventCommunicator::postSendTaskScheduleEvent(...)` posts the task to the
   scheduler unit's event handler. A worker thread picks it up and invokes its
   `CTaskHandleAlgorithm::handleTask(processorContext, task)` — i.e. the
   saturation pre-pass's `handleTask` (cpp:254) or the full completion handler.

**Threading / task model:** event-driven `CTask` work items dispatched by a
`Scheduler` (`Scheduler::CTask`, `CTaskHandleAlgorithm`, `CTaskProcessor*Thread`).
One scheduler thread + one completor thread + N worker threads; **each thread owns
a private TaskHandleAlgorithm instance and a private centralized-but-limited memory
pool** (no shared mutable calc state across threads — parallelism is over
independent satisfiability tasks, contexts allocated from per-thread pools).
The `CTaskHandleAlgorithmBuilder` is the injection seam selecting which algorithm
(approximate saturation vs full tableau completion) the threads run.
