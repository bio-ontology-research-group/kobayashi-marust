# Konclude `CCalculationTableauCompletionTaskHandleAlgorithm` — Completion method catalogue

Source (READ-ONLY): `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.{h,cpp}`
Header: 1606 lines. CPP: 27686 lines. **554 method definitions** (518 unique names, 25 overloaded), totalling 24882 lines of bodies.

All line numbers are 1-based ranges in the `.cpp`. `L` = body line count (def line .. matching 4-tab `}` ).

Class qualifier `CCalculationTableauCompletionTaskHandleAlgorithm::` stripped from signatures for brevity.

## Family summary

| Family | methods | body lines |
|---|---:|---:|
| Core processing loop / driver | 37 | 2734 |
| Expansion rules (apply*Rule, Automat*, ORBranching) | 51 | 3656 |
| Reapply-queue management | 20 | 376 |
| Rule counters / statistics | 7 | 21 |
| Variable-binding / binding-propagation rules | 11 | 438 |
| Merge handling | 34 | 2787 |
| Nominal handling | 25 | 890 |
| Datatype / value-space / literal handling | 12 | 487 |
| Blocking (pairwise / label-optimized / dynamic) | 55 | 2246 |
| Caching / backend-cache / saturation | 67 | 3587 |
| Incremental expansion / compatibility | 20 | 651 |
| Neighbour / backend-cache node expansion | 12 | 611 |
| Dependency tracking | 70 | 926 |
| Backtracking | 11 | 698 |
| Clash processing | 18 | 475 |
| Generic helpers / accessors / label tests | 104 | 4299 |
| **TOTAL** | **554** | **24882** |

## Methods by family

### CORE PROCESSING LOOP — Core processing loop / driver  (37 methods, 2734 lines)

| L | range | signature |
|---:|---|---|
| 7 | 848-854 | `CCalculationAlgorithmContextBase* createCalculationAlgorithmContext(CTaskProcessorContext *processorContext, CProcessContext* processContext, CSatisfiableCalculationTask* satCalcTask)` |
| 800 | 858-1657 | `bool handleTask(CTaskProcessorContext *processorContext, CTask* task)` |
| 21 | 2074-2094 | `bool continueIndividualProcessing(CIndividualProcessNode*& indiProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 601 | 2190-2790 | `CIndividualProcessNode* takeNextProcessIndividual(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 32 | 2794-2825 | `void analyzeCompletionGraphStatistics(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 319 | 8720-9038 | `bool initialNodeInitialize(CIndividualProcessNode*& indiProcNode, bool allowPreprocess, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 109 | 9061-9169 | `bool individualNodeInitializing(CIndividualProcessNode*& indiProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 9480-9494 | `void individualNodeConclusion(CIndividualProcessNode*& indiProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 24 | 9496-9519 | `bool tableauRuleProcessing(CIndividualProcessNode*& indiProcNode,CConceptProcessDescriptor*& conProcDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 28 | 9522-9549 | `void tableauRuleChoice(CIndividualProcessNode*& indiProcNode,CConceptProcessDescriptor*& conProcDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 35 | 16396-16430 | `bool initializeORProcessing(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CBranchingORProcessingRestrictionSpecification** plannedBranchingProcessRestriction, CCalculationAlgorithmContextBase* ...` |
| 172 | 16493-16664 | `bool planORProcessing(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CBranchingORProcessingRestrictionSpecification** plannedBranchingProcessRestriction, CCalculationAlgorithmContextBase* calcAl...` |
| 3 | 17201-17203 | `void prepareBranchedTaskProcessing(CIndividualProcessNode*& individual, CSatisfiableCalculationTask* newTask, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 17286-17294 | `CIndividualLinkEdge* getLinkProcessingRestriction(CConceptProcessDescriptor*& conProDes)` |
| 3 | 19762-19764 | `void propagateProcessingRestrictionToAncestor(CIndividualProcessNode*& indi, cint64 addRestrictionFlags, bool recursive, cint64 whileNotContainsFlags, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 19767-19778 | `void propagateAddingProcessingRestrictionToAncestor(CIndividualProcessNode*& indi, cint64 addRestrictionFlags, bool recursive, cint64 whileNotContainsFlags, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 19783-19785 | `void propagateProcessingRestrictionToSuccessors(CIndividualProcessNode*& indi, cint64 addRestrictionFlags, bool recursive, cint64 whileNotContainsFlags, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 19810-19827 | `void propagateAddingProcessingRestrictionToSuccessors(CIndividualProcessNode*& indi, cint64 addRestrictionFlags, bool recursive, cint64 whileNotContainsFlags, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 19831-19848 | `void propagateClearingProcessingRestrictionToSuccessors(CIndividualProcessNode*& indi, cint64 clearRestrictionFlags, bool recursive, cint64 whileContainsFlags, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 13 | 19887-19899 | `void propagateIndividualProcessedAndReactivate(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 56 | 19901-19956 | `void searchReactivateIndividualsProcessedPropagated(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 19958-19964 | `void propagateIndividualUnprocessed(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 25 | 19968-19992 | `void propagateIndividualUnprocessed(CIndividualProcessNode*& indi, bool requiresConsFlag, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 31 | 26692-26722 | `void addConceptToIndividualSkipANDProcessing(CConcept* addingConcept, bool negate, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, bool allowPreprocessing, bool allowInitalization, bool markModification...` |
| 13 | 27152-27164 | `void insertConceptProcessDescriptorToProcessingQueue(CConceptProcessDescriptor* conProDes, CConceptProcessingQueue*& conceptProcessingQueue, CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 17 | 27166-27182 | `void insertConceptProcessDescriptorToProcessingQueue(CConceptProcessDescriptor* conProDes, CConceptProcessingQueue*& conceptProcessingQueue, cint64 bindingCount, CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* cal...` |
| 16 | 27185-27200 | `void addConceptToProcessingQueue(CConceptDescriptor *conceptDescriptor, CDependencyTrackPoint* depTrackPoint, CConceptProcessingQueue*& conceptProcessingQueue, CIndividualProcessNode*& processIndi, bool reapplied, CCalculationAlgorithmCo...` |
| 11 | 27203-27213 | `bool needsProcessingForConcept(CConceptDescriptor *conceptDescriptor, CDependencyTrackPoint* depTrackPoint, CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 27216-27225 | `void addConceptPreprocessedToProcessingQueue(CConceptDescriptor *conceptDescriptor, CDependencyTrackPoint* depTrackPoint, CConceptProcessingQueue*& conceptProcessingQueue, CIndividualProcessNode*& processIndi, cint64 bindingCount, CCalcu...` |
| 46 | 27228-27273 | `void addConceptPreprocessedToProcessingQueue(CConceptDescriptor *conceptDescriptor, CDependencyTrackPoint* depTrackPoint, CConceptProcessingQueue*& conceptProcessingQueue, CIndividualProcessNode*& processIndi, bool allowPreprocessing, CC...` |
| 4 | 27278-27281 | `void addConceptToProcessingQueue(CConceptProcessDescriptor* reinsertConProDes, CConceptProcessingQueue*& conceptProcessingQueue, CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 24 | 27284-27307 | `void addCopiedConceptToProcessingQueue(CConceptProcessDescriptor* copyConProDes, CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 27311-27322 | `void addConceptRestrictedToProcessingQueue(CConceptDescriptor *conceptDescriptor, CDependencyTrackPoint* depTrackPoint, CConceptProcessingQueue*& conceptProcessingQueue, CIndividualProcessNode*& processIndi, bool reapplied, CProcessingRe...` |
| 17 | 27325-27341 | `void addConceptRestrictedToProcessingQueue(CConceptDescriptor *conceptDescriptor, CDependencyTrackPoint* depTrackPoint, CConceptProcessingQueue*& conceptProcessingQueue, CIndividualProcessNode*& processIndi, bool reapplied, CProcessingRe...` |
| 12 | 27345-27356 | `void addConceptRestrictedFixedPriorityToProcessingQueue(CConceptDescriptor *conceptDescriptor, CDependencyTrackPoint* depTrackPoint, CConceptProcessingQueue*& conceptProcessingQueue, CIndividualProcessNode*& processIndi, bool reapplied, ...` |
| 58 | 27359-27416 | `bool addIndividualToProcessingQueueBasedOnProcessingConcepts(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 133 | 27419-27551 | `bool addIndividualToProcessingQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |

### EXPANSION RULES (APPLY*RULE) — Expansion rules (apply*Rule, Automat*, ORBranching)  (51 methods, 3656 lines)

| L | range | signature |
|---:|---|---|
| 3 | 9552-9554 | `void applyNegAutomatChooseRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 9556-9558 | `void applyNegANDRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 9560-9562 | `void applyNegSOMERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 9564-9566 | `void applyNegALLRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 9568-9570 | `void applyNegORRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 9573-9575 | `void applyNegATMOSTRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 9577-9579 | `void applyNegATLEASTRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 21 | 9583-9603 | `void applyAutomatChooseRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 8 | 9606-9613 | `void applyAutomatANDRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 119 | 9634-9752 | `void applyAutomatTransactions(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, CConcept* concept, bool negated, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 55 | 10310-10364 | `void applyREPRESENTATIVEGROUNDINGRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 249 | 10366-10614 | `void applyREPRESENTATIVEJOINRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 121 | 10803-10923 | `void applyREPRESENTATIVEBINDVARIABLERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 121 | 10927-11047 | `void applyREPRESENTATIVEIMPLICATIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 37 | 11121-11157 | `void applyREPRESENTATIVEALLRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 72 | 11161-11232 | `void applyREPRESENTATIVEANDRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 65 | 11514-11578 | `void applyVARIABLEBINDINGANDRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 37 | 11833-11869 | `void applyVARBINDPROPAGATEALLRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 125 | 11874-11998 | `void applyVARBINDVARIABLERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 219 | 12002-12220 | `void applyVARBINDPROPAGATEJOINRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 61 | 12418-12478 | `void applyVARBINDPROPAGATEGROUNDINGRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 106 | 12481-12586 | `void applyVARBINDPROPAGATEIMPLICATIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 83 | 12593-12675 | `void applyVARBINDPREPARERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 45 | 12681-12725 | `void applyVARBINDFINALIZERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 213 | 12828-13040 | `void applyBINDPROPAGATEGROUNDINGRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 241 | 13048-13288 | `void applyBINDPROPAGATECYCLERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 37 | 13467-13503 | `void applyBINDPROPAGATEALLRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 101 | 13510-13610 | `void applyBINDPROPAGATEIMPLICATIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 13614-13616 | `void applyBINDPROPAGATEANDRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 13620-13623 | `void applyBINDPROPAGATEANDFLAGALLRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 76 | 13694-13769 | `void applyBINDVARIABLERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 23 | 14009-14031 | `void applyDATATYPERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 17 | 14037-14053 | `void applyDATARESTRICTIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 14058-14077 | `void applyDATALITERALRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 14082-14097 | `void applyDATALITERALIMPLICATIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 14102-14117 | `void applyDATATYPEIMPLICATIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 13 | 14123-14135 | `void applyDATARESTRICTIONIMPLICATIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 14138-14152 | `void applyBOTTOMRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 14156-14171 | `void applyANDRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 188 | 14215-14402 | `void applySOMERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 78 | 14608-14685 | `void applyVALUERule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 132 | 14689-14820 | `void applyFUNCTIONALRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 146 | 14861-15006 | `void applyATMOSTRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 86 | 16068-16153 | `void applyATLEASTRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 98 | 16162-16259 | `void applyNOMINALRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 95 | 16299-16393 | `void applyALLRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 270 | 16741-17010 | `void executeORBranching(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CBranchingORProcessingRestrictionSpecification* plannedBranchingProcessRestriction, CCalculationAlgorithmContextBase* calcA...` |
| 31 | 17022-17052 | `void applyORRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 67 | 17056-17122 | `void applyIMPLICATIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 48 | 17130-17177 | `void applyNOMINALIMPLICATIONRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 41 | 17243-17283 | `void applySELFRule(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |

### REAPPLY-QUEUE MANAGEMENT — Reapply-queue management  (20 methods, 376 lines)

| L | range | signature |
|---:|---|---|
| 21 | 6252-6272 | `bool reapplySatisfiableCachedAbsorbedDisjunctionConcepts(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 6275-6294 | `bool reapplySatisfiableCachedAbsorbedGeneratingConcepts(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 11236-11245 | `void reapplyConceptUpdatedRepresentative(CIndividualProcessNode*& processIndi, CConceptDescriptor* bindingConDes, CDependencyTrackPoint* bindingDepTrackPoint, CReapplyConceptLabelSet* conSet, CCondensedReapplyQueue* reapplyQueue, CCalcul...` |
| 10 | 11248-11257 | `void reapplyConceptUpdatedRepresentative(CIndividualProcessNode*& processIndi, CConceptDescriptor* bindingConDes, CDependencyTrackPoint* bindingDepTrackPoint, cint64 bindingCount, CReapplyConceptLabelSet* conSet, CCondensedReapplyQueue* ...` |
| 22 | 13876-13897 | `void applyReapplyQueueConcepts(CIndividualProcessNode*& processIndi, CPropagationBindingReapplyConceptDescriptor* reapplyDesLinker, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 31 | 22019-22049 | `void collectReapplyAutomatTransactionsRestrictions(CIndividualProcessNode*& processIndi, CRole* collectingRole, CConcept* concept, bool negated, CPROCESSINGHASH<cint64, CConceptNegationPair>*& conExtensionMap, CReapplyConceptSaturationLa...` |
| 58 | 22295-22352 | `CIndividualLinkEdge* createNewIndividualsLinksReapplyed(CIndividualProcessNode*& indiSource, CIndividualProcessNode*& indiDestination, CSortedNegLinker<CRole*>* roleLinkerIt, CRole* ancRole, CDependencyTrackPoint* depTrackPoint, bool che...` |
| 27 | 22372-22398 | `CIndividualLinkEdge* createNewIndividualsLinkReapplyed(CIndividualProcessNode*& indiCreator, CIndividualProcessNode*& indiSource, CIndividualProcessNode*& indiDestination, CRole* role, CDependencyTrackPoint* depTrackPoint, CCalculationAl...` |
| 28 | 26492-26519 | `void applyExtendedReapplyConceptDescriptor(CIndividualProcessNode*& processIndi, CConcept* concept, bool negation, CCondensedReapplyConceptDescriptor* reapplyConceptDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 25 | 26523-26547 | `void applyReapplyQueueConcepts(CIndividualProcessNode*& processIndi, CConcept* concept, bool negation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 21 | 26549-26569 | `void applyReapplyQueueConcepts(CIndividualProcessNode*& processIndi, CRole* role, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 28 | 26572-26599 | `void applyReapplyQueueConceptsRestricted(CIndividualProcessNode*& processIndi, CReapplyQueueIterator* reapplyQueueIt, CIndividualLinkEdge* restrictedLink, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 26602-26621 | `void applyReapplyQueueConcepts(CIndividualProcessNode*& processIndi, CCondensedReapplyQueueIterator* reapplyQueueIt, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 5 | 26625-26629 | `void addConceptToReapplyQueue(CConceptDescriptor *conceptDescriptor, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 26632-26640 | `void addConceptToReapplyQueue(CConceptDescriptor *conceptDescriptor, CRole* role, CIndividualProcessNode*& processIndi, bool isStaticDes, CDependencyTrackPoint* dependencyTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 26642-26650 | `void addConceptToReapplyQueue(CConceptDescriptor *conceptDescriptor, CConcept* concept, bool negation, CIndividualProcessNode*& processIndi, bool isStaticDes, CDependencyTrackPoint* dependencyTrackPoint, CCalculationAlgorithmContextBase*...` |
| 9 | 26653-26661 | `void addConceptToReapplyQueue(CConceptDescriptor *conceptDescriptor, CRole* role, CIndividualProcessNode*& processIndi, CProcessingRestrictionSpecification* procRest, CDependencyTrackPoint* dependencyTrackPoint, CCalculationAlgorithmCont...` |
| 9 | 26663-26671 | `void addConceptToReapplyQueue(CConceptDescriptor *conceptDescriptor, CConcept* concept, bool negation, CIndividualProcessNode*& processIndi, CProcessingRestrictionSpecification* procRest, CDependencyTrackPoint* dependencyTrackPoint, CCal...` |
| 7 | 26674-26680 | `bool isConceptInReapplyQueue(CConceptDescriptor* conceptDescriptor, CConcept* concept, bool negation, CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 26682-26688 | `bool isConceptInReapplyQueue(CConceptDescriptor* conceptDescriptor, CRole* role, CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |

### RULE COUNTERS/STATS — Rule counters / statistics  (7 methods, 21 lines)

| L | range | signature |
|---:|---|---|
| 3 | 27650-27652 | `cint64 getAppliedANDRuleCount()` |
| 3 | 27654-27656 | `cint64 getAppliedORRuleCount()` |
| 3 | 27658-27660 | `cint64 getAppliedSOMERuleCount()` |
| 3 | 27662-27664 | `cint64 getAppliedATLEASTRuleCount()` |
| 3 | 27666-27668 | `cint64 getAppliedALLRuleCount()` |
| 3 | 27670-27672 | `cint64 getAppliedATMOSTRuleCount()` |
| 3 | 27674-27676 | `cint64 getAppliedTotalRuleCount()` |

### VARIABLE-BINDING/PROPAGATION RULES — Variable-binding / binding-propagation rules  (11 methods, 438 lines)

| L | range | signature |
|---:|---|---|
| 31 | 10617-10647 | `bool hasCommonVariableBindings(CIndividualProcessNode*& processIndi, CRepresentativeVariableBindingPathMap* leftRepVarBindMap, CRepresentativeVariableBindingPathMap* rightRepVarBindMap, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 11581-11609 | `bool propagateInitialVariableBindings(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CVariableBindingPathSet* newVarBindingSet, CVariableBindingPathSet* prevVarBindingSet, CDependency* otherDependencies, CConceptVariab...` |
| 55 | 11612-11666 | `bool propagateFreshVariableBindings(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CVariableBindingPathSet* newVarBindingSet, CVariableBindingPathSet* prevVarBindingSet, CDependency* otherDependencies, CConceptVariable...` |
| 64 | 11671-11734 | `void propagateVariableBindingsToSuccessor(CIndividualProcessNode* processIndi, CIndividualProcessNode*& succIndi, CSortedNegLinker<CConcept*>* conceptOpLinker, bool negate, CConceptDescriptor* conDes, CIndividualLinkEdge* restLink, CCalc...` |
| 29 | 11741-11769 | `bool propagateInitialVariableBindingsToSuccessor(CIndividualProcessNode*& processIndi, CIndividualProcessNode* succIndi, CConceptDescriptor* conDes, CVariableBindingPathSet* newVarBindingPathSet, CVariableBindingPathSet* prevVarBindingPa...` |
| 57 | 11774-11830 | `bool propagateFreshVariableBindingsToSuccessor(CIndividualProcessNode*& processIndi, CIndividualProcessNode* succIndi, CConceptDescriptor* conDes, CVariableBindingPathSet* newVarBindingPathSet, CVariableBindingPathSet* prevVarBindingPath...` |
| 60 | 12226-12285 | `bool propagateVariableBindingsJoins(CIndividualProcessNode* processIndi, CConceptDescriptor* joiningConDes, CConcept* joinConcept, CVariableBindingPathDescriptor* varBindPathDes, bool leftTriggerPath, CVariableBindingPathJoiningHash* var...` |
| 27 | 12291-12317 | `CVariableBindingDescriptor* createVariableBindingPathKey(CIndividualProcessNode* processIndi, CSortedLinker<CVariable*>* varLinker, CVariableBindingDescriptor* varBindDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 12321-12336 | `bool triggerVariableBindingPathJoining(CIndividualProcessNode* processIndi, CVariableBindingPathDescriptor* varBindPathDes, CVariableBindingDescriptor* varBindDes, bool leftTriggered, CVariableBindingTriggerHash* varBindTriggerHash, CCal...` |
| 9 | 12341-12349 | `void forceVariableBindingJoinCreated(CIndividualProcessNode* processIndi, CConceptDescriptor* joiningConDes, CConcept* joinConcept, CConceptDescriptor*& joinConDes, CDependencyTrackPoint* mergedDependencyTrackPoint, CVariableBindingPathS...` |
| 61 | 12353-12413 | `CVariableBindingPath* getJoinedVariableBindingPath(CVariableBindingPath* leftVarBindPath, CVariableBindingPath* rightVarBindPath, CCalculationAlgorithmContextBase* calcAlgContext)` |

### MERGE HANDLING — Merge handling  (34 methods, 2787 lines)

| L | range | signature |
|---:|---|---|
| 15 | 1686-1700 | `bool findNextPossibleInstanceMergingIndividual(CIndividualProcessNode* processIndi, CPossibleInstancesIndividualsMergingData* possInstanceMergingData, CCalculationAlgorithmContextBase* calcAlgContext, CPROCESSHASH<CBackendRepresentativeM...` |
| 175 | 1704-1878 | `bool findNextPossibleInstanceMergingIndividual(CIndividualProcessNode* processIndi, CPossibleInstancesIndividualsMergingData* possInstanceMergingData, CCalculationAlgorithmContextBase* calcAlgContext, CPROCESSHASH<CBackendRepresentativeM...` |
| 139 | 1885-2023 | `bool tryPossibleInstanceMerging(CIndividualProcessNode* processIndi, CPossibleInstancesIndividualsMergingData* possInstanceMergingData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 141 | 3102-3242 | `bool incrementalMergeWithPreviousNondeterministicCompletionGraph(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 123 | 3250-3372 | `bool incrementalMergeWithPreviousDeterministicCompletionGraph(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10057-10063 | `CMERGEDCONCEPTDependencyNode* createMERGEDCONCEPTDependency(CDependencyTrackPoint*& mergedConceptContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* mergePrevDepTrackPoint, CDep...` |
| 7 | 10065-10071 | `CMERGEDLINKDependencyNode* createMERGEDLINKDependency(CDependencyTrackPoint*& mergedLinkContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* mergePrevDepTrackPoint, CDependencyTrackPoint* linkPrevDepTrackPo...` |
| 7 | 10074-10080 | `CMERGEDIndividualDependencyNode* createMERGEDINDIVIDUALDependency(CDependencyTrackPoint*& mergedIndividualContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* mergePrevDepTrackPoint, CDependencyTrackPoint* ...` |
| 7 | 10131-10137 | `CMERGEDependencyNode* createMERGEDependency(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10157-10163 | `CMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode* createMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode(CIndividualProcessNode*& processIndi, CDependencyTrackPoint* prevDepTrackPoint, CIndividualProcessNode* mergingIndi, CCalculationAlgorith...` |
| 7 | 10219-10225 | `CSAMEINDIVIDUALSMERGEDependencyNode* createSAMEINDIVIDUALMERGEDependency(CDependencyTrackPoint*& expContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPoint* prevOtherDe...` |
| 32 | 15009-15040 | `QString generateDebugMergingQueueString(CBranchingMergingProcessingRestrictionSpecification* branchingMergingProcRest, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 50 | 15044-15093 | `bool mergeMergingIndividualNodesPairwise(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, cint64 linkCount, cint64 cardinality, CBranchingMergingProcessingRestrictionSpecification* branchingMergingProcRest, CC...` |
| 430 | 15097-15526 | `bool mergeMergingIndividualNodes(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, cint64 linkCount, cint64 cardinality, CBranchingMergingProcessingRestrictionSpecification* branchingMergingProcRest, CCalculati...` |
| 63 | 15611-15673 | `CSatisfiableCalculationTask* createMergeBranchingTask(CIndividualProcessNode*& processIndiNode, CConceptProcessDescriptor*& conProDes, CIndividualProcessNode*& distinctIndiNode, CIndividualProcessNode*& mergingIndiNode, CNonDeterministic...` |
| 140 | 15677-15816 | `bool qualifyMergingIndividualNodes(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, CBranchingMergingProcessingRestrictionSpecification* branchingMergingProcRest, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 244 | 15820-16063 | `void initializeMergingIndividualNodes(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, CRoleSuccessorLinkIterator* roleSuccIt, CIndividualLinkEdge* usingLastLink, CSortedNegLinker<CConcept*>* conceptOpLinkerIt...` |
| 7 | 16264-16270 | `CIndividualProcessNode* getCorrectedMergedIntoIndividualNode(CIndividualProcessNode* indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 24 | 16690-16713 | `CClashedDependencyDescriptor* createIndividualMergeCausingDescriptors(CClashedDependencyDescriptor* prevClashes, CIndividualProcessNode*& processIndi, CIndividualLinkEdge* link, CSortedNegLinker<CConcept*>* conceptAddLinker, CCalculation...` |
| 159 | 20481-20639 | `bool isIndividualNodesMergeableWithoutNewRuleApplications(CIndividualProcessNode* mergeIntoIndi1, CIndividualProcessNode* indi2, bool* mergingPossiblyRequiresRuleApplications, bool cancelOnPossiblyNewRuleApplications, CCalculationAlgorit...` |
| 8 | 20644-20651 | `bool expandBackendCacheIndividualNodesNominalMerging(CIndividualProcessNode* indi1, CIndividualProcessNode* indi2, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 56 | 20655-20710 | `bool expandBackendCacheIndividualNodesNominalMergingNeighbouringConnections(CIndividualProcessNode* indi1, CIndividualProcessNode* indi2, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 38 | 20714-20751 | `bool isIndividualNodesMergeable(CIndividualProcessNode* indi1, CIndividualProcessNode* indi2, CClashedDependencyDescriptor*& clashDescriptors, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 11 | 20754-20764 | `bool areIndividualNodesDisjointRolesMergeable(CIndividualProcessNode* indi1, CIndividualProcessNode* indi2, CClashedDependencyDescriptor*& clashDescriptors, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 97 | 20767-20863 | `bool isIndividualNodeDisjointRolesMergeable(CIndividualProcessNode* indi1, CIndividualProcessNode* indi2, CClashedDependencyDescriptor*& clashDescriptors, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 50 | 20936-20985 | `CIndividualProcessNode* getMergedIndividualNodes(CIndividualProcessNode*& preferedMergeIntoIndividualNode, CIndividualProcessNode*& individual2, CDependencyTrackPoint* mergeDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 17 | 20990-21006 | `CIndividualProcessNode* getIntoEmptyMergedIndividualNode(CIndividualProcessNode*& mergingIndividualNode, bool createAsNominal, CIndividualProcessNode* mergerNode, CDependencyTrackPoint* mergeDepTrackPoint, CCalculationAlgorithmContextBas...` |
| 553 | 21010-21562 | `void mergeIndividualNodeInto(CIndividualProcessNode*& mergeIntoIndividualNode, CIndividualProcessNode*& individual, CDependencyTrackPoint* mergeDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 48 | 23036-23083 | `bool visitIndividualsRelevantMergingsBackendSynchronisationDataIndividuals(CIndividualProcessNode* indiNode, CXLinker<cint64>* mergedIndiLinker, CXLinker<cint64>* lastProcessedMergedIndiLinker, bool localize, function<bool(CIndividualPro...` |
| 22 | 23089-23110 | `bool visitNewlyMergedIndividualsBackendSynchronisationData(CIndividualProcessNode* indiNode, CPROCESSHASH<CIndividualProcessNode*, CDependencyTrackPoint*>* newIndiMergedHash, bool visitBaseIndividual, function<bool(CIndividualProcessNode...` |
| 25 | 23118-23142 | `bool visitNewlyMergedIndividualsBackendSynchronisationData(CIndividualProcessNode* indiNode, CXLinker<CIndividualProcessNode*>* newIndiMergedLinker, CXLinker<CIndividualProcessNode*>* prevIndiMergedLinker, bool visitBaseIndividual, funct...` |
| 12 | 23144-23155 | `bool visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(CIndividualProcessNode* indiNode, CXLinker<CIndividualProcessNode*>* newIndiMergedLinker, CXLinker<CIndividualProcessNode*>* prevIndiMergedLinker, ...` |
| 40 | 25849-25888 | `bool testIndividualNodeBackendCacheNewMergings(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 26 | 26007-26032 | `bool testIndividualNodeBackendCacheSameMergedBlockingCritical(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |

### NOMINAL HANDLING — Nominal handling  (25 methods, 890 lines)

| L | range | signature |
|---:|---|---|
| 7 | 2153-2159 | `bool checkIndividualNodesReactivationDueToNominalCachingLoss(CIndividualProcessNode* nominalProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 21 | 2161-2181 | `bool reactivateIndividualNodesDueToNominalCachingLoss(CIndividualProcessNode* nominalProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 28 | 3441-3468 | `bool identifyCompatibilityChangedNominalIndividualNodes(CPROCESSINGSET<cint64>* nonCompatibleChangedNominalNodeSet, CPROCESSINGSET<cint64>* compatibleNominalNodeSet, CPROCESSINGSET<cint64>* redundantNodeSet, CPROCESSINGSET<cint64>* newNo...` |
| 12 | 7999-8010 | `QString generateDebugDependentNominalsString(CIndividualProcessNode* indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 24 | 9413-9436 | `CIndividualProcessNode* getDelayProcessingBlockingNominalNode(CIndividualProcessNode* testIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 23 | 9441-9463 | `bool tryDelayNominalProcessing(CConceptProcessDescriptor* conProDes, CIndividualProcessNode* testIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 9467-9476 | `bool canDelayNominalProcessing(CConceptProcessDescriptor* conProDes, CIndividualProcessNode* testIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 61 | 14545-14605 | `bool checkBackendCachedNominalConnection(CIndividualProcessNode*& processIndi, CRole* role, cint64 nominalId, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 16274-16277 | `bool isNominalIndividualNodeAvailable(cint64 indiID, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 16280-16294 | `CIndividualProcessNode* getCorrectedNominalIndividualNode(cint64 indiID, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 65 | 17396-17460 | `bool isLabelConceptSubSetIgnoreNominals(CReapplyConceptLabelSet* subConceptSet, CReapplyConceptLabelSet* superConceptSet, bool* clashFlag, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 57 | 17580-17636 | `bool isLabelConceptEqualSetConsiderNominalsForClashOnly(CReapplyConceptLabelSet* conceptSet1, CReapplyConceptLabelSet* conceptSet2, bool* clashFlag, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 239 | 17732-17970 | `bool isNominalVariablePropagationBindingSubSet(CIndividualProcessNode*& testIndi, CIndividualProcessNode*& blockingIndi, CIndividualNodeBlockingTestData* blockData, bool testContinueBlocking, CBlockingAlternativeData** blockAltData, CCal...` |
| 3 | 20303-20305 | `void propagateIndividualNodeNewNominalConnectionToAncestors(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 20308-20310 | `void propagateIndividualNodeNominalConnectionToAncestors(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 53 | 20313-20365 | `void propagateIndividualNodeNominalConnectionFlagsToAncestors(CIndividualProcessNode*& indi, cint64 nominalPropagationFlags, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 36 | 20368-20403 | `void propagateIndividualNodeNominalConnectionStatusToAncestors(CIndividualProcessNode*& indi, CIndividualProcessNode* copyFromIndiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 55 | 20406-20460 | `void propagateIndividualNodeConnectedNominalToAncestors(CIndividualProcessNode*& indi, cint64 nominalID, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 11 | 20464-20474 | `void propagateIndividualNodeNeighboursNominalConnectionToAncestors(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 22192-22206 | `void createNominalsSuccessorIndividuals(CIndividualProcessNode*& indi, CSortedNegLinker<CRole*>* roleLinkerIt, CRole* ancRole, CSortedNegLinker<CConcept*>* conceptLinkerIt, bool negate, CDependencyTrackPoint* depTrackPoint, cint64 succCa...` |
| 8 | 22497-22504 | `CIndividual* createNewTemporaryNominalIndividual(cint64 indiId, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 25468-25471 | `CIndividualProcessNode* getLocalizedForcedBackendInitializedNominalIndividualNode(cint64 nominalId, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 25473-25490 | `CIndividualProcessNode* getLocalizedForcedBackendInitializedNominalIndividualNode(CIndividualProcessNode* indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 25494-25500 | `CIndividualProcessNode* getForcedInitializedNominalIndividualNode(CIndividualProcessNode* indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 111 | 25891-26001 | `bool testIndividualNodeBackendCacheNominalIndirectConnectionBlockingCritical(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |

### DATATYPE/VALUE HANDLING — Datatype / value-space / literal handling  (12 methods, 487 lines)

| L | range | signature |
|---:|---|---|
| 41 | 9172-9212 | `void checkValueSpaceDistinctSatisfiability(CIndividualProcessNode* processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 17 | 9215-9231 | `void triggerValueSpaceConcepts(CIndividualProcessNode* processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 19 | 9236-9254 | `void addtriggeredValueSpaceConcepts(CIndividualProcessNode* processIndi, CConceptDescriptor* triggeredConceptLinker, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10033-10039 | `CDATAASSERTIONDependencyNode* createDATAASSERTIONDependency(CDependencyTrackPoint*& valueDepTrackPoint, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 10771-10799 | `CRepresentativeVariableBindingPathSetJoiningKeyMap* getRepresentativeJoiningKeyData(CRepresentativeVariableBindingPathSetData* repVarBindPathSetData, CConcept* joinConcept, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 36 | 14457-14492 | `void addDataAssertion(CIndividualProcessNode*& processIndi, CDataAssertionLinker* dataAssertionLinker, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 116 | 21737-21852 | `bool tryInitalizingFromSaturatedData(CIndividualProcessNode*& indi, CXSortedNegLinker<CConcept*>* initConceptLinker, CDependencyTrackPoint* depTrackPoint, bool allowPreprocess, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 60 | 22081-22140 | `bool tryExpansionFromSaturatedData(CIndividualProcessNode*& indi, CIndividualProcessNode* createdSuccIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* depTrackPoint, CIndividualSaturationProcessNode*& saturationIndiNode, bool* sat...` |
| 79 | 22618-22696 | `bool loadIndividualNodeDataFromBackendCache(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 38 | 22988-23025 | `bool visitIndividualsRelevantBackendSynchronisationDataIndividuals(CIndividualProcessNode* indiNode, bool localize, function<bool(CIndividualProcessNode* baseIndiNode, CIndividualProcessNode* locBackendSyncDataIndiNode, CDependencyTrackP...` |
| 35 | 23738-23772 | `CPROCESSHASH< QPair<CRole*, bool>, CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationRoleNeighbourExpansionData >* getBackendSynchronizationFilledRoleNeighbourExpansionDataHash(CIndividualProcessNode* indiNode, CBackendRepres...` |
| 10 | 23984-23993 | `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* getLocalizedIndividualBackendCacheSnychronisationData(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |

### BLOCKING — Blocking (pairwise / label-optimized / dynamic)  (55 methods, 2246 lines)

| L | range | signature |
|---:|---|---|
| 46 | 4049-4094 | `void testCompletionGraphCachingAndBlocking(CCalculationAlgorithmContextBase* calcAlgContext, CIndividualProcessNode* exceptIndividualNode)` |
| 14 | 4193-4206 | `bool isIndividualNodeValidBlocker(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 4216-4227 | `bool isIndividualNodeBackendCacheSynchronizationProcessingBlocked(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 4739-4747 | `bool isSaturationCachedProcessingBlocked(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 4822-4830 | `bool isSatisfiableCachedProcessingBlocked(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 5181-5190 | `void upgradeSignatureBlockingToIndividualReusing(CIndividualProcessNode* processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 5303-5314 | `bool addReusingBlockerFollowing(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 5317-5328 | `bool removeReusingBlockerFollowing(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 5331-5339 | `bool isSignatureBlockedProcessingBlocked(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 38 | 5344-5381 | `bool testAlternativeBlocked(CIndividualProcessNode*& individualNode, CBlockingAlternativeData* blockAltData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 84 | 5385-5468 | `bool detectIndividualNodeSignatureBlockingStatus(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 5472-5483 | `bool addSignatureBlockingBlockerFollowing(CIndividualProcessNode*& blockingIndividualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 5486-5497 | `bool removeSignatureBlockingBlockerFollowing(CIndividualProcessNode*& blockingIndividualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 33 | 5502-5534 | `void rebuildSignatureBlockingCandidateHash(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 47 | 5537-5583 | `CIndividualProcessNode* searchSignatureIndividualNodeBlocker(CIndividualProcessNode*& blockingNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 21 | 5589-5609 | `bool addSignatureIndividualNodeBlockerCandidate(CIndividualProcessNode*& indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 69 | 5612-5680 | `bool establishIndividualNodeSignatureBlocking(CIndividualProcessNode*& blockingIndividualNode, CIndividualProcessNode*& blockerIndividualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 88 | 5685-5772 | `bool refreshIndividualNodeSignatureBlocking(CIndividualProcessNode*& blockingIndividualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 67 | 5776-5842 | `bool updateBlockingReviewMarking(CIndividualProcessNode*& blockingIndividualNode, bool isBlocked, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 110 | 5846-5955 | `bool updateSignatureBlockingConceptExpansion(CIndividualProcessNode*& blockingIndividualNode, CSignatureBlockingIndividualNodeConceptExpansionData* sigBlockingData, CIndividualProcessNode*& blockerIndividualNode, CIndividualNodeAnalizedC...` |
| 11 | 6098-6108 | `bool isConceptSignatureBlockingCritical(CIndividualProcessNode*& individualNode, CConceptDescriptor* conDes, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 6317-6319 | `void propagateIndirectSuccessorSignatureBlocked(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 6326-6328 | `void propagateIndirectSuccessorReuseBlocked(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 6505-6524 | `void reactivateIndirectSignatureBlockedSuccessors(CIndividualProcessNode*& indi, bool recursive, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 25 | 9384-9408 | `void eliminiateBlockedIndividuals(CIndividualProcessNode*& indiProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 17698-17726 | `bool hasOptimizedBlockingB2AutomateTransitionOperands(CConcept* concept, CRole* role, CReapplyConceptLabelSet* vConSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 294 | 18488-18781 | `bool isLabelConceptOptimizedBlocking(CIndividualProcessNode*& testIndi, CIndividualProcessNode*& blockingIndi, CIndividualNodeBlockingTestData* blockData, bool testContinueBlocking, CBlockingAlternativeData** blockAltData, CCalculationAl...` |
| 12 | 18882-18893 | `bool isLabelConceptSubSetBlocking(CIndividualProcessNode*& testIndi, CIndividualProcessNode*& blockingIndi, CIndividualNodeBlockingTestData* blockData, bool testContinueBlocking, CBlockingAlternativeData** blockAltData, CCalculationAlgor...` |
| 6 | 18896-18901 | `bool isLabelConceptEqualBlocking(CIndividualProcessNode*& testIndi, CIndividualProcessNode*& blockingIndi, CIndividualNodeBlockingTestData* blockData, bool testContinueBlocking, CBlockingAlternativeData** blockAltData, CCalculationAlgori...` |
| 21 | 18904-18924 | `bool isLabelConceptEqualPairwiseBlocking(CIndividualProcessNode*& testIndi, CIndividualProcessNode*& blockingIndi, CIndividualNodeBlockingTestData* blockData, bool testContinueBlocking, CBlockingAlternativeData** blockAltData, CCalculati...` |
| 60 | 18927-18986 | `bool isIndividualNodeBlocking(CIndividualProcessNode*& testIndi, CIndividualProcessNode*& blockingIndi, CIndividualNodeBlockingTestData* blockData, bool testContinueBlocking, CBlockingAlternativeData** blockAltData, CCalculationAlgorithm...` |
| 128 | 18991-19118 | `bool detectIndividualNodeBlockedStatus(CIndividualProcessNode*& testIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 19121-19136 | `CIndividualProcessNode* getBlockingIndividualNode(CIndividualProcessNode* blockingTestIndi, CBlockingAlternativeData** blockAltData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 19139-19167 | `bool continueIndividualNodeBlock(CIndividualProcessNode*& indi, CIndividualNodeBlockingTestData* blockData, CIndividualProcessNode*& blockerIndiNode, CBlockingAlternativeData** blockAltData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 19172-19189 | `bool signatureCachedIndividualNodeBlock(CIndividualProcessNode*& indi, CIndividualNodeBlockingTestData* blockData, CIndividualProcessNode*& blockerIndiNode, CBlockingAlternativeData** blockAltData, CCalculationAlgorithmContextBase* calcA...` |
| 3 | 19193-19195 | `void clearBlockingCache(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 50 | 19199-19248 | `CIndividualProcessNode* getAncestorBlockingIndividualNode(CIndividualProcessNode* blockingTestIndi, CBlockingAlternativeData** blockAltData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 72 | 19251-19322 | `CIndividualProcessNode* getAnywhereBlockingIndividualNode(CIndividualProcessNode* blockingTestIndi, CBlockingAlternativeData** blockAltData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 138 | 19326-19463 | `CIndividualProcessNode* getAnywhereBlockingIndividualNodeLinkedCanidateHashed(CIndividualProcessNode* blockingTestIndi, CBlockingAlternativeData** blockAltData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 73 | 19467-19539 | `CIndividualProcessNode* getAnywhereBlockingIndividualNodeCanidateHashed(CIndividualProcessNode* blockingTestIndi, CBlockingAlternativeData** blockAltData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 55 | 19571-19625 | `CBlockingIndividualNodeCandidateIterator getBlockingIndividualNodeCandidateIterator(CIndividualProcessNode* blockingTestIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 19690-19693 | `void propagateIndirectSuccessorBlocking(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 19 | 19789-19807 | `void propagateAddingBlockedProcessingRestrictionToSuccessors(CIndividualProcessNode*& indi, cint64 addRestrictionFlags, bool recursive, cint64 whileNotContainsFlags, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 19851-19868 | `void reactivateIndirectBlockedSuccessors(CIndividualProcessNode*& indi, bool recursive, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 14 | 19871-19884 | `bool reactivateBlockedIndividuals(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 43 | 19997-20039 | `bool isIndividualNodeProcessingBlocked(CIndividualProcessNode* blockingTestIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 20042-20045 | `bool isIndividualNodeExpansionBlocked(CIndividualProcessNode* blockingTestIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 59 | 20049-20107 | `bool needsIndividualNodeExpansionBlockingTest(CConceptProcessDescriptor* conProDes, CIndividualProcessNode* blockingTestIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 21861-21863 | `void propagateIndirectSuccessorSaturationBlocked(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 25 | 22587-22611 | `bool tryEstablishExpansionBlockingWithBackendCacheSynchronisation(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 81 | 23196-23276 | `bool testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 137 | 26037-26173 | `bool testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 27 | 26177-26203 | `bool testIndividualNodeConceptBackendCacheNeighbourExpansionBlockingCritical(CConcept* concept, bool conNegation, bool nondeterministic, CBackendRepresentativeMemoryCacheIndividualAssociationData* assocData, CCalculationAlgorithmContextB...` |
| 26 | 26871-26896 | `bool addBlockingCoreConcept(CConceptDescriptor* conceptDescriptor, CIndividualProcessNode*& processIndi, CReapplyConceptLabelSet* conLabelSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 6 | 27643-27648 | `bool addIndividualToBlockingUpdateReviewProcessingQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |

### CACHING/BACKEND/SATURATION — Caching / backend-cache / saturation  (67 methods, 3587 lines)

| L | range | signature |
|---:|---|---|
| 27 | 2100-2126 | `bool installSaturationCachingReactivation(CIndividualProcessNode* indiProcNode, CSaturationNodeAssociatedDependentNominalSet* nominalSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 2130-2149 | `bool tryInstallSaturationCachingReactivation(CIndividualProcessNode* indiProcNode, CSuccessorConnectedNominalSet* nominalSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 4210-4213 | `bool isIndividualNodeCompletionGraphCached(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 51 | 4230-4280 | `bool detectIndividualNodeBackendCacheSynchronized(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 31 | 4284-4314 | `void clearCompletionGraphCaching(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 28 | 4317-4344 | `bool detectIndividualNodeCompletionGraphCached(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 4350-4359 | `void commitCacheMessages(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 30 | 4363-4392 | `void testIndividualNodeUnsatisfiableCached(CIndividualProcessNode* individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 123 | 4503-4625 | `bool cacheSatisfiableIndividualNodes(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 34 | 4670-4703 | `bool testAllSuccessorsProcessedAndWriteSatisfiableCache(CIndividualProcessNode* indiNode, CPROCESSINGSET<CIndividualProcessNode*>* processedNodeSet, CSatisfiableExpanderCacheHandler* satExpHandler, CCalculationAlgorithmContextBase* calcA...` |
| 29 | 4706-4734 | `bool writeSatisfiableCachedIndividualNodesOfUnsatisfiableBranch(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 68 | 4750-4817 | `bool detectIndividualNodeSaturationCached(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 117 | 4833-4949 | `bool detectIndividualNodeSatisfiableExpandedCached(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 6298-6304 | `void addSatisfiableCachedAbsorbedDisjunctionConcept(CConceptDescriptor *conceptDescriptor, CIndividualProcessNode*& processIndi, CProcessingRestrictionSpecification* procRest, CDependencyTrackPoint* dependencyTrackPoint, CCalculationAlgo...` |
| 7 | 6308-6314 | `void addSatisfiableCachedAbsorbedGeneratingConcept(CConceptDescriptor *conceptDescriptor, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 6321-6323 | `void propagateIndirectSuccessorSatisfiableCached(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 25 | 6332-6356 | `bool isSatisfiableCachedAutomatConceptCompatible(CIndividualProcessNode*& individualNode, CConcept* concept, bool negated, CIndividualProcessNode* ancestorIndiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 62 | 6359-6420 | `bool isSatisfiableCachedCompatible(CIndividualProcessNode*& individualNode, CExpanderBranchedLinker* satBranchLinker, CIndividualProcessNode* ancestorIndiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 60 | 6423-6482 | `void expandCachedConcepts(CIndividualProcessNode*& individualNode, CSignatureSatisfiableExpanderCacheEntry* entry, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 6527-6546 | `void reactivateIndirectSatisfiableCachedSuccessors(CIndividualProcessNode*& indi, bool recursive, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 6548-6567 | `void reactivateIndirectSaturationCachedSuccessors(CIndividualProcessNode*& indi, bool recursive, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 33 | 6865-6897 | `bool rootUnsatisfiabilityWriteCaches(CSatisfiableCalculationTask* task, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 6 | 7391-7396 | `void addIndividualNodeForCacheUnsatisfiableRetrieval(CIndividualProcessNode*& indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 7400-7408 | `bool writeClashDescriptorsToCache(CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 7412-7423 | `bool writeClashDescriptorsToCache(CTrackedClashedDescriptor*& trackedClashedDes, CTrackedClashedDescriptor* additionalTrackedClashedDes, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 117 | 7426-7542 | `bool writeClashDescriptorsToCache(CTrackedClashedDescriptor*& trackedClashedDes, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 9042-9057 | `bool addCachedComputedTypes(CIndividualProcessNode*& indiProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 37 | 14175-14211 | `bool isGeneratingConceptSatisfiableCachedAbsorpable(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 22 | 16438-16459 | `bool hasSaturatedClashedFlagForConcept(CConcept* concept, bool negation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 11 | 18088-18098 | `QSet< QSet<CConcept*> > getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindingsCached(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 50 | 21674-21723 | `bool tryEstablishSaturationCaching(CIndividualProcessNode*& indi, CIndividualProcessNode* succIndi, CIndividualSaturationProcessNode* saturationIndiNode, bool* satCachingPossible, CConceptDescriptor** lastSatCachPossibleConDes, CCalculat...` |
| 46 | 21866-21911 | `bool validateSaturationCachingPossible(CIndividualProcessNode* indi, CIndividualSaturationProcessNode*& saturationIndiNode, bool* satCachingPossible, CConceptDescriptor** lastSatCachPossibleConDes, CConcept* addedConcept, bool addedConce...` |
| 97 | 21917-22013 | `CIndividualSaturationProcessNode* getCreationSuccessorSaturationNode(CIndividualProcessNode*& indi, CConceptDescriptor* conDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 22 | 22054-22075 | `CIndividualSaturationProcessNode* getSaturationResolvedIndividualNodeExtension(CSaturationIndividualNodeExtensionResolveData* resolveData, CPROCESSINGHASH<cint64, CConceptNegationPair>* conExtensionMap, CCalculationAlgorithmContextBase* ...` |
| 113 | 22702-22814 | `bool initializeIndividualNodeWithBackendCache(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 22817-22823 | `CIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(CBackendRepresentativeMemoryCacheIndividualAssociationData* indiAssData, CCalculationAlgorithmCon...` |
| 5 | 22825-22829 | `CIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 79 | 22831-22909 | `bool markIndividualNodeBackendNonConceptSetRelatedProcessing(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 46 | 22921-22966 | `bool tryDelayIndividualNodeInitializationWithBackendConceptSetLabel(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 14 | 22971-22984 | `bool registerProcessedIndividualForBackendConceptSetLabel(CIndividualProcessNode* individual, CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* locBackendSyncData, CBackendRepresentativeMemoryCacheIndividualAssociationD...` |
| 35 | 23159-23193 | `cint64 getBackendCacheRoleRepresentativeNeighbourCount(CIndividualProcessNode* indiNode, CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* backendSyncData, CBackendRepresentativeMemoryCacheIndividualAssociationData* ass...` |
| 47 | 23282-23328 | `bool expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 261 | 23335-23595 | `bool expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache(CIndividualProcessNode* indiNode, CIndividualProcessNode* checkingBackendSyncDataIndiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 55 | 23603-23657 | `bool expandIndividualInferringNeighboursFromBackendCache(CIndividualProcessNode* indiNode, CIndividualProcessNode* backendSyncDataIndiNode, bool forceExpansion, CDependencyTrackPoint* backSyncDepTrackPoint, CCalculationAlgorithmContextBa...` |
| 69 | 23663-23731 | `bool expandIndividualAllNeighboursFromBackendCache(CIndividualProcessNode* indiNode, CIndividualProcessNode* backendSyncDataIndiNode, bool forceExpansion, bool nonDeterministicConsequencesMissingExpansion, CDependencyTrackPoint* backSync...` |
| 31 | 23782-23812 | `bool expandIndividualNeighbourNodeFromBackendCache(CIndividualProcessNode* indiNode, cint64 neighbourIndiId, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 108 | 23819-23926 | `bool expandIndividualNeighbourNodeFromBackendCache(CIndividualProcessNode* indiNode, CBackendRepresentativeMemoryCacheIndividualAssociationData* assocData, cint64 neighbourIndiId, CIndividualNodeRepresentativeMemoryBackendCacheSynchronis...` |
| 444 | 23995-24438 | `bool expandDirectlyInfluencedIndividualNeighbourNodesFromBackendCache(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 190 | 24443-24632 | `CIndividualProcessNode* queuedIndividualBackendNeighbourExpansion(CIndividualProcessNode*& baseIndiNode, CBackendNeighbourExpansionControllingData* expContData, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 6 | 24706-24711 | `bool markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 11 | 24715-24725 | `bool markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessingForDisjointRoles(CIndividualProcessNode* indiNode, CRole* role, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 8 | 24727-24734 | `bool markIndividualNodeBackendNonConceptSetRelatedProcessingForDisjointRoles(CIndividualProcessNode* indiNode, CRole* role, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 8 | 24736-24743 | `bool markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessingForDisjointRoles(CIndividualProcessNode* indiNode, CRole* role, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 53 | 24745-24797 | `bool markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessing(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 79 | 24803-24881 | `bool prepareBackendExpansionReuseBranching(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 25 | 24889-24913 | `bool prepareBackendIndividualFixedReuseExpansion(CIndividualProcessNode*& indiProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 88 | 24916-25003 | `bool prepareBackendIndividualPrioritizedReuseExpansion(CIndividualProcessNode*& indiProcNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 77 | 25010-25086 | `bool checkIndividualBackendExpansionReuseable(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 282 | 25092-25373 | `bool reuseIndividualBackendExpansion(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 80 | 26283-26362 | `bool testIndividualNodeBackendCacheConceptsSynchronization(CIndividualProcessNode* indiNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 40 | 26368-26407 | `bool validateBackendSynchronisationContinued(CIndividualProcessNode* indi, CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* backendSyncData, CConcept* addedConcept, bool addedConceptNegation, CCalculationAlgorithmConte...` |
| 22 | 26900-26921 | `bool isConceptUnsatisfiabilitySaturated(CConcept* concept, bool negation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 27587-27596 | `bool addIndividualToBackendSynchronisationRetestQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 27598-27607 | `bool addIndividualToBackendDirectInfluenceExpansionQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 27609-27618 | `bool addIndividualToBackendIndirectCompatibilityExpansionQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 27621-27630 | `bool addIndividualToBackendReuseExpansionQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 27632-27641 | `bool addIndividualToBackendNeighbourExpansionQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |

### INCREMENTAL EXPANSION — Incremental expansion / compatibility  (20 methods, 651 lines)

| L | range | signature |
|---:|---|---|
| 116 | 2937-3052 | `bool initializeIncrementalIndividualExpansion(CIndividualProcessNode* individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 14 | 3058-3071 | `CIndividual* getNextIncrementalExpansionIndividual(CIndividualProcessNode* individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 3075-3084 | `CIndividualProcessNode* incrementalNodeExpansion(CIndividualProcessNode* expandNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 3088-3094 | `bool requiresIncrementalNodeExpansion(CIndividualProcessNode* individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 48 | 3384-3431 | `void pruneIncrementalRemovedSuccessors(CIndividualProcessNode*& indi, CPROCESSINGSET<cint64>* compatibleNominalNodeSet, CPROCESSINGSET<cint64>* pruningNodeSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 3476-3493 | `bool checkCompatibilityUpdateDirectlyChangedPropagation(CIndividualProcessNode* individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 3497-3508 | `bool linkCreationDirectlyChangedNeighbourConnectionUpdate(CIndividualProcessNode* sourceIndi, CIndividualProcessNode* destIndi, bool queueIncrementalExpansion, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 3512-3529 | `bool establishDirectlyChangedNeighbourConnection(CIndividualProcessNode* individualNode, CIndividualProcessNode* neighbourNodeCandidate, bool queueIncrementalExpansion, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 101 | 3534-3634 | `bool propagateDirectlyChangedNeighbourNodeConnection(CIndividualProcessNode* individualNode, bool queueIncrementalExpansion, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 64 | 3639-3702 | `CIndividualProcessNode* searchDirectlyChangedNeighbourNodeConnection(CIndividualProcessNode* individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 13 | 3706-3718 | `bool clearDirectlyChangedNeighbourConnection(CIndividualProcessNode* individualNode, bool queueCompatibilityChecks, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 40 | 3722-3761 | `bool clearPropagatedDirectlyChangedNeighbourConnection(CIndividualProcessNode* individualNode, bool queueCompatibilityChecks, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 4955-4972 | `bool hasCompatibleConceptSetReuse(CIndividualProcessNode* indiNode, CReapplyConceptLabelSet* subConceptSet, CIndividualProcessNode* reuseNodeCand, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 45 | 5960-6004 | `bool hasCompatibleConceptSetSignature(CIndividualProcessNode*& blockingNode, CReapplyConceptLabelSet* conSet, CIndividualProcessNode* compatibleTestNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 23 | 8014-8036 | `QString generateDebugIncrementalExpansionString(CIndividualProcessNode* indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 24 | 17990-18013 | `bool areVariablePropagationBindingsCompatible(CVariableBindingPath* varBindPath1, CVariableBindingPath* varBindPath2, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 34 | 18017-18050 | `QSet<CConcept*> getConceptsForCompatibleVariablePropagationBindings(CIndividualProcessNode*& individualNode, CVariableBindingPath* varBindPath, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 18262-18277 | `cint64 getBindingsCompatibleConceptSetsHashValue(const QSet< QSet<CConcept*> >& associatedConceptSets, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 10 | 27554-27563 | `bool addIndividualToIncrementalCompatibilityCheckingQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 27565-27584 | `bool addIndividualToIncrementalExpansionQueue(CIndividualProcessNode* individual, CCalculationAlgorithmContextBase* calcAlgContext)` |

### NEIGHBOUR/BACKEND EXPANSION — Neighbour / backend-cache node expansion  (12 methods, 611 lines)

| L | range | signature |
|---:|---|---|
| 87 | 6009-6095 | `bool anlyzeIndiviudalNodesConceptExpansion(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 48 | 23930-23977 | `bool expandIndirectlyConnectedIndividuals(CIndividualProcessNode* indiNode, bool checkExpansionRequired, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 35 | 24645-24679 | `bool canDelayRepresentativeNeighbourExpansion(CIndividualProcessNode* expIndiNode, CBackendNeighbourExpansionQueueDataLinker* backendNeighbourExpDataLinker, CPROCESSHASH<CBackendRepresentativeMemoryLabelCacheItem *, CIndividualNodeRepres...` |
| 18 | 24683-24700 | `bool delayingRepresentativeNeighbourExpansion(CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* locBackendSyncData, bool expansionDelaying, bool representativeExpansion, CIndividualNodeRepresentativeMemoryBackendCacheSy...` |
| 49 | 25379-25427 | `bool ensurePropagationCutLinksToExpandedIndividual(CIndividualProcessNode* propCutIndiNode, CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* locPropCutIndiBackendSyncData, CBackendNeighbourExpansionQueueDataLinker* bac...` |
| 37 | 25503-25539 | `bool expandDirectlyInfluencedNeighboursWithPropagation(CConcept* concept, bool conNegation, bool nondeterministic, CIndividualProcessNode* indiNode, CBackendRepresentativeMemoryCacheIndividualAssociationData* assocData, CIndividualProces...` |
| 27 | 25547-25573 | `bool ensureBaseLinkExpansion(CIndividualProcessNode* expIndiNode, CIndividualProcessNode* indiNode, cint64 neighbourNodeId, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 126 | 25577-25702 | `bool initializeNeighbourExpansionWithPropagation(CIndividualProcessNode* indiNode, CIndividualProcessNode* locBackendSyncDataIndiNode, CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* locBackendSyncData, CDependencyTra...` |
| 16 | 25727-25742 | `bool isNeighbourExpansionWithPropagationAllowed(CIndividualProcessNode* indiNode, CConcept* concept, bool conNegation, cint64 neighbourIndiId, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 53 | 25745-25797 | `bool canExpansionPotentiallyInfluenceNeighbourWithPotentialPropagation(CIndividualProcessNode* indiNode, CConcept* concept, bool conNegation, bool nondeterministic, CBackendRepresentativeMemoryCacheIndividualAssociationData* assData, cin...` |
| 45 | 25801-25845 | `bool canExpandDirectlyInfluencedNeighbourWithPropagation(CIndividualProcessNode* indiNode, CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* locBackendSyncData, CDependencyTrackPoint* backSyncDepTrackPoint, CConcept* co...` |
| 70 | 26209-26278 | `bool debugCheckDirectlyInfluencedNeighbourWithPropagationPossible(CConcept* concept, bool conNegation, CIndividualProcessNode* indiNode, CBackendRepresentativeMemoryCacheIndividualAssociationData* assocData, CIndividualNodeRepresentative...` |

### DEPENDENCY TRACKING — Dependency tracking  (70 methods, 926 lines)

| L | range | signature |
|---:|---|---|
| 60 | 2873-2932 | `bool areAllDependentFactsUnchanged(CIndividualProcessNode* individualNode, CIndividualProcessNode* backtrackedIndividualNode, CDependencyTrackPoint* prevConDepTrackPoint, CIndividualProcessNodeVector* prevIndiNodeVec, cint64& remBacktrac...` |
| 3 | 3871-3873 | `bool trackIndividualReferredDependence(cint64 indiID, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 3876-3878 | `bool trackIndividualExtendedDependence(cint64 indiID, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 66 | 3880-3945 | `bool trackIndividualDependence(cint64 indiID, bool indiReferred, bool indiExtended, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 4032-4046 | `bool isConceptFromPredecessorDependent(CIndividualProcessNode*& individualNode, CConceptDescriptor* conDes, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 6112-6140 | `bool isConceptFromDirectOrPredecessorOrNondeterminismusDependent(CIndividualProcessNode*& individualNode, CConceptDescriptor* conDes, CDependencyTrackPoint* depTrackPoint, bool* directDependentFlag, CCalculationAlgorithmContextBase* calc...` |
| 104 | 6144-6247 | `bool getConceptDependenciesToSameIndividualNode(CIndividualProcessNode*& individualNode, CConceptDescriptor* conDes, CDependencyTrackPoint* depTrackPoint, CXLinker<CConceptDescriptor*>*& depLinker, CCalculationAlgorithmContextBase* calcA...` |
| 17 | 6723-6739 | `QString writeDebugTrackingLineStringToFile(const QString& debugDataString, const QString& fileNameString, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 27 | 6744-6770 | `QString generateDebugTrackingLineString(CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 7360-7388 | `void markDependencyRelevance(CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 7900-7917 | `bool initializeTrackingLine(CTrackedClashedDependencyLine* trackingLine, CTrackedClashedDescriptor* trackingClashes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 7975-7978 | `CIndividualProcessNode* getCoresspondingIndividualNodeFromDependency(CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 7981-7995 | `CIndividualProcessNode* getCoresspondingIndividualNodeFromDependency(CDependencyNode* depNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 124 | 8175-8298 | `QString generateDebugDependencyString(CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 9755-9761 | `CREPRESENTATIVEGROUNDINGDependencyNode* createREPRESENTATIVEGROUNDINGDependency(CDependencyTrackPoint*& implContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint...` |
| 7 | 9763-9769 | `CREPRESENTATIVEJOINDependencyNode* createREPRESENTATIVEJOINDependency(CDependencyTrackPoint*& joinContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDepende...` |
| 7 | 9771-9777 | `CREPRESENTATIVEBINDVARIABLEDependencyNode* createREPRESENTATIVEBINDVARIABLEDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, C...` |
| 7 | 9779-9785 | `CREPRESENTATIVEIMPLICATIONDependencyNode* createREPRESENTATIVEIMPLICATIONDependency(CDependencyTrackPoint*& implContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackP...` |
| 7 | 9787-9793 | `CREPRESENTATIVEALLDependencyNode* createREPRESENTATIVEALLDependency(CDependencyTrackPoint*& allDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPoi...` |
| 7 | 9795-9801 | `CREPRESENTATIVEANDDependencyNode* createREPRESENTATIVEANDDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorit...` |
| 7 | 9803-9809 | `CRESOLVEREPRESENTATIVEDependencyNode* createRESOLVEREPRESENTATIVEDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CRepresentativeVariableBindingPathMap* resolveVarBind...` |
| 7 | 9820-9826 | `CPROPAGATEVARIABLECONNECTIONDependencyNode* createPROPAGATEVARIABLECONNECTIONDependency(CIndividualProcessNode* processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgC...` |
| 7 | 9828-9834 | `CVARBINDPROPAGATEIMPLICATIONDependencyNode* createVARBINDPROPAGATEIMPLICATIONDependency(CDependencyTrackPoint*& implContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTr...` |
| 7 | 9836-9842 | `CVARBINDPROPAGATEGROUNDINGDependencyNode* createVARBINDPROPAGATEGROUNDINGDependency(CDependencyTrackPoint*& implContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackP...` |
| 7 | 9844-9850 | `CVARBINDPROPAGATEALLDependencyNode* createVARBINDPROPAGATEALLDependency(CDependencyTrackPoint*& allDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrac...` |
| 7 | 9852-9858 | `CVARBINDPROPAGATEANDDependencyNode* createVARBINDPROPAGATEANDDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlg...` |
| 7 | 9860-9866 | `CPROPAGATEVARIABLEBINDINGDependencyNode* createPROPAGATEVARIABLEBINDINGDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDepe...` |
| 7 | 9868-9874 | `CPROPAGATEVARIABLEBINDINGSSUCCESSORDependencyNode* createPROPAGATEVARIABLEBINDINGSSUCCESSORDependency(CDependencyTrackPoint*& allDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prev...` |
| 7 | 9876-9882 | `CVARBINDVARIABLEDependencyNode* createVARBINDVARIABLEDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmCo...` |
| 7 | 9884-9890 | `CVARBINDPROPAGATEJOINDependencyNode* createVARBINDPROPAGATEJOINDependency(CDependencyTrackPoint*& continueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDepende...` |
| 7 | 9897-9903 | `CBINDPROPAGATEGROUNDINGDependencyNode* createBINDPROPAGATEGROUNDINGDependency(CDependencyTrackPoint*& implContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, ...` |
| 7 | 9905-9911 | `CPROPAGATECONNECTIONAWAYDependencyNode* createPROPAGATECONNECTIONAWAYDependency(CIndividualProcessNode* processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 9913-9919 | `CPROPAGATECONNECTIONDependencyNode* createPROPAGATECONNECTIONDependency(CIndividualProcessNode* processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 9921-9927 | `CBINDPROPAGATECYCLEDependencyNode* createBINDPROPAGATECYCLEDependency(CDependencyTrackPoint*& continueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyT...` |
| 7 | 9929-9935 | `CBINDPROPAGATEALLDependencyNode* createBINDPROPAGATEALLDependency(CDependencyTrackPoint*& allDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPoint...` |
| 7 | 9937-9943 | `CPROPAGATEBINDINGSSUCCESSORDependencyNode* createPROPAGATEBINDINGSSUCCESSORDependency(CDependencyTrackPoint*& allDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, C...` |
| 7 | 9945-9951 | `CBINDPROPAGATEIMPLICATIONDependencyNode* createBINDPROPAGATEIMPLICATIONDependency(CDependencyTrackPoint*& implContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoi...` |
| 7 | 9953-9959 | `CANDDependencyNode* createANDDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 9961-9967 | `CBINDPROPAGATEANDDependencyNode* createBINDPROPAGATEANDDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithm...` |
| 7 | 9969-9975 | `CPROPAGATEBINDINGDependencyNode* createPROPAGATEBINDINGDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependency* prevOthe...` |
| 7 | 9977-9983 | `CBINDVARIABLEDependencyNode* createBINDVARIABLEDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextB...` |
| 7 | 9985-9991 | `CNOMINALDependencyNode* createNOMINALDependency(CDependencyTrackPoint*& nominalContDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPoint* nominalD...` |
| 7 | 9993-9999 | `CAUTOMATCHOOSEDependencyNode* createAUTOMATCHOOSEDependency(CDependencyTrackPoint*& andDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContex...` |
| 7 | 10001-10007 | `CSOMEDependencyNode* createSOMEDependency(CDependencyTrackPoint*& someDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgCon...` |
| 7 | 10009-10015 | `CSELFDependencyNode* createSELFDependency(CDependencyTrackPoint*& someDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgCon...` |
| 7 | 10017-10023 | `CVALUEDependencyNode* createVALUEDependency(CDependencyTrackPoint*& valueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPoint* nominalDepTrackPoi...` |
| 7 | 10025-10031 | `CROLEASSERTIONDependencyNode* createROLEASSERTIONDependency(CDependencyTrackPoint*& valueDepTrackPoint, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPoint* nominalDepTrackPoint, CRole* b...` |
| 7 | 10041-10047 | `CNEGVALUEDependencyNode* createNEGVALUEDependency(CDependencyTrackPoint*& negValueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPoint* nominalDe...` |
| 7 | 10049-10055 | `CALLDependencyNode* createALLDependency(CDependencyTrackPoint*& allDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPoint* linkDepTrackPoint, CCalc...` |
| 7 | 10083-10089 | `CFUNCTIONALDependencyNode* createFUNCTIONALDependency(CDependencyTrackPoint*& functionalContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackPo...` |
| 7 | 10091-10097 | `CDISTINCTDependencyNode* createDISTINCTDependency(CDependencyTrackPoint*& distinctDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase...` |
| 7 | 10099-10105 | `CAUTOMATTRANSACTIONDependencyNode* createAUTOMATTRANSACTIONDependency(CDependencyTrackPoint*& allDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackP...` |
| 7 | 10107-10113 | `CATLEASTDependencyNode* createATLEASTDependency(CDependencyTrackPoint*& atleastDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* c...` |
| 7 | 10115-10121 | `CORDependencyNode* createORDependency(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10123-10129 | `CATMOSTDependencyNode* createATMOSTDependency(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10139-10145 | `CREUSEINDIVIDUALDependencyNode* createREUSEINDIVIDUALDependency(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10147-10153 | `CREUSECOMPLETIONGRAPHDependencyNode* createREUSECOMPLETIONGRAPHDependency(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10165-10171 | `CREUSECONCEPTSDependencyNode* createREUSECONCEPTSDependency(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10173-10179 | `CQUALIFYDependencyNode* createQUALIFYDependency(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10183-10189 | `CORONLYOPTIONDependencyNode* createORONLYOPTIONDependency(CDependencyTrackPoint*& orContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependency* prevOther...` |
| 7 | 10192-10198 | `CIMPLICATIONDependencyNode* createIMPLICATIONDependency(CDependencyTrackPoint*& implContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependency* prevOther...` |
| 7 | 10201-10207 | `CEXPANDEDDependencyNode* createEXPANDEDDependency(CDependencyTrackPoint*& expContinueDepTrackPoint, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* prevDepTrackPoint, CDependency* prevOtherDependencies, CCalculationAlgorithm...` |
| 7 | 10210-10216 | `CCONNECTIONDependencyNode* createCONNECTIONDependency(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10230-10236 | `CREUSEBACKENDEXPANSIONMODESDependencyNode* createREUSEBACKENDEXPANSIONMODESDependency(CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10239-10245 | `CREUSEBACKENDFIXEDINDIVIDUALEXPANSIONDependencyNode* createREUSEBACKENDFIXEDINDIVIDUALEXPANSIONDependency(CIndividualProcessNode*& processIndi, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 10248-10254 | `CREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDependencyNode* createREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDependency(CIndividualProcessNode*& processIndi, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcA...` |
| 7 | 10259-10265 | `CREUSEBACKENDVALUEDependencyNode* createREUSEBACKENDVALUEDependency(CDependencyTrackPoint*& valueDepTrackPoint, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CDependencyTrackP...` |
| 17 | 16669-16685 | `CNonDeterministicDependencyTrackPoint* createNonDeterministicDependencyTrackPointBranch(CNonDeterministicDependencyNode* dependencyNode, bool singleBranch, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 17 | 17182-17198 | `CSatisfiableCalculationTask* createDependendBranchingTaskList(cint64 newTaskCount, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 23027-23033 | `bool hasNondeterministicDependency(CDependencyTrackPoint* dependencyTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |

### BACKTRACKING — Backtracking  (11 methods, 698 lines)

| L | range | signature |
|---:|---|---|
| 88 | 6774-6861 | `void clashedBacktracking(CClashedDependencyDescriptor* clashes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 6963-6974 | `bool backtrackFromTrackingLine(CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 98 | 6976-7073 | `bool backtrackFromTrackingLineStep(CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 7075-7077 | `bool backtrackNonDeterministicBranchingClashedDescriptorFromCurrentIndividualNodeLevel(CTrackedClashedDescriptor* trackedClashedDes, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 7080-7082 | `bool backtrackNonDeterministicBranchingClashedDescriptorFromPreviousIndividualNodeLevel(CTrackedClashedDescriptor* trackedClashedDes, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 265 | 7085-7349 | `bool backtrackNonDeterministicBranchingClashedDescriptor(CTrackedClashedDescriptor* trackedClashedDes, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 11 | 7655-7665 | `bool backtrackDeterministicBranchingClashedDescriptorFromCurrentIndividualNodeLevel(CTrackedClashedDescriptor* trackedClashedDes, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 6 | 7669-7674 | `bool backtrackDeterministicClashedDescriptorFromPreviousIndividualNodeLevels(CTrackedClashedDescriptor* trackedClashedDes, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 96 | 7677-7772 | `CTrackedClashedDescriptor* getBacktrackedDeterministicClashedDescriptorsBeforeProcessingTag(CTrackedClashedDescriptor* trackedClashedDescriptors, cint64 processingTag, CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmCon...` |
| 85 | 7779-7863 | `CTrackedClashedDescriptor* getBacktrackedDeterministicClashedDescriptors(CTrackedClashedDescriptor* trackedClashedDes, CTrackedClashedDependencyLine* trackingLine, cint64* minIndiLevel, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 31 | 7866-7896 | `CTrackedClashedDescriptor* tryGetInvalidSameIndividualNodeLevelBacktrackedDeterministicClashedDescriptors(CTrackedClashedDescriptor* trackedClashedDes, CTrackedClashedDependencyLine* trackingLine, cint64* minIndiLevel, CCalculationAlgori...` |

### CLASH PROCESSING — Clash processing  (18 methods, 475 lines)

| L | range | signature |
|---:|---|---|
| 11 | 4395-4405 | `CClashedDependencyDescriptor* createClashedIndividualNodeDescriptor(CClashedDependencyDescriptor* prevClashes, CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 17 | 6569-6585 | `QString generateDebugTrackedClashedDescriptorSummaryString(CTrackedClashedDescriptor* trackedClashDescriptors, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 131 | 6588-6718 | `QString generateDebugTrackedClashedDescriptorString(CTrackedClashedDescriptor* trackedClashDescriptors, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 8 | 6952-6959 | `CTrackedClashedDescriptor* getFreeTrackedClashedDescriptor(CTrackedClashedDependencyLine* trackingLine, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 6 | 7352-7357 | `void markRelevanceForTrackedClashedDescriptors(CTrackedClashedDescriptor* descriptors, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 8 | 7545-7552 | `bool addIndiNodeSignatureOfUnsatisfiableClashedDescriptors(CTrackedClashedDescriptor* trackedClashedDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 7554-7556 | `bool isClashedDescriptorSortedBefore(CTrackedClashedDescriptor* trackedClashedDesBefore, CTrackedClashedDescriptor* trackedClashedDesAfter, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 25 | 7559-7583 | `CTrackedClashedDescriptor* getSortedClashedDescriptors(CTrackedClashedDescriptor* trackedClashedDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 7586-7592 | `bool writeUnsatisfiableClashedDescriptors(CTrackedClashedDescriptor* trackedClashedDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 58 | 7595-7652 | `CTrackedClashedDescriptor* getCollectedFilteredClashedDescriptorsFromBranch(CTrackedClashedDescriptor* nonDetClashedPointingDes, CNonDeterministicDependencyNode* nonDetBranchDepNode, CTrackedClashedDependencyLine* trackingLine, CCalculat...` |
| 15 | 7921-7935 | `CTrackedClashedDescriptor* createTrackedClashesDescriptors(CClashedDependencyDescriptor* clashes, CCalculationAlgorithmContextBase* calcAlgContext, CMemoryAllocationManager* tmpMemMan, bool copyIndependentConceptDescriptors)` |
| 35 | 7939-7973 | `CTrackedClashedDescriptor* createTrackedClashesDescriptor(CClashedDependencyDescriptor* clashDes, CCalculationAlgorithmContextBase* calcAlgContext, CMemoryAllocationManager* tmpMemMan, bool copyIndependentConceptDescriptors)` |
| 4 | 16717-16720 | `CClashedDependencyDescriptor* createClashedConceptDescriptor(CClashedDependencyDescriptor* prevClashes, CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmCont...` |
| 4 | 16722-16725 | `CClashedDependencyDescriptor* createClashedIndividualLinkDescriptor(CClashedDependencyDescriptor* prevClashes, CIndividualLinkEdge* link, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 16727-16730 | `CClashedDependencyDescriptor* createClashedIndividualDistinctDescriptor(CClashedDependencyDescriptor* prevClashes, CDistinctEdge* distinct, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 16732-16735 | `CClashedDependencyDescriptor* createClashedNegationDisjointDescriptor(CClashedDependencyDescriptor* prevClashes, CNegationDisjointEdge* disjointNegLink, CDependencyTrackPoint* prevDepTrackPoint, CCalculationAlgorithmContextBase* calcAlgC...` |
| 69 | 17323-17391 | `bool isLabelConceptClashSet(CReapplyConceptLabelSet* subConceptSet, CReapplyConceptLabelSet* superConceptSet, bool* subSetFlag, bool ignoreNominalsForSubsetChecking, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 66 | 20867-20932 | `bool isLabelConceptClashSet(CIndividualProcessNode* subSetIndi, CIndividualProcessNode* superSetIndi, CClashedDependencyDescriptor*& clashDescriptors, CCalculationAlgorithmContextBase* calcAlgContext)` |

### GENERIC HELPERS — Generic helpers / accessors / label tests  (104 methods, 4299 lines)

| L | range | signature |
|---:|---|---|
| 352 | 494-845 | `void readCalculationConfig(CSatisfiableCalculationTask* satCalcTask)` |
| 63 | 4097-4159 | `void analyzeABoxCompressionPossibilities(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 28 | 4163-4190 | `void analyzeBranchingMemoryWasting(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 49 | 4408-4456 | `void testProblematicConceptSet(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 38 | 4462-4499 | `bool analyseBranchingStatistics(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 40 | 4628-4667 | `void debugTestCriticalConceptSet(QStringList& conSetList, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 42 | 4977-5018 | `CIndividualProcessNode* searchSignatureReusingIndividualNode(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 5 | 5021-5025 | `void removeIndividualReusing(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 151 | 5028-5178 | `void updateIndividualReusing(CIndividualProcessNode* processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 106 | 5193-5298 | `void establishIndividualReusing(CIndividualProcessNode* processIndi, CIndividualProcessNode* reuseIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 6486-6503 | `void reactivateIndirectReuseSuccessors(CIndividualProcessNode*& indi, bool recursive, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 31 | 6902-6932 | `bool cancellationRootTask(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 6935-6949 | `bool cancellationTask(CSatisfiableCalculationTask* task, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 135 | 8039-8173 | `QString generateDebugIndiStatusString(CIndividualProcessNode* indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 62 | 8301-8362 | `QStringList generateExtendedDebugConceptSetStringList(CReapplyConceptLabelSet* conSet, CConceptPropagationBindingSetHash* propBindSetHash, CConceptVariableBindingPathSetHash* varBindPathSetHash, CCalculationAlgorithmContextBase* calcAlgC...` |
| 26 | 8368-8393 | `QString writeGeneratedExtendedDebugIndiModelStringList(const QString& filename, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 230 | 8396-8625 | `QString generateExtendedDebugIndiModelStringList(CCalculationAlgorithmContextBase* calcAlgContext, QStringList* list)` |
| 90 | 8629-8718 | `QString generateDebugIndiModelStringList(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 125 | 9257-9381 | `void tryCompletionGraphReuse(CIndividualProcessNode* processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 9617-9631 | `bool isRestrictedTopObjectPropertyPropagation(CIndividualProcessNode*& processIndi, CIndividualProcessNode*& destIndi, CConcept* concept, bool negated, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 10650-10669 | `bool areRepresentativesJoinable(CIndividualProcessNode*& processIndi, CRepresentativeVariableBindingPathSetData* leftRepData, CRepresentativeVariableBindingPathSetData* rightRepData, CSortedLinker<CVariable*>* varLinker, CCalculationAlgo...` |
| 44 | 10672-10715 | `void createCommonJoiningAll(CRepresentativeJoiningCommonKeyMap* repJoinCommonKeyMap, CRepresentativeJoiningAllDataExtension* joinAllExtData, CRepresentativeVariableBindingPathSetData* leftRepData, CRepresentativeVariableBindingPathSetDat...` |
| 49 | 10719-10767 | `void createCommonJoiningKeyMap(CRepresentativeJoiningCommonKeyMap* repJoinCommonKeyMap, CRepresentativeVariableBindingPathSetJoiningKeyMap* firstJoiningKeyMap, CRepresentativeVariableBindingPathSetData* firstRepData, CRepresentativeVaria...` |
| 68 | 11050-11117 | `void propagateRepresentativeToSuccessor(CIndividualProcessNode* processIndi, CIndividualProcessNode*& succIndi, CSortedNegLinker<CConcept*>* conceptOpLinker, bool negate, CConceptDescriptor* conDes, CIndividualLinkEdge* restLink, CCalcul...` |
| 116 | 11260-11375 | `void updateRepresentativePropagationSet(CIndividualProcessNode*& processIndi, CRepresentativePropagationSet* repPropSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 11379-11387 | `void propagateRepresentative(CIndividualProcessNode*& processIndi, CRepresentativePropagationDescriptor* repPropDes, CRepresentativePropagationSet* repPropSet, CDependencyTrackPoint* nextDepTrackPoint, CCalculationAlgorithmContextBase* c...` |
| 55 | 11390-11444 | `bool requiresRepresentativePropagation(CIndividualProcessNode*& processIndi, CRepresentativePropagationDescriptor* repPropDes, CRepresentativePropagationSet* testRepPropSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 62 | 13294-13355 | `void propagatePropagationBindingsToSuccessor(CIndividualProcessNode* processIndi, CIndividualProcessNode*& succIndi, CSortedNegLinker<CConcept*>* conceptOpLinker, bool negate, CConceptDescriptor* conDes, CIndividualLinkEdge* restLink, CC...` |
| 29 | 13362-13390 | `bool propagateInitialPropagationBindingsToSuccessor(CIndividualProcessNode*& processIndi, CIndividualProcessNode* succIndi, CConceptDescriptor* conDes, CPropagationBindingSet* newPropBindingSet, CPropagationBindingSet* prevPropBindingSet...` |
| 69 | 13395-13463 | `bool propagateFreshPropagationBindingsToSuccessor(CIndividualProcessNode*& processIndi, CIndividualProcessNode* succIndi, CConceptDescriptor* conDes, CPropagationBindingSet* newPropBindingSet, CPropagationBindingSet* prevPropBindingSet, ...` |
| 63 | 13626-13688 | `void propagatePropagationBindings(CIndividualProcessNode*& processIndi, CConceptProcessDescriptor*& conProDes, bool negate, bool propagateAllFlag, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 13773-13801 | `bool propagateInitialPropagationBindings(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CPropagationBindingSet* newPropBindingSet, CPropagationBindingSet* prevPropBindingSet, CDependency* otherDependencies, CCalculatio...` |
| 68 | 13804-13871 | `bool propagateFreshPropagationBindings(CIndividualProcessNode*& processIndi, CConceptDescriptor* conDes, CPropagationBindingSet* newPropBindingSet, CPropagationBindingSet* prevPropBindingSet, CDependency* otherDependencies, CCalculationA...` |
| 46 | 14410-14455 | `void addReverseRoleAssertion(CIndividualProcessNode*& processIndi, CReverseRoleAssertionLinker* reverseRoleAssertionLinker, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 46 | 14495-14540 | `void addRoleAssertion(CIndividualProcessNode*& processIndi, CRoleAssertionLinker* roleAssertionLinker, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 36 | 14823-14858 | `bool hasIdenticalConceptOperands(CSortedNegLinker<CConcept*>* opConLinker1, CSortedNegLinker<CConcept*>* opConLinker2)` |
| 78 | 15530-15607 | `CSatisfiableCalculationTask* createDistinctBranchingTask(CIndividualProcessNode*& processIndiNode, CConceptProcessDescriptor*& conProDes, CIndividualProcessNode*& distinctIndiNode, bool createAsNominal, CNonDeterministicDependencyNode* m...` |
| 27 | 16464-16490 | `bool getAdditionalDisjunctCheckingConcept(CConcept* opConcept, bool opConNegation, CConcept** checkingConcept, bool* checkingNegation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 17013-17019 | `bool isConceptAdditionAtomaric(CConcept* addingConcept, bool negated, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 17206-17217 | `void installConceptRoleBranchTrigger(CIndividualProcessNode*& processIndi, CConceptDescriptor* conceptDescriptor, CDependencyTrackPoint* depTrackPoint, CProcessingRestrictionSpecification* procRest, CConceptRoleBranchingTrigger* trigger,...` |
| 20 | 17221-17240 | `CConceptRoleBranchingTrigger* searchNextConceptRoleBranchTrigger(CIndividualProcessNode*& processIndi, CConceptRoleBranchingTrigger* triggers, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 13 | 17307-17319 | `CIndividualLinkEdge* getIndividualNodeLink(CIndividualProcessNode*& indiSource, CIndividualProcessNode*& indiDestination, CRole* role, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 78 | 17466-17543 | `bool isLabelConceptSubSet(CReapplyConceptLabelSet* subConceptSet, CReapplyConceptLabelSet* superConceptSet, CConceptDescriptor** firstNotEntailedConDes, bool* equalConSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 17547-17575 | `bool isLabelConceptEqualSet(CReapplyConceptLabelSet* conceptSet1, CReapplyConceptLabelSet* conceptSet2, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 54 | 17642-17695 | `bool isPairwiseLabelConceptEqualSet(CReapplyConceptLabelSet* conceptSet1, CReapplyConceptLabelSet* conceptSet1Pair, CReapplyConceptLabelSet* conceptSet2, CReapplyConceptLabelSet* conceptSet2Pair, CCalculationAlgorithmContextBase* calcAlg...` |
| 30 | 18055-18084 | `bool collectIndividualNodeVariablePropagationBindings(CIndividualProcessNode*& individualNode, QHash<cint64, CVariableBindingPath*>& collecingPropagationVariableBindingsHash, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 13 | 18102-18114 | `QSet< QSet<CConcept*> > getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindings(CIndividualProcessNode*& individualNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 30 | 18120-18149 | `QSet< QList< QSet<CConcept*> > > getIndividualNodesListAssociatedConceptsSetFromVariablePropagationBindings(CIndividualProcessNode*& individualNode, CIndividualProcessNode*& ancestorIndividualNode, const QList<cint64>& dependentNominalId...` |
| 104 | 18155-18258 | `bool isAnonymousVariablePropagationBindingSingleIndividualAnalogousPath(CIndividualProcessNode*& testIndi, CIndividualProcessNode*& blockingIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 101 | 18283-18383 | `bool isAnonymousVariablePropagationBindingAnalogousPath(CIndividualProcessNode*& testIndi, CIndividualProcessNode*& blockingIndi, CIndividualNodeBlockingTestData* blockData, bool testContinueBlocking, CBlockingAlternativeData** blockAltD...` |
| 20 | 18390-18409 | `QString generateDebugIndividualNodeAssociatedConceptsString(cint64 indiNodeId, const QSet<CConcept*>& associatedConcepts, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 12 | 18414-18425 | `QString generateDebugIndividualNodeAssociatedConceptsSetString(CIndividualProcessNode*& individualNode, const QSet< QSet<CConcept*> >& allVariableMappingsAssociatedConceptsSet, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 33 | 18430-18462 | `QString generateDebugIndividualNodesListAssociatedConceptsSetString(CIndividualProcessNode*& individualNode, CIndividualProcessNode*& ancestorIndividualNode, const QList<cint64>& dependentNominalIdList, const QSet< QList< QSet<CConcept*>...` |
| 4 | 18786-18789 | `bool containsIndividualNodeConcept(CIndividualProcessNode*& testIndi, CConcept* conTest, bool* containsNegation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 14 | 18792-18805 | `bool containsIndividualNodeConcept(CReapplyConceptLabelSet* conLabelSet, CConcept* conTest, bool* containsNegation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 42 | 18808-18849 | `bool containsIndividualNodeConcepts(CReapplyConceptLabelSet* conLabelSet, CSortedNegLinker<CConcept*>* conTestLinkerIt, bool* containsNegation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 11 | 18852-18862 | `bool containsIndividualNodeConcepts(CReapplyConceptLabelSet* conLabelSet, CSortedNegLinker<CConcept*>* conTestLinkerIt, bool negated, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 18865-18868 | `bool containsIndividualNodeConcepts(CIndividualProcessNode*& testIndi, CSortedNegLinker<CConcept*>* conTestLinkerIt, bool negated, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 18870-18873 | `bool containsIndividualNodeConcepts(CIndividualProcessNode*& testIndi, CSortedNegLinker<CConcept*>* conTestLinkerIt, bool* containsNegation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 4 | 18876-18879 | `bool containsIndividualNodeConcepts(CIndividualProcessNode*& testIndi, CSortedNegLinker<CConcept*>* conTestLinkerIt, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 19543-19549 | `void addIndividualNodeCandidateForConcept(CIndividualProcessNode*& indi, CConceptDescriptor* conDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 17 | 19552-19568 | `void addIndividualNodeCandidateForConcept(CIndividualProcessNode*& indi, CSortedNegLinker<CConcept*>* concepts, bool negated, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 55 | 19634-19688 | `void propagateIndividualNodeModified(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 60 | 19699-19758 | `void pruneSuccessors(CIndividualProcessNode*& indi, CIndividualProcessNode* ancestorIndi, bool removeNominalLinks, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 6 | 20117-20122 | `bool hasAncestorIndividualNode(CIndividualProcessNode*& processIndi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 20125-20140 | `bool hasRoleSuccessorConcept(CIndividualProcessNode*& processIndi, CRole* role, CConcept* concept, bool conceptNegation, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 26 | 20142-20167 | `bool hasRoleSuccessorConcepts(CIndividualProcessNode*& processIndi, CRole* role, CSortedNegLinker<CConcept*>* conceptLinker, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 24 | 20170-20193 | `CIndividualProcessNode* getRoleSuccessorWithConcepts(CIndividualProcessNode*& processIndi, CRole* role, CSortedNegLinker<CConcept*>* conceptLinker, bool negate, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 41 | 20198-20238 | `bool hasDistinctRoleSuccessorConcepts(CIndividualProcessNode*& processIndi, CRole* role, CSortedNegLinker<CConcept*>* conceptLinker, bool negate, cint64 distinctCount, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 30 | 20241-20270 | `void createIndividualNodeDisjointRolesLinks(CIndividualProcessNode*& sourceIndi, CIndividualProcessNode*& destinationIndi, CSortedNegLinker<CRole*>* disjointRoleLinker, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBa...` |
| 22 | 20274-20295 | `void createIndividualNodeNegationLink(CIndividualProcessNode*& sourceIndi, CIndividualProcessNode*& destinationIndi, CRole* negationRole, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 68 | 21565-21632 | `CIndividualProcessNode* tryExtendFunctionalSuccessorIndividual(CIndividualProcessNode*& indi, CConceptDescriptor* conDes, CSortedNegLinker<CRole*>* roleLinkerIt, CRole* ancRole, CSortedNegLinker<CConcept*>* conceptLinkerIt, bool negate, ...` |
| 36 | 21635-21670 | `CIndividualProcessNode* createSuccessorIndividual(CIndividualProcessNode*& indi, CConceptDescriptor* conDes, CSortedNegLinker<CRole*>* roleLinkerIt, CRole* ancRole, CSortedNegLinker<CConcept*>* conceptLinkerIt, bool negate, CDependencyTr...` |
| 44 | 22143-22186 | `void createDistinctSuccessorIndividuals(CIndividualProcessNode*& indi, CConceptDescriptor* conDes, CPROCESSINGLIST<CIndividualProcessNode*>& indiList, CSortedNegLinker<CRole*>* roleLinkerIt, CRole* ancRole, CSortedNegLinker<CConcept*>* c...` |
| 36 | 22212-22247 | `CIndividualLinkEdge* createNewIndividualsLinks(CIndividualProcessNode*& indiSource, CIndividualProcessNode*& indiDestination, CSortedNegLinker<CRole*>* roleLinkerIt, CRole* ancRole, CDependencyTrackPoint* depTrackPoint, CCalculationAlgor...` |
| 19 | 22251-22269 | `void installIndividualNodeRoleLink(CIndividualProcessNode*& sourceIndi, CIndividualProcessNode*& destinationIndi, CIndividualLinkEdge* individualLink, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 21 | 22272-22292 | `CReapplyQueueIterator installIndividualNodeRoleLinkReapplied(CIndividualProcessNode*& sourceIndi, CIndividualProcessNode*& destinationIndi, CIndividualLinkEdge* individualLink, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 15 | 22355-22369 | `CIndividualLinkEdge* createNewIndividualsLink(CIndividualProcessNode*& indiCreator, CIndividualProcessNode*& indiSource, CIndividualProcessNode*& indiDestination, CRole* role, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmCo...` |
| 9 | 22401-22409 | `void createIndividualsDistinct(CIndividualProcessNode*& indiSource, CIndividualProcessNode*& indiDestination, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 18 | 22413-22430 | `void createIndividualsDistinct(CPROCESSINGLIST<CIndividualProcessNode*>& indiList, CDependencyTrackPoint* depTrackPoint, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 22433-22435 | `bool hasIndividualsLink(CIndividualProcessNode*& indiSource, CIndividualProcessNode*& indiDestination, CRole* role, bool locateable, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 20 | 22439-22458 | `CIndividualProcessNode* createNewEmptyIndividual(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 14 | 22462-22475 | `CIndividualProcessNode* createNewIndividual(CDependencyTrackPoint* depTrackPoint, bool dataNode, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 6 | 22477-22482 | `CIndividualProcessNode* getAvailableUpToDateIndividual(cint64 indiID, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 22485-22493 | `CIndividualProcessNode* getUpToDateIndividual(CIndividualProcessNode* indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 78 | 22506-22583 | `CIndividualProcessNode* getUpToDateIndividual(cint64 indiID, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 17 | 25707-25723 | `CAnsweringPropagationSteeringController* getPropagationSteeringController(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 26412-26414 | `CIndividualProcessNode* getLocalizedIndividual(cint64 indiID, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 26416-26444 | `CIndividualProcessNode* getLocalizedIndividual(CIndividualProcessNode* indi, bool updateIndividual, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 16 | 26446-26461 | `CIndividualProcessNode* getSuccessorIndividual(CIndividualProcessNode*& indi, CIndividualLinkEdge* link, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 14 | 26464-26477 | `CIndividualProcessNode* getLocalizedSuccessorIndividual(CIndividualProcessNode*& indi, CIndividualLinkEdge* link, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 26480-26488 | `CIndividualProcessNode* getAncestorIndividual(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 29 | 26725-26753 | `void addConceptToIndividual(CConcept* addingConcept, bool negate, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, bool allowPreprocessing, bool allowInitalization, CCalculationAlgorithmContextBase* calc...` |
| 26 | 26757-26782 | `CConceptDescriptor* addConceptToIndividualReturnConceptDescriptor(CConcept* addingConcept, bool negate, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, bool allowPreprocessing, bool allowInitalization, ...` |
| 3 | 26786-26788 | `void setIndividualNodeAncestorConnectionModified(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 7 | 26790-26796 | `void setIndividualNodeConceptLabelSetModified(CIndividualProcessNode*& indi, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 3 | 26800-26802 | `bool isIndividualNodeConceptLabelSetModified(CIndividualProcessNode*& indi, cint64 modTag, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 9 | 26809-26817 | `CConceptDescriptor* createConceptDescriptor(CCalculationAlgorithmContextBase* calcAlgContext)` |
| 5 | 26820-26824 | `void releaseConceptDescriptor(CConceptDescriptor* conDes, CCalculationAlgorithmContextBase* calcAlgContext)` |
| 41 | 26829-26869 | `void addConceptsToIndividual(CSortedNegLinker<CConcept*>* conceptAddLinkerIt, bool negate, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, bool allowPreprocessing, bool allowInitalization, cint64* conce...` |
| 97 | 26925-27021 | `bool insertConceptsToIndividualConceptSet(CConceptDescriptor* conceptDescriptor, CDependencyTrackPoint* dependencyTrackPoint, CIndividualProcessNode*& processIndi, CReapplyConceptLabelSet* conLabelSet, CCondensedReapplyQueueIterator* rea...` |
| 39 | 27026-27064 | `void addConceptsToIndividual(CConceptAssertionLinker* conceptAddLinkerIt, bool negate, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, bool allowPreprocessing, bool allowInitalization, cint64* conceptCo...` |
| 39 | 27068-27106 | `void addConceptsToIndividual(CXNegLinker<CConcept*>* conceptAddLinkerIt, bool negate, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, bool allowPreprocessing, bool allowInitalization, cint64* conceptCou...` |
| 39 | 27110-27148 | `void addConceptsToIndividual(CXSortedNegLinker<CConcept*>* conceptAddLinkerIt, bool negate, CIndividualProcessNode*& processIndi, CDependencyTrackPoint* dependencyTrackPoint, bool allowPreprocessing, bool allowInitalization, cint64* conc...` |

## Proposed port batching (parallel translation units)

36 units, each <= ~800 source lines, rule-families kept contiguous. Order a unit's methods by their cpp start line.

| Unit | family | methods | lines | cpp ranges |
|---:|---|---:|---:|---|
| 1 | Core processing loop / driver | 2 | 807 | 848-1657 |
| 2 | Core processing loop / driver | 3 | 654 | 2074-2825 |
| 3 | Core processing loop / driver | 15 | 781 | 8720-19899 |
| 4 | Core processing loop / driver | 17 | 492 | 19901-27551 |
| 5 | Expansion rules (apply*Rule, Automat*, ORBranching) | 15 | 752 | 9552-11157 |
| 6 | Expansion rules (apply*Rule, Automat*, ORBranching) | 8 | 768 | 11161-12675 |
| 7 | Expansion rules (apply*Rule, Automat*, ORBranching) | 12 | 796 | 12681-14097 |
| 8 | Expansion rules (apply*Rule, Automat*, ORBranching) | 10 | 788 | 14102-16259 |
| 9 | Expansion rules (apply*Rule, Automat*, ORBranching) | 6 | 552 | 16299-17283 |
| 10 | Reapply-queue management | 27 | 397 | 6252-27676 |
| 11 | Variable-binding / binding-propagation rules | 11 | 438 | 10617-12413 |
| 12 | Merge handling | 13 | 717 | 1686-15093 |
| 13 | Merge handling | 3 | 633 | 15097-15816 |
| 14 | Merge handling | 11 | 711 | 15820-21006 |
| 15 | Merge handling | 7 | 726 | 21010-26032 |
| 16 | Nominal handling | 24 | 779 | 2153-25500 |
| 17 | Nominal handling | 13 | 598 | 25891-23993 |
| 18 | Blocking (pairwise / label-optimized / dynamic) | 25 | 776 | 4049-9408 |
| 19 | Blocking (pairwise / label-optimized / dynamic) | 13 | 738 | 17698-19322 |
| 20 | Blocking (pairwise / label-optimized / dynamic) | 17 | 732 | 19326-27648 |
| 21 | Caching / backend-cache / saturation | 21 | 776 | 2100-6567 |
| 22 | Caching / backend-cache / saturation | 20 | 777 | 6865-23193 |
| 23 | Caching / backend-cache / saturation | 6 | 571 | 23282-23926 |
| 24 | Caching / backend-cache / saturation | 8 | 799 | 23995-24881 |
| 25 | Caching / backend-cache / saturation | 12 | 664 | 24889-27641 |
| 26 | Incremental expansion / compatibility | 20 | 651 | 2937-27584 |
| 27 | Neighbour / backend-cache node expansion | 12 | 611 | 6009-26278 |
| 28 | Dependency tracking | 54 | 794 | 2873-10121 |
| 29 | Dependency tracking | 27 | 830 | 10123-7896 |
| 30 | Clash processing | 18 | 475 | 4395-20932 |
| 31 | Generic helpers / accessors / label tests | 9 | 768 | 494-5178 |
| 32 | Generic helpers / accessors / label tests | 9 | 713 | 5193-8718 |
| 33 | Generic helpers / accessors / label tests | 14 | 753 | 9257-13801 |
| 34 | Generic helpers / accessors / label tests | 18 | 792 | 13804-18383 |
| 35 | Generic helpers / accessors / label tests | 35 | 770 | 18390-22493 |
| 36 | Generic helpers / accessors / label tests | 19 | 503 | 22506-27148 |

### Unit member lists

**Unit 1** (Core processing loop / driver, 2 methods, 807 lines):
  - `createCalculationAlgorithmContext` [848-854] (L7)
  - `handleTask` [858-1657] (L800)

**Unit 2** (Core processing loop / driver, 3 methods, 654 lines):
  - `continueIndividualProcessing` [2074-2094] (L21)
  - `takeNextProcessIndividual` [2190-2790] (L601)
  - `analyzeCompletionGraphStatistics` [2794-2825] (L32)

**Unit 3** (Core processing loop / driver, 15 methods, 781 lines):
  - `initialNodeInitialize` [8720-9038] (L319)
  - `individualNodeInitializing` [9061-9169] (L109)
  - `individualNodeConclusion` [9480-9494] (L15)
  - `tableauRuleProcessing` [9496-9519] (L24)
  - `tableauRuleChoice` [9522-9549] (L28)
  - `initializeORProcessing` [16396-16430] (L35)
  - `planORProcessing` [16493-16664] (L172)
  - `prepareBranchedTaskProcessing` [17201-17203] (L3)
  - `getLinkProcessingRestriction` [17286-17294] (L9)
  - `propagateProcessingRestrictionToAncestor` [19762-19764] (L3)
  - `propagateAddingProcessingRestrictionToAncestor` [19767-19778] (L12)
  - `propagateProcessingRestrictionToSuccessors` [19783-19785] (L3)
  - `propagateAddingProcessingRestrictionToSuccessors` [19810-19827] (L18)
  - `propagateClearingProcessingRestrictionToSuccessors` [19831-19848] (L18)
  - `propagateIndividualProcessedAndReactivate` [19887-19899] (L13)

**Unit 4** (Core processing loop / driver, 17 methods, 492 lines):
  - `searchReactivateIndividualsProcessedPropagated` [19901-19956] (L56)
  - `propagateIndividualUnprocessed` [19958-19964] (L7)
  - `propagateIndividualUnprocessed` [19968-19992] (L25)
  - `addConceptToIndividualSkipANDProcessing` [26692-26722] (L31)
  - `insertConceptProcessDescriptorToProcessingQueue` [27152-27164] (L13)
  - `insertConceptProcessDescriptorToProcessingQueue` [27166-27182] (L17)
  - `addConceptToProcessingQueue` [27185-27200] (L16)
  - `needsProcessingForConcept` [27203-27213] (L11)
  - `addConceptPreprocessedToProcessingQueue` [27216-27225] (L10)
  - `addConceptPreprocessedToProcessingQueue` [27228-27273] (L46)
  - `addConceptToProcessingQueue` [27278-27281] (L4)
  - `addCopiedConceptToProcessingQueue` [27284-27307] (L24)
  - `addConceptRestrictedToProcessingQueue` [27311-27322] (L12)
  - `addConceptRestrictedToProcessingQueue` [27325-27341] (L17)
  - `addConceptRestrictedFixedPriorityToProcessingQueue` [27345-27356] (L12)
  - `addIndividualToProcessingQueueBasedOnProcessingConcepts` [27359-27416] (L58)
  - `addIndividualToProcessingQueue` [27419-27551] (L133)

**Unit 5** (Expansion rules (apply*Rule, Automat*, ORBranching), 15 methods, 752 lines):
  - `applyNegAutomatChooseRule` [9552-9554] (L3)
  - `applyNegANDRule` [9556-9558] (L3)
  - `applyNegSOMERule` [9560-9562] (L3)
  - `applyNegALLRule` [9564-9566] (L3)
  - `applyNegORRule` [9568-9570] (L3)
  - `applyNegATMOSTRule` [9573-9575] (L3)
  - `applyNegATLEASTRule` [9577-9579] (L3)
  - `applyAutomatChooseRule` [9583-9603] (L21)
  - `applyAutomatANDRule` [9606-9613] (L8)
  - `applyAutomatTransactions` [9634-9752] (L119)
  - `applyREPRESENTATIVEGROUNDINGRule` [10310-10364] (L55)
  - `applyREPRESENTATIVEJOINRule` [10366-10614] (L249)
  - `applyREPRESENTATIVEBINDVARIABLERule` [10803-10923] (L121)
  - `applyREPRESENTATIVEIMPLICATIONRule` [10927-11047] (L121)
  - `applyREPRESENTATIVEALLRule` [11121-11157] (L37)

**Unit 6** (Expansion rules (apply*Rule, Automat*, ORBranching), 8 methods, 768 lines):
  - `applyREPRESENTATIVEANDRule` [11161-11232] (L72)
  - `applyVARIABLEBINDINGANDRule` [11514-11578] (L65)
  - `applyVARBINDPROPAGATEALLRule` [11833-11869] (L37)
  - `applyVARBINDVARIABLERule` [11874-11998] (L125)
  - `applyVARBINDPROPAGATEJOINRule` [12002-12220] (L219)
  - `applyVARBINDPROPAGATEGROUNDINGRule` [12418-12478] (L61)
  - `applyVARBINDPROPAGATEIMPLICATIONRule` [12481-12586] (L106)
  - `applyVARBINDPREPARERule` [12593-12675] (L83)

**Unit 7** (Expansion rules (apply*Rule, Automat*, ORBranching), 12 methods, 796 lines):
  - `applyVARBINDFINALIZERule` [12681-12725] (L45)
  - `applyBINDPROPAGATEGROUNDINGRule` [12828-13040] (L213)
  - `applyBINDPROPAGATECYCLERule` [13048-13288] (L241)
  - `applyBINDPROPAGATEALLRule` [13467-13503] (L37)
  - `applyBINDPROPAGATEIMPLICATIONRule` [13510-13610] (L101)
  - `applyBINDPROPAGATEANDRule` [13614-13616] (L3)
  - `applyBINDPROPAGATEANDFLAGALLRule` [13620-13623] (L4)
  - `applyBINDVARIABLERule` [13694-13769] (L76)
  - `applyDATATYPERule` [14009-14031] (L23)
  - `applyDATARESTRICTIONRule` [14037-14053] (L17)
  - `applyDATALITERALRule` [14058-14077] (L20)
  - `applyDATALITERALIMPLICATIONRule` [14082-14097] (L16)

**Unit 8** (Expansion rules (apply*Rule, Automat*, ORBranching), 10 methods, 788 lines):
  - `applyDATATYPEIMPLICATIONRule` [14102-14117] (L16)
  - `applyDATARESTRICTIONIMPLICATIONRule` [14123-14135] (L13)
  - `applyBOTTOMRule` [14138-14152] (L15)
  - `applyANDRule` [14156-14171] (L16)
  - `applySOMERule` [14215-14402] (L188)
  - `applyVALUERule` [14608-14685] (L78)
  - `applyFUNCTIONALRule` [14689-14820] (L132)
  - `applyATMOSTRule` [14861-15006] (L146)
  - `applyATLEASTRule` [16068-16153] (L86)
  - `applyNOMINALRule` [16162-16259] (L98)

**Unit 9** (Expansion rules (apply*Rule, Automat*, ORBranching), 6 methods, 552 lines):
  - `applyALLRule` [16299-16393] (L95)
  - `executeORBranching` [16741-17010] (L270)
  - `applyORRule` [17022-17052] (L31)
  - `applyIMPLICATIONRule` [17056-17122] (L67)
  - `applyNOMINALIMPLICATIONRule` [17130-17177] (L48)
  - `applySELFRule` [17243-17283] (L41)

**Unit 10** (Reapply-queue management, 27 methods, 397 lines):
  - `reapplySatisfiableCachedAbsorbedDisjunctionConcepts` [6252-6272] (L21)
  - `reapplySatisfiableCachedAbsorbedGeneratingConcepts` [6275-6294] (L20)
  - `reapplyConceptUpdatedRepresentative` [11236-11245] (L10)
  - `reapplyConceptUpdatedRepresentative` [11248-11257] (L10)
  - `applyReapplyQueueConcepts` [13876-13897] (L22)
  - `collectReapplyAutomatTransactionsRestrictions` [22019-22049] (L31)
  - `createNewIndividualsLinksReapplyed` [22295-22352] (L58)
  - `createNewIndividualsLinkReapplyed` [22372-22398] (L27)
  - `applyExtendedReapplyConceptDescriptor` [26492-26519] (L28)
  - `applyReapplyQueueConcepts` [26523-26547] (L25)
  - `applyReapplyQueueConcepts` [26549-26569] (L21)
  - `applyReapplyQueueConceptsRestricted` [26572-26599] (L28)
  - `applyReapplyQueueConcepts` [26602-26621] (L20)
  - `addConceptToReapplyQueue` [26625-26629] (L5)
  - `addConceptToReapplyQueue` [26632-26640] (L9)
  - `addConceptToReapplyQueue` [26642-26650] (L9)
  - `addConceptToReapplyQueue` [26653-26661] (L9)
  - `addConceptToReapplyQueue` [26663-26671] (L9)
  - `isConceptInReapplyQueue` [26674-26680] (L7)
  - `isConceptInReapplyQueue` [26682-26688] (L7)
  - `getAppliedANDRuleCount` [27650-27652] (L3)
  - `getAppliedORRuleCount` [27654-27656] (L3)
  - `getAppliedSOMERuleCount` [27658-27660] (L3)
  - `getAppliedATLEASTRuleCount` [27662-27664] (L3)
  - `getAppliedALLRuleCount` [27666-27668] (L3)
  - `getAppliedATMOSTRuleCount` [27670-27672] (L3)
  - `getAppliedTotalRuleCount` [27674-27676] (L3)

**Unit 11** (Variable-binding / binding-propagation rules, 11 methods, 438 lines):
  - `hasCommonVariableBindings` [10617-10647] (L31)
  - `propagateInitialVariableBindings` [11581-11609] (L29)
  - `propagateFreshVariableBindings` [11612-11666] (L55)
  - `propagateVariableBindingsToSuccessor` [11671-11734] (L64)
  - `propagateInitialVariableBindingsToSuccessor` [11741-11769] (L29)
  - `propagateFreshVariableBindingsToSuccessor` [11774-11830] (L57)
  - `propagateVariableBindingsJoins` [12226-12285] (L60)
  - `createVariableBindingPathKey` [12291-12317] (L27)
  - `triggerVariableBindingPathJoining` [12321-12336] (L16)
  - `forceVariableBindingJoinCreated` [12341-12349] (L9)
  - `getJoinedVariableBindingPath` [12353-12413] (L61)

**Unit 12** (Merge handling, 13 methods, 717 lines):
  - `findNextPossibleInstanceMergingIndividual` [1686-1700] (L15)
  - `findNextPossibleInstanceMergingIndividual` [1704-1878] (L175)
  - `tryPossibleInstanceMerging` [1885-2023] (L139)
  - `incrementalMergeWithPreviousNondeterministicCompletionGraph` [3102-3242] (L141)
  - `incrementalMergeWithPreviousDeterministicCompletionGraph` [3250-3372] (L123)
  - `createMERGEDCONCEPTDependency` [10057-10063] (L7)
  - `createMERGEDLINKDependency` [10065-10071] (L7)
  - `createMERGEDINDIVIDUALDependency` [10074-10080] (L7)
  - `createMERGEDependency` [10131-10137] (L7)
  - `createMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode` [10157-10163] (L7)
  - `createSAMEINDIVIDUALMERGEDependency` [10219-10225] (L7)
  - `generateDebugMergingQueueString` [15009-15040] (L32)
  - `mergeMergingIndividualNodesPairwise` [15044-15093] (L50)

**Unit 13** (Merge handling, 3 methods, 633 lines):
  - `mergeMergingIndividualNodes` [15097-15526] (L430)
  - `createMergeBranchingTask` [15611-15673] (L63)
  - `qualifyMergingIndividualNodes` [15677-15816] (L140)

**Unit 14** (Merge handling, 11 methods, 711 lines):
  - `initializeMergingIndividualNodes` [15820-16063] (L244)
  - `getCorrectedMergedIntoIndividualNode` [16264-16270] (L7)
  - `createIndividualMergeCausingDescriptors` [16690-16713] (L24)
  - `isIndividualNodesMergeableWithoutNewRuleApplications` [20481-20639] (L159)
  - `expandBackendCacheIndividualNodesNominalMerging` [20644-20651] (L8)
  - `expandBackendCacheIndividualNodesNominalMergingNeighbouringConnections` [20655-20710] (L56)
  - `isIndividualNodesMergeable` [20714-20751] (L38)
  - `areIndividualNodesDisjointRolesMergeable` [20754-20764] (L11)
  - `isIndividualNodeDisjointRolesMergeable` [20767-20863] (L97)
  - `getMergedIndividualNodes` [20936-20985] (L50)
  - `getIntoEmptyMergedIndividualNode` [20990-21006] (L17)

**Unit 15** (Merge handling, 7 methods, 726 lines):
  - `mergeIndividualNodeInto` [21010-21562] (L553)
  - `visitIndividualsRelevantMergingsBackendSynchronisationDataIndividuals` [23036-23083] (L48)
  - `visitNewlyMergedIndividualsBackendSynchronisationData` [23089-23110] (L22)
  - `visitNewlyMergedIndividualsBackendSynchronisationData` [23118-23142] (L25)
  - `visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData` [23144-23155] (L12)
  - `testIndividualNodeBackendCacheNewMergings` [25849-25888] (L40)
  - `testIndividualNodeBackendCacheSameMergedBlockingCritical` [26007-26032] (L26)

**Unit 16** (Nominal handling, 24 methods, 779 lines):
  - `checkIndividualNodesReactivationDueToNominalCachingLoss` [2153-2159] (L7)
  - `reactivateIndividualNodesDueToNominalCachingLoss` [2161-2181] (L21)
  - `identifyCompatibilityChangedNominalIndividualNodes` [3441-3468] (L28)
  - `generateDebugDependentNominalsString` [7999-8010] (L12)
  - `getDelayProcessingBlockingNominalNode` [9413-9436] (L24)
  - `tryDelayNominalProcessing` [9441-9463] (L23)
  - `canDelayNominalProcessing` [9467-9476] (L10)
  - `checkBackendCachedNominalConnection` [14545-14605] (L61)
  - `isNominalIndividualNodeAvailable` [16274-16277] (L4)
  - `getCorrectedNominalIndividualNode` [16280-16294] (L15)
  - `isLabelConceptSubSetIgnoreNominals` [17396-17460] (L65)
  - `isLabelConceptEqualSetConsiderNominalsForClashOnly` [17580-17636] (L57)
  - `isNominalVariablePropagationBindingSubSet` [17732-17970] (L239)
  - `propagateIndividualNodeNewNominalConnectionToAncestors` [20303-20305] (L3)
  - `propagateIndividualNodeNominalConnectionToAncestors` [20308-20310] (L3)
  - `propagateIndividualNodeNominalConnectionFlagsToAncestors` [20313-20365] (L53)
  - `propagateIndividualNodeNominalConnectionStatusToAncestors` [20368-20403] (L36)
  - `propagateIndividualNodeConnectedNominalToAncestors` [20406-20460] (L55)
  - `propagateIndividualNodeNeighboursNominalConnectionToAncestors` [20464-20474] (L11)
  - `createNominalsSuccessorIndividuals` [22192-22206] (L15)
  - `createNewTemporaryNominalIndividual` [22497-22504] (L8)
  - `getLocalizedForcedBackendInitializedNominalIndividualNode` [25468-25471] (L4)
  - `getLocalizedForcedBackendInitializedNominalIndividualNode` [25473-25490] (L18)
  - `getForcedInitializedNominalIndividualNode` [25494-25500] (L7)

**Unit 17** (Nominal handling, 13 methods, 598 lines):
  - `testIndividualNodeBackendCacheNominalIndirectConnectionBlockingCritical` [25891-26001] (L111)
  - `checkValueSpaceDistinctSatisfiability` [9172-9212] (L41)
  - `triggerValueSpaceConcepts` [9215-9231] (L17)
  - `addtriggeredValueSpaceConcepts` [9236-9254] (L19)
  - `createDATAASSERTIONDependency` [10033-10039] (L7)
  - `getRepresentativeJoiningKeyData` [10771-10799] (L29)
  - `addDataAssertion` [14457-14492] (L36)
  - `tryInitalizingFromSaturatedData` [21737-21852] (L116)
  - `tryExpansionFromSaturatedData` [22081-22140] (L60)
  - `loadIndividualNodeDataFromBackendCache` [22618-22696] (L79)
  - `visitIndividualsRelevantBackendSynchronisationDataIndividuals` [22988-23025] (L38)
  - `getBackendSynchronizationFilledRoleNeighbourExpansionDataHash` [23738-23772] (L35)
  - `getLocalizedIndividualBackendCacheSnychronisationData` [23984-23993] (L10)

**Unit 18** (Blocking (pairwise / label-optimized / dynamic), 25 methods, 776 lines):
  - `testCompletionGraphCachingAndBlocking` [4049-4094] (L46)
  - `isIndividualNodeValidBlocker` [4193-4206] (L14)
  - `isIndividualNodeBackendCacheSynchronizationProcessingBlocked` [4216-4227] (L12)
  - `isSaturationCachedProcessingBlocked` [4739-4747] (L9)
  - `isSatisfiableCachedProcessingBlocked` [4822-4830] (L9)
  - `upgradeSignatureBlockingToIndividualReusing` [5181-5190] (L10)
  - `addReusingBlockerFollowing` [5303-5314] (L12)
  - `removeReusingBlockerFollowing` [5317-5328] (L12)
  - `isSignatureBlockedProcessingBlocked` [5331-5339] (L9)
  - `testAlternativeBlocked` [5344-5381] (L38)
  - `detectIndividualNodeSignatureBlockingStatus` [5385-5468] (L84)
  - `addSignatureBlockingBlockerFollowing` [5472-5483] (L12)
  - `removeSignatureBlockingBlockerFollowing` [5486-5497] (L12)
  - `rebuildSignatureBlockingCandidateHash` [5502-5534] (L33)
  - `searchSignatureIndividualNodeBlocker` [5537-5583] (L47)
  - `addSignatureIndividualNodeBlockerCandidate` [5589-5609] (L21)
  - `establishIndividualNodeSignatureBlocking` [5612-5680] (L69)
  - `refreshIndividualNodeSignatureBlocking` [5685-5772] (L88)
  - `updateBlockingReviewMarking` [5776-5842] (L67)
  - `updateSignatureBlockingConceptExpansion` [5846-5955] (L110)
  - `isConceptSignatureBlockingCritical` [6098-6108] (L11)
  - `propagateIndirectSuccessorSignatureBlocked` [6317-6319] (L3)
  - `propagateIndirectSuccessorReuseBlocked` [6326-6328] (L3)
  - `reactivateIndirectSignatureBlockedSuccessors` [6505-6524] (L20)
  - `eliminiateBlockedIndividuals` [9384-9408] (L25)

**Unit 19** (Blocking (pairwise / label-optimized / dynamic), 13 methods, 738 lines):
  - `hasOptimizedBlockingB2AutomateTransitionOperands` [17698-17726] (L29)
  - `isLabelConceptOptimizedBlocking` [18488-18781] (L294)
  - `isLabelConceptSubSetBlocking` [18882-18893] (L12)
  - `isLabelConceptEqualBlocking` [18896-18901] (L6)
  - `isLabelConceptEqualPairwiseBlocking` [18904-18924] (L21)
  - `isIndividualNodeBlocking` [18927-18986] (L60)
  - `detectIndividualNodeBlockedStatus` [18991-19118] (L128)
  - `getBlockingIndividualNode` [19121-19136] (L16)
  - `continueIndividualNodeBlock` [19139-19167] (L29)
  - `signatureCachedIndividualNodeBlock` [19172-19189] (L18)
  - `clearBlockingCache` [19193-19195] (L3)
  - `getAncestorBlockingIndividualNode` [19199-19248] (L50)
  - `getAnywhereBlockingIndividualNode` [19251-19322] (L72)

**Unit 20** (Blocking (pairwise / label-optimized / dynamic), 17 methods, 732 lines):
  - `getAnywhereBlockingIndividualNodeLinkedCanidateHashed` [19326-19463] (L138)
  - `getAnywhereBlockingIndividualNodeCanidateHashed` [19467-19539] (L73)
  - `getBlockingIndividualNodeCandidateIterator` [19571-19625] (L55)
  - `propagateIndirectSuccessorBlocking` [19690-19693] (L4)
  - `propagateAddingBlockedProcessingRestrictionToSuccessors` [19789-19807] (L19)
  - `reactivateIndirectBlockedSuccessors` [19851-19868] (L18)
  - `reactivateBlockedIndividuals` [19871-19884] (L14)
  - `isIndividualNodeProcessingBlocked` [19997-20039] (L43)
  - `isIndividualNodeExpansionBlocked` [20042-20045] (L4)
  - `needsIndividualNodeExpansionBlockingTest` [20049-20107] (L59)
  - `propagateIndirectSuccessorSaturationBlocked` [21861-21863] (L3)
  - `tryEstablishExpansionBlockingWithBackendCacheSynchronisation` [22587-22611] (L25)
  - `testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality` [23196-23276] (L81)
  - `testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical` [26037-26173] (L137)
  - `testIndividualNodeConceptBackendCacheNeighbourExpansionBlockingCritical` [26177-26203] (L27)
  - `addBlockingCoreConcept` [26871-26896] (L26)
  - `addIndividualToBlockingUpdateReviewProcessingQueue` [27643-27648] (L6)

**Unit 21** (Caching / backend-cache / saturation, 21 methods, 776 lines):
  - `installSaturationCachingReactivation` [2100-2126] (L27)
  - `tryInstallSaturationCachingReactivation` [2130-2149] (L20)
  - `isIndividualNodeCompletionGraphCached` [4210-4213] (L4)
  - `detectIndividualNodeBackendCacheSynchronized` [4230-4280] (L51)
  - `clearCompletionGraphCaching` [4284-4314] (L31)
  - `detectIndividualNodeCompletionGraphCached` [4317-4344] (L28)
  - `commitCacheMessages` [4350-4359] (L10)
  - `testIndividualNodeUnsatisfiableCached` [4363-4392] (L30)
  - `cacheSatisfiableIndividualNodes` [4503-4625] (L123)
  - `testAllSuccessorsProcessedAndWriteSatisfiableCache` [4670-4703] (L34)
  - `writeSatisfiableCachedIndividualNodesOfUnsatisfiableBranch` [4706-4734] (L29)
  - `detectIndividualNodeSaturationCached` [4750-4817] (L68)
  - `detectIndividualNodeSatisfiableExpandedCached` [4833-4949] (L117)
  - `addSatisfiableCachedAbsorbedDisjunctionConcept` [6298-6304] (L7)
  - `addSatisfiableCachedAbsorbedGeneratingConcept` [6308-6314] (L7)
  - `propagateIndirectSuccessorSatisfiableCached` [6321-6323] (L3)
  - `isSatisfiableCachedAutomatConceptCompatible` [6332-6356] (L25)
  - `isSatisfiableCachedCompatible` [6359-6420] (L62)
  - `expandCachedConcepts` [6423-6482] (L60)
  - `reactivateIndirectSatisfiableCachedSuccessors` [6527-6546] (L20)
  - `reactivateIndirectSaturationCachedSuccessors` [6548-6567] (L20)

**Unit 22** (Caching / backend-cache / saturation, 20 methods, 777 lines):
  - `rootUnsatisfiabilityWriteCaches` [6865-6897] (L33)
  - `addIndividualNodeForCacheUnsatisfiableRetrieval` [7391-7396] (L6)
  - `writeClashDescriptorsToCache` [7400-7408] (L9)
  - `writeClashDescriptorsToCache` [7412-7423] (L12)
  - `writeClashDescriptorsToCache` [7426-7542] (L117)
  - `addCachedComputedTypes` [9042-9057] (L16)
  - `isGeneratingConceptSatisfiableCachedAbsorpable` [14175-14211] (L37)
  - `hasSaturatedClashedFlagForConcept` [16438-16459] (L22)
  - `getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindingsCached` [18088-18098] (L11)
  - `tryEstablishSaturationCaching` [21674-21723] (L50)
  - `validateSaturationCachingPossible` [21866-21911] (L46)
  - `getCreationSuccessorSaturationNode` [21917-22013] (L97)
  - `getSaturationResolvedIndividualNodeExtension` [22054-22075] (L22)
  - `initializeIndividualNodeWithBackendCache` [22702-22814] (L113)
  - `getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher` [22817-22823] (L7)
  - `getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher` [22825-22829] (L5)
  - `markIndividualNodeBackendNonConceptSetRelatedProcessing` [22831-22909] (L79)
  - `tryDelayIndividualNodeInitializationWithBackendConceptSetLabel` [22921-22966] (L46)
  - `registerProcessedIndividualForBackendConceptSetLabel` [22971-22984] (L14)
  - `getBackendCacheRoleRepresentativeNeighbourCount` [23159-23193] (L35)

**Unit 23** (Caching / backend-cache / saturation, 6 methods, 571 lines):
  - `expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache` [23282-23328] (L47)
  - `expandIndirectCompatibleRequiredIndividualNeighbourNodesFromBackendCache` [23335-23595] (L261)
  - `expandIndividualInferringNeighboursFromBackendCache` [23603-23657] (L55)
  - `expandIndividualAllNeighboursFromBackendCache` [23663-23731] (L69)
  - `expandIndividualNeighbourNodeFromBackendCache` [23782-23812] (L31)
  - `expandIndividualNeighbourNodeFromBackendCache` [23819-23926] (L108)

**Unit 24** (Caching / backend-cache / saturation, 8 methods, 799 lines):
  - `expandDirectlyInfluencedIndividualNeighbourNodesFromBackendCache` [23995-24438] (L444)
  - `queuedIndividualBackendNeighbourExpansion` [24443-24632] (L190)
  - `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing` [24706-24711] (L6)
  - `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessingForDisjointRoles` [24715-24725] (L11)
  - `markIndividualNodeBackendNonConceptSetRelatedProcessingForDisjointRoles` [24727-24734] (L8)
  - `markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessingForDisjointRoles` [24736-24743] (L8)
  - `markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessing` [24745-24797] (L53)
  - `prepareBackendExpansionReuseBranching` [24803-24881] (L79)

**Unit 25** (Caching / backend-cache / saturation, 12 methods, 664 lines):
  - `prepareBackendIndividualFixedReuseExpansion` [24889-24913] (L25)
  - `prepareBackendIndividualPrioritizedReuseExpansion` [24916-25003] (L88)
  - `checkIndividualBackendExpansionReuseable` [25010-25086] (L77)
  - `reuseIndividualBackendExpansion` [25092-25373] (L282)
  - `testIndividualNodeBackendCacheConceptsSynchronization` [26283-26362] (L80)
  - `validateBackendSynchronisationContinued` [26368-26407] (L40)
  - `isConceptUnsatisfiabilitySaturated` [26900-26921] (L22)
  - `addIndividualToBackendSynchronisationRetestQueue` [27587-27596] (L10)
  - `addIndividualToBackendDirectInfluenceExpansionQueue` [27598-27607] (L10)
  - `addIndividualToBackendIndirectCompatibilityExpansionQueue` [27609-27618] (L10)
  - `addIndividualToBackendReuseExpansionQueue` [27621-27630] (L10)
  - `addIndividualToBackendNeighbourExpansionQueue` [27632-27641] (L10)

**Unit 26** (Incremental expansion / compatibility, 20 methods, 651 lines):
  - `initializeIncrementalIndividualExpansion` [2937-3052] (L116)
  - `getNextIncrementalExpansionIndividual` [3058-3071] (L14)
  - `incrementalNodeExpansion` [3075-3084] (L10)
  - `requiresIncrementalNodeExpansion` [3088-3094] (L7)
  - `pruneIncrementalRemovedSuccessors` [3384-3431] (L48)
  - `checkCompatibilityUpdateDirectlyChangedPropagation` [3476-3493] (L18)
  - `linkCreationDirectlyChangedNeighbourConnectionUpdate` [3497-3508] (L12)
  - `establishDirectlyChangedNeighbourConnection` [3512-3529] (L18)
  - `propagateDirectlyChangedNeighbourNodeConnection` [3534-3634] (L101)
  - `searchDirectlyChangedNeighbourNodeConnection` [3639-3702] (L64)
  - `clearDirectlyChangedNeighbourConnection` [3706-3718] (L13)
  - `clearPropagatedDirectlyChangedNeighbourConnection` [3722-3761] (L40)
  - `hasCompatibleConceptSetReuse` [4955-4972] (L18)
  - `hasCompatibleConceptSetSignature` [5960-6004] (L45)
  - `generateDebugIncrementalExpansionString` [8014-8036] (L23)
  - `areVariablePropagationBindingsCompatible` [17990-18013] (L24)
  - `getConceptsForCompatibleVariablePropagationBindings` [18017-18050] (L34)
  - `getBindingsCompatibleConceptSetsHashValue` [18262-18277] (L16)
  - `addIndividualToIncrementalCompatibilityCheckingQueue` [27554-27563] (L10)
  - `addIndividualToIncrementalExpansionQueue` [27565-27584] (L20)

**Unit 27** (Neighbour / backend-cache node expansion, 12 methods, 611 lines):
  - `anlyzeIndiviudalNodesConceptExpansion` [6009-6095] (L87)
  - `expandIndirectlyConnectedIndividuals` [23930-23977] (L48)
  - `canDelayRepresentativeNeighbourExpansion` [24645-24679] (L35)
  - `delayingRepresentativeNeighbourExpansion` [24683-24700] (L18)
  - `ensurePropagationCutLinksToExpandedIndividual` [25379-25427] (L49)
  - `expandDirectlyInfluencedNeighboursWithPropagation` [25503-25539] (L37)
  - `ensureBaseLinkExpansion` [25547-25573] (L27)
  - `initializeNeighbourExpansionWithPropagation` [25577-25702] (L126)
  - `isNeighbourExpansionWithPropagationAllowed` [25727-25742] (L16)
  - `canExpansionPotentiallyInfluenceNeighbourWithPotentialPropagation` [25745-25797] (L53)
  - `canExpandDirectlyInfluencedNeighbourWithPropagation` [25801-25845] (L45)
  - `debugCheckDirectlyInfluencedNeighbourWithPropagationPossible` [26209-26278] (L70)

**Unit 28** (Dependency tracking, 54 methods, 794 lines):
  - `areAllDependentFactsUnchanged` [2873-2932] (L60)
  - `trackIndividualReferredDependence` [3871-3873] (L3)
  - `trackIndividualExtendedDependence` [3876-3878] (L3)
  - `trackIndividualDependence` [3880-3945] (L66)
  - `isConceptFromPredecessorDependent` [4032-4046] (L15)
  - `isConceptFromDirectOrPredecessorOrNondeterminismusDependent` [6112-6140] (L29)
  - `getConceptDependenciesToSameIndividualNode` [6144-6247] (L104)
  - `writeDebugTrackingLineStringToFile` [6723-6739] (L17)
  - `generateDebugTrackingLineString` [6744-6770] (L27)
  - `markDependencyRelevance` [7360-7388] (L29)
  - `initializeTrackingLine` [7900-7917] (L18)
  - `getCoresspondingIndividualNodeFromDependency` [7975-7978] (L4)
  - `getCoresspondingIndividualNodeFromDependency` [7981-7995] (L15)
  - `generateDebugDependencyString` [8175-8298] (L124)
  - `createREPRESENTATIVEGROUNDINGDependency` [9755-9761] (L7)
  - `createREPRESENTATIVEJOINDependency` [9763-9769] (L7)
  - `createREPRESENTATIVEBINDVARIABLEDependency` [9771-9777] (L7)
  - `createREPRESENTATIVEIMPLICATIONDependency` [9779-9785] (L7)
  - `createREPRESENTATIVEALLDependency` [9787-9793] (L7)
  - `createREPRESENTATIVEANDDependency` [9795-9801] (L7)
  - `createRESOLVEREPRESENTATIVEDependency` [9803-9809] (L7)
  - `createPROPAGATEVARIABLECONNECTIONDependency` [9820-9826] (L7)
  - `createVARBINDPROPAGATEIMPLICATIONDependency` [9828-9834] (L7)
  - `createVARBINDPROPAGATEGROUNDINGDependency` [9836-9842] (L7)
  - `createVARBINDPROPAGATEALLDependency` [9844-9850] (L7)
  - `createVARBINDPROPAGATEANDDependency` [9852-9858] (L7)
  - `createPROPAGATEVARIABLEBINDINGDependency` [9860-9866] (L7)
  - `createPROPAGATEVARIABLEBINDINGSSUCCESSORDependency` [9868-9874] (L7)
  - `createVARBINDVARIABLEDependency` [9876-9882] (L7)
  - `createVARBINDPROPAGATEJOINDependency` [9884-9890] (L7)
  - `createBINDPROPAGATEGROUNDINGDependency` [9897-9903] (L7)
  - `createPROPAGATECONNECTIONAWAYDependency` [9905-9911] (L7)
  - `createPROPAGATECONNECTIONDependency` [9913-9919] (L7)
  - `createBINDPROPAGATECYCLEDependency` [9921-9927] (L7)
  - `createBINDPROPAGATEALLDependency` [9929-9935] (L7)
  - `createPROPAGATEBINDINGSSUCCESSORDependency` [9937-9943] (L7)
  - `createBINDPROPAGATEIMPLICATIONDependency` [9945-9951] (L7)
  - `createANDDependency` [9953-9959] (L7)
  - `createBINDPROPAGATEANDDependency` [9961-9967] (L7)
  - `createPROPAGATEBINDINGDependency` [9969-9975] (L7)
  - `createBINDVARIABLEDependency` [9977-9983] (L7)
  - `createNOMINALDependency` [9985-9991] (L7)
  - `createAUTOMATCHOOSEDependency` [9993-9999] (L7)
  - `createSOMEDependency` [10001-10007] (L7)
  - `createSELFDependency` [10009-10015] (L7)
  - `createVALUEDependency` [10017-10023] (L7)
  - `createROLEASSERTIONDependency` [10025-10031] (L7)
  - `createNEGVALUEDependency` [10041-10047] (L7)
  - `createALLDependency` [10049-10055] (L7)
  - `createFUNCTIONALDependency` [10083-10089] (L7)
  - `createDISTINCTDependency` [10091-10097] (L7)
  - `createAUTOMATTRANSACTIONDependency` [10099-10105] (L7)
  - `createATLEASTDependency` [10107-10113] (L7)
  - `createORDependency` [10115-10121] (L7)

**Unit 29** (Dependency tracking, 27 methods, 830 lines):
  - `createATMOSTDependency` [10123-10129] (L7)
  - `createREUSEINDIVIDUALDependency` [10139-10145] (L7)
  - `createREUSECOMPLETIONGRAPHDependency` [10147-10153] (L7)
  - `createREUSECONCEPTSDependency` [10165-10171] (L7)
  - `createQUALIFYDependency` [10173-10179] (L7)
  - `createORONLYOPTIONDependency` [10183-10189] (L7)
  - `createIMPLICATIONDependency` [10192-10198] (L7)
  - `createEXPANDEDDependency` [10201-10207] (L7)
  - `createCONNECTIONDependency` [10210-10216] (L7)
  - `createREUSEBACKENDEXPANSIONMODESDependency` [10230-10236] (L7)
  - `createREUSEBACKENDFIXEDINDIVIDUALEXPANSIONDependency` [10239-10245] (L7)
  - `createREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDependency` [10248-10254] (L7)
  - `createREUSEBACKENDVALUEDependency` [10259-10265] (L7)
  - `createNonDeterministicDependencyTrackPointBranch` [16669-16685] (L17)
  - `createDependendBranchingTaskList` [17182-17198] (L17)
  - `hasNondeterministicDependency` [23027-23033] (L7)
  - `clashedBacktracking` [6774-6861] (L88)
  - `backtrackFromTrackingLine` [6963-6974] (L12)
  - `backtrackFromTrackingLineStep` [6976-7073] (L98)
  - `backtrackNonDeterministicBranchingClashedDescriptorFromCurrentIndividualNodeLevel` [7075-7077] (L3)
  - `backtrackNonDeterministicBranchingClashedDescriptorFromPreviousIndividualNodeLevel` [7080-7082] (L3)
  - `backtrackNonDeterministicBranchingClashedDescriptor` [7085-7349] (L265)
  - `backtrackDeterministicBranchingClashedDescriptorFromCurrentIndividualNodeLevel` [7655-7665] (L11)
  - `backtrackDeterministicClashedDescriptorFromPreviousIndividualNodeLevels` [7669-7674] (L6)
  - `getBacktrackedDeterministicClashedDescriptorsBeforeProcessingTag` [7677-7772] (L96)
  - `getBacktrackedDeterministicClashedDescriptors` [7779-7863] (L85)
  - `tryGetInvalidSameIndividualNodeLevelBacktrackedDeterministicClashedDescriptors` [7866-7896] (L31)

**Unit 30** (Clash processing, 18 methods, 475 lines):
  - `createClashedIndividualNodeDescriptor` [4395-4405] (L11)
  - `generateDebugTrackedClashedDescriptorSummaryString` [6569-6585] (L17)
  - `generateDebugTrackedClashedDescriptorString` [6588-6718] (L131)
  - `getFreeTrackedClashedDescriptor` [6952-6959] (L8)
  - `markRelevanceForTrackedClashedDescriptors` [7352-7357] (L6)
  - `addIndiNodeSignatureOfUnsatisfiableClashedDescriptors` [7545-7552] (L8)
  - `isClashedDescriptorSortedBefore` [7554-7556] (L3)
  - `getSortedClashedDescriptors` [7559-7583] (L25)
  - `writeUnsatisfiableClashedDescriptors` [7586-7592] (L7)
  - `getCollectedFilteredClashedDescriptorsFromBranch` [7595-7652] (L58)
  - `createTrackedClashesDescriptors` [7921-7935] (L15)
  - `createTrackedClashesDescriptor` [7939-7973] (L35)
  - `createClashedConceptDescriptor` [16717-16720] (L4)
  - `createClashedIndividualLinkDescriptor` [16722-16725] (L4)
  - `createClashedIndividualDistinctDescriptor` [16727-16730] (L4)
  - `createClashedNegationDisjointDescriptor` [16732-16735] (L4)
  - `isLabelConceptClashSet` [17323-17391] (L69)
  - `isLabelConceptClashSet` [20867-20932] (L66)

**Unit 31** (Generic helpers / accessors / label tests, 9 methods, 768 lines):
  - `readCalculationConfig` [494-845] (L352)
  - `analyzeABoxCompressionPossibilities` [4097-4159] (L63)
  - `analyzeBranchingMemoryWasting` [4163-4190] (L28)
  - `testProblematicConceptSet` [4408-4456] (L49)
  - `analyseBranchingStatistics` [4462-4499] (L38)
  - `debugTestCriticalConceptSet` [4628-4667] (L40)
  - `searchSignatureReusingIndividualNode` [4977-5018] (L42)
  - `removeIndividualReusing` [5021-5025] (L5)
  - `updateIndividualReusing` [5028-5178] (L151)

**Unit 32** (Generic helpers / accessors / label tests, 9 methods, 713 lines):
  - `establishIndividualReusing` [5193-5298] (L106)
  - `reactivateIndirectReuseSuccessors` [6486-6503] (L18)
  - `cancellationRootTask` [6902-6932] (L31)
  - `cancellationTask` [6935-6949] (L15)
  - `generateDebugIndiStatusString` [8039-8173] (L135)
  - `generateExtendedDebugConceptSetStringList` [8301-8362] (L62)
  - `writeGeneratedExtendedDebugIndiModelStringList` [8368-8393] (L26)
  - `generateExtendedDebugIndiModelStringList` [8396-8625] (L230)
  - `generateDebugIndiModelStringList` [8629-8718] (L90)

**Unit 33** (Generic helpers / accessors / label tests, 14 methods, 753 lines):
  - `tryCompletionGraphReuse` [9257-9381] (L125)
  - `isRestrictedTopObjectPropertyPropagation` [9617-9631] (L15)
  - `areRepresentativesJoinable` [10650-10669] (L20)
  - `createCommonJoiningAll` [10672-10715] (L44)
  - `createCommonJoiningKeyMap` [10719-10767] (L49)
  - `propagateRepresentativeToSuccessor` [11050-11117] (L68)
  - `updateRepresentativePropagationSet` [11260-11375] (L116)
  - `propagateRepresentative` [11379-11387] (L9)
  - `requiresRepresentativePropagation` [11390-11444] (L55)
  - `propagatePropagationBindingsToSuccessor` [13294-13355] (L62)
  - `propagateInitialPropagationBindingsToSuccessor` [13362-13390] (L29)
  - `propagateFreshPropagationBindingsToSuccessor` [13395-13463] (L69)
  - `propagatePropagationBindings` [13626-13688] (L63)
  - `propagateInitialPropagationBindings` [13773-13801] (L29)

**Unit 34** (Generic helpers / accessors / label tests, 18 methods, 792 lines):
  - `propagateFreshPropagationBindings` [13804-13871] (L68)
  - `addReverseRoleAssertion` [14410-14455] (L46)
  - `addRoleAssertion` [14495-14540] (L46)
  - `hasIdenticalConceptOperands` [14823-14858] (L36)
  - `createDistinctBranchingTask` [15530-15607] (L78)
  - `getAdditionalDisjunctCheckingConcept` [16464-16490] (L27)
  - `isConceptAdditionAtomaric` [17013-17019] (L7)
  - `installConceptRoleBranchTrigger` [17206-17217] (L12)
  - `searchNextConceptRoleBranchTrigger` [17221-17240] (L20)
  - `getIndividualNodeLink` [17307-17319] (L13)
  - `isLabelConceptSubSet` [17466-17543] (L78)
  - `isLabelConceptEqualSet` [17547-17575] (L29)
  - `isPairwiseLabelConceptEqualSet` [17642-17695] (L54)
  - `collectIndividualNodeVariablePropagationBindings` [18055-18084] (L30)
  - `getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindings` [18102-18114] (L13)
  - `getIndividualNodesListAssociatedConceptsSetFromVariablePropagationBindings` [18120-18149] (L30)
  - `isAnonymousVariablePropagationBindingSingleIndividualAnalogousPath` [18155-18258] (L104)
  - `isAnonymousVariablePropagationBindingAnalogousPath` [18283-18383] (L101)

**Unit 35** (Generic helpers / accessors / label tests, 35 methods, 770 lines):
  - `generateDebugIndividualNodeAssociatedConceptsString` [18390-18409] (L20)
  - `generateDebugIndividualNodeAssociatedConceptsSetString` [18414-18425] (L12)
  - `generateDebugIndividualNodesListAssociatedConceptsSetString` [18430-18462] (L33)
  - `containsIndividualNodeConcept` [18786-18789] (L4)
  - `containsIndividualNodeConcept` [18792-18805] (L14)
  - `containsIndividualNodeConcepts` [18808-18849] (L42)
  - `containsIndividualNodeConcepts` [18852-18862] (L11)
  - `containsIndividualNodeConcepts` [18865-18868] (L4)
  - `containsIndividualNodeConcepts` [18870-18873] (L4)
  - `containsIndividualNodeConcepts` [18876-18879] (L4)
  - `addIndividualNodeCandidateForConcept` [19543-19549] (L7)
  - `addIndividualNodeCandidateForConcept` [19552-19568] (L17)
  - `propagateIndividualNodeModified` [19634-19688] (L55)
  - `pruneSuccessors` [19699-19758] (L60)
  - `hasAncestorIndividualNode` [20117-20122] (L6)
  - `hasRoleSuccessorConcept` [20125-20140] (L16)
  - `hasRoleSuccessorConcepts` [20142-20167] (L26)
  - `getRoleSuccessorWithConcepts` [20170-20193] (L24)
  - `hasDistinctRoleSuccessorConcepts` [20198-20238] (L41)
  - `createIndividualNodeDisjointRolesLinks` [20241-20270] (L30)
  - `createIndividualNodeNegationLink` [20274-20295] (L22)
  - `tryExtendFunctionalSuccessorIndividual` [21565-21632] (L68)
  - `createSuccessorIndividual` [21635-21670] (L36)
  - `createDistinctSuccessorIndividuals` [22143-22186] (L44)
  - `createNewIndividualsLinks` [22212-22247] (L36)
  - `installIndividualNodeRoleLink` [22251-22269] (L19)
  - `installIndividualNodeRoleLinkReapplied` [22272-22292] (L21)
  - `createNewIndividualsLink` [22355-22369] (L15)
  - `createIndividualsDistinct` [22401-22409] (L9)
  - `createIndividualsDistinct` [22413-22430] (L18)
  - `hasIndividualsLink` [22433-22435] (L3)
  - `createNewEmptyIndividual` [22439-22458] (L20)
  - `createNewIndividual` [22462-22475] (L14)
  - `getAvailableUpToDateIndividual` [22477-22482] (L6)
  - `getUpToDateIndividual` [22485-22493] (L9)

**Unit 36** (Generic helpers / accessors / label tests, 19 methods, 503 lines):
  - `getUpToDateIndividual` [22506-22583] (L78)
  - `getPropagationSteeringController` [25707-25723] (L17)
  - `getLocalizedIndividual` [26412-26414] (L3)
  - `getLocalizedIndividual` [26416-26444] (L29)
  - `getSuccessorIndividual` [26446-26461] (L16)
  - `getLocalizedSuccessorIndividual` [26464-26477] (L14)
  - `getAncestorIndividual` [26480-26488] (L9)
  - `addConceptToIndividual` [26725-26753] (L29)
  - `addConceptToIndividualReturnConceptDescriptor` [26757-26782] (L26)
  - `setIndividualNodeAncestorConnectionModified` [26786-26788] (L3)
  - `setIndividualNodeConceptLabelSetModified` [26790-26796] (L7)
  - `isIndividualNodeConceptLabelSetModified` [26800-26802] (L3)
  - `createConceptDescriptor` [26809-26817] (L9)
  - `releaseConceptDescriptor` [26820-26824] (L5)
  - `addConceptsToIndividual` [26829-26869] (L41)
  - `insertConceptsToIndividualConceptSet` [26925-27021] (L97)
  - `addConceptsToIndividual` [27026-27064] (L39)
  - `addConceptsToIndividual` [27068-27106] (L39)
  - `addConceptsToIndividual` [27110-27148] (L39)
