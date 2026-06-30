# Konclude `Process/` — Runtime Completion-Graph Data Model (port catalogue)

Source: `Source/Reasoner/Kernel/Process/` in the Konclude checkout
(`/home/leechuck/Public/software/Konclude`). READ-ONLY reference.

Scope of directory: **347 top-level classes** (346 `.h`/`.cpp` pairs at the root
+ `ProcessSettings.h`, header-only), plus two subtrees:
- `Dependency/` — 151 files (75 class pairs + branching-tree), the proof / dependency-tracking node zoo.
- `Marker/` — 3 files (`CMarker`, `MarkerSettings.h`).

This is the in-memory data model the SHIQ tableau **completion engine** mutates
during a satisfiability test. It is NOT the calculus driver (that lives in
`Kernel/Algorithm/`); these are the structs the algorithm reads and writes.

Every root file is >100 lines; line counts below are `.h`+`.cpp` combined.

---

## 1. CORE classes (port these as Rust structs FIRST)

These are the objects the completion algorithm directly manipulates per
satisfiability test. Field/method counts are from the `.h`.

### CProcessingDataBox  — 3422 L, **209 fields, 265 methods**
Bases: none (standalone). The **per-test global state container** ("data box"):
owns every processing queue, the individual-node vector, the clash linker,
top-concept handles, ontology pointer, branching/merging bookkeeping, datatype
value-space data, statistics. This is the root aggregate the engine threads
through every rule.
- **Dominant pattern: triple-buffered fields** `mX` / `mUseX` / `mPrevX`
  (current / working / previous) on nearly every queue — this is Konclude's
  copy-on-branch + restore-on-backtrack mechanism for the completion graph.
  ~50+ of the 209 fields are such triples.
- Representative field groups: `CIndividualProcessingQueue*`,
  `CIndividualUnsortedProcessingQueue*` (×many: immediate, delayed-nominal,
  role-assertion, backend-sync-retest, backend-reuse, direct-influence …),
  `CIndividualDepthProcessingQueue*`, `CIndividualConceptBatchProcessingQueue*`,
  `CIndividualLinkerRotationProcessingQueue*`, `CIndividualVector*`,
  `CIndividualProcessNodeVector*`, `CClashedDependencyDescriptor*`,
  `CConcept* mOntologyTopConcept / mOntologyTopDataRangeConcept`,
  `CConcreteOntology* mOntology`, `CProcessContext* mProcessContext`.
- Port note: in Rust this becomes the owning `ProcessingDataBox` struct; the
  `m/mUse/mPrev` triples map to an explicit save/restore stack rather than three
  raw pointers.

### CIndividualProcessNode  — 3035 L, **143 fields, ~320 methods**
Bases: `CIndividualProcessNodeReference`, `CLocalizationTag`, `CBlockedTestTag`,
`CDependencyTracker` (multiple inheritance → in Rust = composition of those as
embedded fields/traits). **The completion-graph node** (an individual / tableau
node). Holds its concept label set, role successors, blocking state, caching
state, datatype values, merge state.
- Identity/topology fields: `cint64 mIndiID`, `CIndividualType mIndiType`,
  `CIndividual* mNomIndi`, `cint64 indiAncDepth / mNominalLevel / mMergeIntoID`,
  `CIndividualLinkEdge* mAncestorLink / mLastAddedLink`,
  `CProcessContext* mProcessContext`, `CMemoryAllocationManager* mMemAllocMan`,
  `CIndividualProcessNode* mPrevIndividual / mBlockerIndiNode / mFollowingIndiNode`.
- Label/successor stores (again `m/mUse/mPrev` triples):
  `CConceptProcessingQueue*`, `CReapplyConceptLabelSet*`,
  `CReapplyRoleSuccessorHash*`, `CSuccessorRoleHash*`,
  `CConnectionSuccessorSet*`, `CDistinctHash*`, `CDisjointSuccessorRoleHash*`.
- Blocking / signature-blocking: `CIndividualNodeSaturationBlockingData*`,
  `CIndividualNodeBlockData*`,
  `CBlockingVariableBindingsAnalogousPropagationData*`,
  `CIndividualNodeAnalizedConceptExpansionData*`,
  `CSignatureBlockingIndividualNodeConceptExpansionData*`,
  `CReusingIndividualNodeConceptExpansionData*`, `CBlockingFollowSet*`,
  `CXLinker<CIndividualProcessNode*>* mBlockedIndividualsLinker`,
  many `mLast…BlockerCandidate…` cint64 counters, `bool mInvalidSignatureBlocking`.
- Propagation / variable-binding (SHIQ + nominal-schema):
  `CConceptPropagationBindingSetHash*`, `CConceptVariableBindingPathSetHash*`,
  `CConceptRepresentativePropagationSetHash*`, `CPropagationBindingSet*`.
- Caching / backend sync: `CIndividualNodeModelData* indiModel`,
  `CIndividualNodeSatisfiableCacheRetrievalData*`,
  `CIndividualNodeSatisfiableCacheStoringData*`,
  `CIndividualNodeBackendCacheSynchronisationData*`,
  `CIndividualNodeUnsatisfiableCacheRetrievalData*`.
- Assertion-init iterators: `CXSortedNegLinker<CConcept*>*`,
  `CConceptAssertionLinker*`, `CDataAssertionLinker*`, `CRoleAssertionLinker*`,
  `CReverseRoleAssertionLinker*`, `CAdditionalProcessRoleAssertionsLinker*`,
  `CAdditionalProcessDataAssertionsLinker*`, `CProcessAssertedDataLiteralLinker*`.
- Queue-membership booleans (~20 `bool m…ProcessingQueued`),
  `CIndividualProcessNodePriority mLastProcessingPriority`.
- Merge/reactivation: `CIndividualMergingHash*`, `CDependencyTrackPoint*
  mMergedDepTrackPoint`, `CNominalCachingLossReactivationData*`,
  `CSuccessorIndividualATMOSTReactivationData*`,
  `CSuccessorConnectedNominalSet*`, `CDatatypesValueSpaceData*`,
  `CIndividualNodeIncrementalExpansionData*`.
- Port note: this is the single biggest port unit. The `m/mUse/mPrev` triples
  are again branch save/restore. The multiple inheritance must become
  composition (`reference`, `localization_tag`, `blocked_test_tag`,
  `dependency_tracker` as embedded structs).

### CIndividualSaturationProcessNode  — 1025 L, **38 fields, 102 methods**
Base: `CIndividualProcessNodeReference`. The **saturation-phase** counterpart of
the process node (lightweight pre-completion / lazy non-branching saturation —
the "cheap" pass before full tableau). Fields: `CProcessContext*`,
`CMemoryAllocationManager*`, `CExtendedConceptReferenceLinkingData*`,
`CIndividualSaturationReferenceLinkingData*`,
`CRoleBackwardSaturationPropagationHash*`, `CReapplyConceptSaturationLabelSet*`,
`CIndividualSaturationProcessNodeExtensionData*`,
`CIndividualSaturationProcessNodeLinker* mIndiProcessLinker / mIndiCompletionLinker`,
`CConceptSaturationProcessLinker*`, status flags
(`CIndividualSaturationProcessNodeStatusFlags mDirect/mIndirectStatusFlags`),
substitute/copy node pointers, `CConceptSaturationDescriptor* mClashedConSatDesLinker`,
dependency linkers (`CXNegLinker<…>* mDependingIndiNodeLinker`,
`CXLinker<…>* mNonInverseConnectedIndiNodeLinker / mMultipleCardinalityAncestorNodesLinker`),
nominal handles (`CIndividual* mNominalIndi / mIntegratedNominalIndi`),
`CIndividualSaturationProcessNodeCacheData* mCacheData`, `cint64 mIndiID /
mReferenceMode / mMaxAtleastCardinality / mMaxAtmostCardinality`, several bool
flags (`mSeparatedSaturation`, `mABoxIndividualRepresentationNode`, occurrence
statistics).

### CReapplyConceptLabelSet  — 689 L, **11 fields, 35 methods**
Base: `CConceptLabelSetModificationTag`. The **concept label set** of a node
(the set of concepts asserted at an individual) plus the "reapply" dependency
map so rules can be re-fired on backtrack/extension. Fields:
`CPROCESSMAP<cint64,CConceptDescriptorDependencyReapplyData> mConceptDesDepMap`
(+ `*mAdditionalConceptDesDepMap`), `CCoreConceptDescriptor* mCoreConDesLinker`,
`CConceptDescriptor* mConceptDesLinker / mPrevConceptDesLinker`,
`CConceptSetSignature mConceptSignature`, `CConceptSetStructure mConceptStructure`,
`CConceptSetFlags mConceptFlags`, `cint64 mConceptCount`, `CProcessContext*`.
Saturation twin: **CReapplyConceptSaturationLabelSet** (513 L).

### CReapplyRoleSuccessorHash  — 515 L, **4 fields, 22 methods**
Base: none. The **role-successor edge index** of a node, with reapply support:
`CProcessContext* mContext`,
`CPROCESSHASH<CRole*,CReapplyRoleSuccessorData> mRoleSuccessorDataHash`,
`cint64 mLinkCount`. Maps each role to its successor links; `CReapplyRoleSuccessorData`
(141 L) is the per-role value. Saturation twin:
**CLinkedRoleSaturationSuccessorHash** (456 L).

### CBranchingMergingProcessingRestrictionSpecification  — 685 L, **25 fields, 56 methods**
Bases: `CProcessingRestrictionSpecification`
(itself `: CLinkerBase<double,CProcessingRestrictionSpecification>`),
`CDependencyTracker`. The **merge/≤n branching restriction** record driving
ATMOST-induced node merging. Fields include `cint64 mRemainingNominalCreationCount`,
`CIndividualLinkEdge* mIndiLink`, remaining-candidate counters,
`bool mDistinctSetFixed / mHasMergingInitCandidates`,
`CPROCESSSET<cint64>* mDistinctMergedNodesSet / mLastDistinctMergedNodesSet`,
six `CBranchingMergingIndividualNodeCandidateLinker*` candidate lists
(nominal/merging/init/onlyPosQualify/onlyNegQualify/bothQualify),
`CNonDeterministicDependencyNode* mMergingDependencyNode`,
`CClashedDependencyDescriptor* mInitMergingNodesClashes / mMultipleInitMergingNodesClashes`,
`CDependencyTrackPoint* mAddedBlockablePredDepTrackPoint`,
`CXLinker<CIndividualLinkEdge*>* mLastCheckedSuccChoiceTriggerLinker`, misc flags.
Sibling: **CBranchingORProcessingRestrictionSpecification** (262 L) — the ⊔
disjunction-branching variant.

### Dependency tracking (the proof / backtracking spine — port as a unit)
The completion graph carries a dependency DAG so the engine can do
dependency-directed backjumping. Core nodes live in `Dependency/`:
- **CDependencyNode** (186 L) base `CProcessingTag`. Fields:
  `CProcessContext*`, `CConceptDescriptor* mConceptDescriptor`,
  `CIndividualProcessNode* mIndividualNode`, `DEPENDENCNODEYTYPE mDepNodeType`,
  `CDependencyTrackPoint* mDepTrackPoint`, `CDependency* mAdditionalAfterDepLinker`.
- **CDeterministicDependencyNode** (`: CDependencyNode, CDependencyTrackPoint`)
  and **CNonDeterministicDependencyNode** (`: CDependencyNode`) — the det/nondet
  split that drives backjumping.
- **CDependencyTrackPoint** (`: CBranchingTag`) — a branch point label;
  **CNonDeterministicDependencyTrackPoint**, **CORDisjunctDependencyTrackPoint**.
- **CDependency** (`: CLinkerBase<CDependency*,CDependency>`) — an intrusive
  linked dependency edge.
- **CBranchingTree** / **CBranchTreeNode** — the search/branching tree.
- 70+ rule-specific dependency-node subclasses
  (`C{ALL,AND,ATLEAST,ATMOST,SOME,OR,MERGE,NOMINAL,FUNCTIONAL,CONNECTION,
  PROPAGATE…,REPRESENTATIVE…,REUSE…,VARBIND…}DependencyNode`) — one per
  expansion rule; each is small (one record type tagging "this fact was derived
  by rule X from these premises"). Port as a single tagged enum
  `DependencyKind` + one `DependencyNode` struct, NOT 70 structs.
- `CDependencyTracker` (root, 150 L) — the mixin the process nodes inherit to
  hold their current track point.

---

## 2. Inheritance hierarchies & base classes

Small tag/reference bases (all in the root, each ~85–210 L); in Rust these
become embedded fields or marker traits, not deep class trees:

| Base | L | derives from | role |
|------|---|--------------|------|
| `CProcessReference` (in `Ontology/`) | — | — | root: ties an object to a `CProcessContext` |
| `CIndividualProcessNodeReference` | 126 | `CProcessReference` | node identity / context handle |
| `CProcessTag` | 168 | — | root of the "tag" mixins |
| `CProcessingTag` | 197 | — | dependency-node tag root |
| `CLocalizationTag` | 206 | `CProcessTag` | per-node localization marking |
| `CBlockedTestTag` | 190 | `CProcessTag` | blocking-test marking |
| `CConceptLabelSetModificationTag` | 197 | `CProcessTag` | label-set dirty marking |
| `CBlockingFollowUpdateTag` | 198 | `CProcessTag` | blocking-follow update marking |
| `CNodeSwitchTag` | 197 | `CProcessTag` | node-switch marking |
| `CBranchingTag` | 210 | — | branch-point tag root |
| `CDependencyTracker` | 150 | — | mixin: holds current dep track point |
| `CProcessingRestrictionSpecification` | 159 | `CLinkerBase<double,…>` | base of branching-restriction specs |

Multiple-inheritance hot spots to flatten into composition:
`CIndividualProcessNode : CIndividualProcessNodeReference, CLocalizationTag,
CBlockedTestTag, CDependencyTracker`;
`CBranchingMergingProcessingRestrictionSpecification :
CProcessingRestrictionSpecification, CDependencyTracker`;
`CDeterministicDependencyNode : CDependencyNode, CDependencyTrackPoint`.

## Intrusive linked-list / linker patterns ([ownership] concerns)

Pervasive: **118 of 347** root headers reference a linker template
(`CLinker` / `CLinkerBase` / `CSortedLinker` / `CXLinker` / `CXNegLinker` /
`CSortedNegLinker`, from `Utilities/Container/CLinker.h`). The codebase models
sets/lists as **intrusive singly-linked chains** (each element embeds its own
`next` pointer) rather than `Vec`/`HashMap`, for arena allocation + cheap
branch-local prepend + O(1) restore on backtrack. Dedicated `*Linker` classes at
the root (each its own node type): `CConceptProcessLinker`,
`CIndividualProcessNodeLinker`, `CIndividualSaturationProcessNodeLinker`,
`CAnalizedConceptExpansionLinker`, `CAdditionalProcessRoleAssertionsLinker`,
`CAdditionalProcessDataAssertionsLinker`, `CProcessAssertedDataLiteralLinker`,
`CBranchingMergingIndividualNodeCandidateLinker`,
`CBackendNeighbourExpansionQueueDataLinker`, `CConceptSaturationProcessLinker`,
`CRoleSaturationProcessLinker`, `CSaturationDisjunctExtractionLinker`,
`CLinkedNeighbourRoleAssertion*Linker`, `CVariableBindingTriggerLinker`,
`CSaturationModifiedProcessUpdateLinker`,
`CIndividualRepresentativeBackendCacheConceptSetLabelNodeQueuingLinker`, etc.
Accessors are mostly `getNext…()` / `setNext…()` (named per payload, e.g.
`getNextProcessIndividualNode`, `getNextConceptDesciptor`).

**Port strategy for the linkers:** replace intrusive `next` chains with arena
indices (`Vec` + `u32` index "links") or `Vec<T>` collections; reproduce the
branch save/restore (`m/mUse/mPrev` triples + linker prepend/unwind) with an
explicit trail/undo stack. Do NOT port the raw pointer chains 1:1 into Rust
(`Box`/`&mut` cycles will fight the borrow checker).

Memory: nodes are arena-allocated via `CMemoryAllocationManager` /
`CProcessMemoryPoolAllocationManager` (134 L) /
`CObjectParameterizingAllocator` — all objects are pool-owned and freed
en masse at test end. Rust port = bump/arena allocator owning the node vectors.

---

## 3. PERIPHERAL subtrees — LATER WAVE / possibly out of scope

Port these only after the core node + dependency model works.

### Datatype value-space maps (concrete domains) — LATER WAVE
Large, self-contained datatype reasoning (only fires on ontologies with
datatypes; ORE-irrelevant for most onts). ~40 classes:
- `CDatatypeRealValueSpaceMap` (1833), `CDatatypeStringValueSpaceMap` (1668),
  `CDatatypeCompareValueSpaceMap` (1394), `CDatatypesValueSpaceData` (628),
  `CDatatypeValueSpaceData` (328), `CDatatypeValueSpaceRealValuesCounter` (333),
  `CDatatypeRealValueDataExclusion` (351), `CDatatypeStringValueDataExclusion` (306),
  and the per-XSD-type families
  `CDatatype{Float,Double,DateTime,Boolean,IRI,XML,BinaryHex,BinaryBase64,
  Binary,Unknown}ValueSpace{Map,Data}`, `*ValueData`, `*ValuesCounter`,
  `*ExclusionType`, `*SpaceMapArranger`, `*SpaceMapData`,
  `CDatatypeValueSpaceDependencyCollector`,
  `CClashedDatatypeValueSpaceExclusionDescriptor`,
  `CDatatypeDependencyTrackPointCollection`,
  `CDatatypeRealValueSpaceData`, etc.

### Backend-cache synchronisation data — LATER WAVE
Konclude's persistent saturation/instance-cache backend; not needed for a
classify-only port until incremental/large-ABox work:
- `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData` (1396),
  `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisation*NeighbourExpansionData`,
  `CIndividualNodeBackendCacheSynchronisationData`,
  `CBackendNeighbourExpansion{Queue,ControllingData,QueueDataLinker}`,
  `CIndividualRepresentativeBackendCacheConceptSetLabelProcessing{Data,Hash,Hasher}`,
  `CIndividualRepresentativeBackendCacheLoadedAssociation{Data,Hash}`,
  `CReuseBackend…`/`CReusing…`/`CReused…` reuse-expansion data,
  `CIndividualDelayedBackendInitializationProcessingQueue`.

### Statistics — OUT OF SCOPE (instrumentation only)
`CProcessingStatistics` (811), `CProcessingStatisticGathering` (208),
`CProcessingStatisticDescription`, `CProcessingStatisticRegistrator`. Pure
counters; replace with lightweight Rust metrics or drop.

### Nominal-schema / variable-binding propagation (SROIQ rules) — LATER WAVE
Heavy machinery for nominal schemas + role-conjunction propagation; large but
only exercised by nominal-schema / complex-RBox onts. ~50 classes incl. the
`CRepresentativeVariableBindingPath*` family (~20 classes: `…SetHash`,
`…SetData`, `…JoiningData/Hash/Hasher`, `…KeyData/Map`, `…MigrateData`, …),
`CVariableBindingPath*` / `CVariableBinding*` family,
`CConceptNominalSchemaGrounding{Data,Hash,Hasher}`,
`CPropagation{Binding,RepresentativeTransition,VariableBindingTransition}*`,
`CRepresentative{Joining,Propagation,Containing}*`.

---

## 4. Remaining root classes (catalogue, grouped; line counts = .h+.cpp)

Name-derived purposes (Konclude names are descriptive). Core/peripheral members
above are not repeated.

### Completion-graph edges & successor indices (CORE-adjacent)
- `CIndividualLinkEdge` (175) — a role edge between two process nodes (the role-successor link object).
- `CLinkEdge` (165) / `CNodeEdge` (274) — generic graph edge base / node-edge record.
- `CDistinctEdge` (139) — owl:differentFrom edge; `CDistinctHash` (194) / `CDistinctIterator` (185) / `CDistinctHash` index.
- `CNegationDisjointEdge` (137) — disjoint-role negative edge; `CDisjointSuccessorRoleHash` (237) / `CDisjointSuccessorRoleIterator` (160).
- `CSuccessorRoleHash` (264) / `CSuccessorRoleIterator` (176) — node → outgoing roles index.
- `CRoleSuccessorHash` (245) / `CRoleSuccessorIterator` (164) / `CRoleSuccessorLinkIterator` (195) — role → successor links.
- `CConnectionSuccessorSet` (267) / `CConnectionSuccessorSetIterator` (192) / `CConnectionSuccessorCorrectionHash` (162) — connected-successor set per node.
- `CSuccessorIterator` (217) / `CSuccessorConnectedNominalSet` (165) — successor traversal + nominal-connection set.
- `CRoleReapplyHash` (181) / `CConceptReapplyHash` (184) / `CRoleBackwardPropagationHash` (166, +`…HashData` 137) — reapply-trigger indices.

### Concept label set / descriptors (CORE-adjacent)
- `CConceptLabelSet` (288) / `CConceptLabelSetIterator` (218) — base concept label set (CReapply… is the live one).
- `CConceptDescriptor` (198) / `CCoreConceptDescriptor` (144) / `CReapplyConceptDescriptor` (195) / `CCondensedReapplyConceptDescriptor` (188) / `CExtendedCondensedReapplyConceptDescriptor*` (139/159) — a concept occurrence + its dependency, condensed/extended variants.
- `CConceptSetSignature` (199) / `CConceptSetStructure` (184) / `CConceptSetFlags` (193) — label-set signature/structure/flags (used for blocking comparison).
- `CConceptDescriptorDependencyReapplyData` (150) / `CConceptDescriptorDependencyPair` (135) / `CConceptProcessDescriptor` (211) / `CClashedConceptDescriptor` (172) — descriptor dependency + clash records.

### Processing queues & priorities (CORE-adjacent — engine work scheduling)
- `CIndividualProcessingQueue` (282), `CIndividualUnsortedProcessingQueue` (193), `CIndividualDepthProcessingQueue` (255), `CIndividualReactivationProcessingQueue` (224), `CIndividualCustomPriorityProcessingQueue` (191), `CIndividualLinkerRotationProcessingQueue` (205), `CCriticalIndividualNodeProcessingQueue` (137), `CIndividualConceptBatchProcessingQueue` (418), `CIndividualDepthConceptProcessDescriptorProcessingQueue` (228 + `…Data` 132) — the node work queues.
- `CConceptProcessingQueue` (330) / `CConceptProcessingQueueIterator` (208) / `CConceptProcessingPriorityQueueData` (138) — per-node concept queue.
- `CReapplyQueue` (236) / `CReapplyQueueIterator` (159) / `CCondensedReapplyQueue` (219) / `CCondensedReapplyQueueIterator` (172) — rule-reapply queues.
- Priorities: `CIndividualProcessNodePriority` (247), `CIndividualDepthPriority` (184), `CConceptProcessPriority` (179).
- Vectors: `CIndividualProcessNodeVector` (139), `CIndividualSaturationProcessNodeVector` (132), `CIndividualProcessNodeDescriptor` (176), `CPreviousIndividualIDSet` (184).

### Context / infrastructure (CORE-adjacent)
- `CProcessContext` (168) / `CProcessContextBase` (188) — per-test context (allocator + data box handle); the ambient `&mut` state in the Rust port.
- `CProcessMemoryPoolAllocationManager` (134) — arena allocator.
- `CProcessTagger` (267) / `CProcessTag` (168) / `CProcessingTag` (197) — tag-id stamping for incremental marking.
- `ProcessSettings.h` (107) — compile-time macros (`CPROCESSMAP`/`CPROCESSHASH`/`CPROCESSSET` typedefs, switches).
- `CNodeSwitchHistory` (328) / `CNodeSwitchTag` (197) — node version/switch history (branch save/restore of nodes).

### Branching / merging / restriction specs (CORE-adjacent — search control)
- `CProcessingRestrictionSpecification` (159, base), `CBranchingORProcessingRestrictionSpecification` (262), `CLinkProcessingRestrictionSpecification` (142), `CTriggeredImplicationProcessingRestrictionSpecification` (183), `CTriggeredNominalImplicationProcessingRestrictionSpecification` (185).
- `CBranchingInstruction` (130) / `CBranchingInstructionAddIndividualConcepts` (175) — recorded branch decisions for restore.
- `CBranchingTag` (210) / `CBranchingMergingIndividualNodeCandidateLinker` (201).
- `CIndividualMergingHash` (180) / `CIndividualMergingHashData` (173) — ≤n merge bookkeeping.

### Blocking (CORE-adjacent — termination)
- `CIndividualNodeBlockData` (134) / `CIndividualNodeBlockingTestData` (222) / `CIndividualNodeSaturationBlockingData` (164) — per-node block state.
- Signature/anywhere blocking: `CSignatureBlockingIndividualNodeConceptExpansionData` (302), `CSignatureBlockingIndividualNodeCandidate{Hash,Data,Iterator}` (203/156/185), `CSignatureBlockingCandidate{Hash,Data,Iterator}` (222/146/148), `CSignatureBlockingReviewData{,Iterator,Set}` (179/191/174), `CBlockingAlternativeData` (130), `CBlockingAlternativeSignatureBlockingCandidateData` (198).
- Candidate hashes: `CBlockingIndividualNodeCandidate{Hash,Data,Iterator}` (209/187/196), `CBlockingIndividualNodeLinkedCandidate{Hash,Data}` (209/182), `CBlockingIndividualNodeLinker` (178), `CBlockingFollowSet` (143), `CBlockingFollowUpdateTag` (198), `CBlockingVariableBindingsAnalogousPropagationData` (158).
- `CIndividualNodeAnalizedConceptExpansionData` (270), `CReusingIndividualNodeConceptExpansionData` (232), `CAnalizedConceptExpansionLinker` (180).

### Clash descriptors (CORE-adjacent — unsat detection)
- `CClashedDependencyDescriptor` (156), `CClashedConceptDescriptor` (172), `CClashedIndividualLinkDescriptor` (150), `CClashedIndividualDistinctDescriptor` (148), `CClashedNegationDisjointLinkDescriptor` (150), `CClashedDatatypeValueSpaceExclusionDescriptor` (159).

### Saturation phase (CORE-adjacent — the lazy pre-pass; many small extension structs)
- Nodes/labels: `CIndividualSaturationProcessNode{,ExtensionData,StatusFlags,StatusUpdateLinker,CacheData,ExtensionResolveData,ExtensionResolveHash,Linker}`, `CReapplyConceptSaturationLabelSet{,Iterator}` (513/274), `CConceptSaturationDescriptor{,ReapplyData}`, `CConceptSaturationProcessLinker`, `CRoleSaturationProcessLinker`.
- Concept-extension data (per rule): `CSaturation{Successor,Predecessor,LinkedSuccessor}…{ALL,FUNCTIONAL,…}Concept(s)ExtensionData/Hash`, `CSaturationIndividualNode{ALL,FUNCTIONAL}ConceptsExtensionData`, `CSaturationSuccessor{Data,ExtensionData,ConceptExtensionMap,RoleAssertionLinker}`, `CSaturationDisjunctCommonConcept{CountHash,ExtractionData}`, `CSaturationDisjunctExtractionLinker`.
- ATMOST/merge & nominal in saturation: `CSaturationATMOSTSuccessorMerging{Data,Hash,HashData}`, `CSaturationIndividualNodeNominalHandlingData`, `CSaturationNominalDependentNode{Data,Hash,HashData}`, `CSaturation{Influenced,}NominalSet`, `CSaturationModifiedProcessUpdateLinker`, `CSaturationIndividualNodeDatatypeData`, `CSaturationIndividualNodeSuccessorExtensionData`, `CSaturationSuccessorExtensionIndividualNodeProcessingQueue`, `CSaturationIndividualNodeProcessingQueue`, `CCriticalSaturationConcept{Queue,TypeQueues}`.
- Backward saturation propagation: `CRoleBackwardSaturationPropagationHash{,Data}`, `CBackwardSaturationPropagation{Link,ReapplyDescriptor}`, `CLinkedRoleSaturationSuccessor{Hash,Data}`, `CIndividualSaturationSuccessorLinkDataLinker`, `CLinkedNeighbourRoleAssertionSaturation{Hash,Data,NodeLinker}`, `CExtendedConceptReferenceLinkingData`(*see node*), `CImplicationReapplyConceptSaturationDescriptor`.

### Backward / forward propagation (CORE-adjacent)
- `CBackwardPropagationLink` (166) / `CBackwardPropagationReapplyDescriptor` (149) / `CRoleBackwardPropagationHash` (166) — ∀/inverse-role backward propagation along edges.
- `CPropagationBinding{,Set,Map,MapData,Descriptor}`, `CPropagationBindingReapplyConcept{Hash,HashData,Iterator,Descriptor}`, `CPropagationBindingSet/Hash`, `CPropagationRepresentativeTransitionExtension`, `CPropagationVariableBindingTransitionExtension` — role-conjunction / nominal-schema binding propagation (overlaps the LATER-WAVE variable-binding family).

### Nominal / reactivation / reuse (mixed; mostly LATER WAVE)
- `CNominalCachingLossReactivationData/Hash/HashData`, `CSuccessorIndividualATMOSTReactivationData`, `CExtendedCondensedReapplyConceptDescriptorATMOSTReactivation`, `CReferredIndividualTracking{Vector,Data}`, `CReusedIndividualNodeData`, `CReusingReviewData`.

### Datatype dependency / assertion plumbing
- `CLinkedDataValueAssertionSaturationData`, `CLinkedNeighbourRoleAssertion{Linker,SaturationData,SaturationHash,SaturationNodeLinker}`, `CProcessAssertedDataLiteralLinker`, `CSaturationSuccessorRoleAssertionLinker`, `CCriticalPredecessorRoleCardinality{Hash,Data}`, `CCriticalIndividualNodeConceptTestSet`, `CSaturationPredecessorRoleFUNCTIONALConceptsExtensionHash`, `CSaturationLinkedSuccessor*` family.

### Caching (model / sat / unsat) — mostly LATER WAVE
- `CIndividualNodeModelData` (134), `CIndividualNodeSatisfiableCacheRetrievalData` (134) / `…StoringData` (134) / `CIndividualNodeSatisfiableExpandingCache{Retrieval,Storing}Data` (146/254), `CIndividualNodeUnsatisfiable{Cache,Occurence Cache}RetrievalData` (134/176), `CMarkerIndividualNode{Data,Hash}` (193/182).

### Marker subtree (`Marker/`) — small
- `CMarker` + `MarkerSettings.h` — node marking primitives used by incremental reasoning.

---

## Port ordering recommendation
1. `CProcessContext`/`Base` + arena allocator + `ProcessSettings` typedefs.
2. `CIndividualProcessNode` (+ its reference/tag bases as embedded structs) and
   its edge/label/successor indices (`CIndividualLinkEdge`,
   `CReapplyConceptLabelSet`, `CReapplyRoleSuccessorHash`, `CSuccessorRoleHash`).
3. `CProcessingDataBox` (queues + node vector) with an explicit branch
   save/restore trail replacing the `m/mUse/mPrev` triples.
4. Dependency model (`CDependencyNode` + `DependencyKind` enum,
   `CDependencyTrackPoint`, `CBranchingTree`) — needed for backjumping.
5. Branching/merging restriction specs + clash descriptors.
6. Blocking data structures.
7. Saturation phase (large but self-similar; can stub initially).
8. LATER WAVE: datatypes, backend-cache sync, nominal-schema variable bindings,
   statistics.
