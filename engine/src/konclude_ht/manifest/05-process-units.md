# W2 fan-out — Konclude `Process/` runtime completion-graph data model (port units)

Decomposition for porting Konclude's per-satisfiability-test completion-graph
state model (`Source/Reasoner/Kernel/Process/`) into Rust, function-by-function,
per `PORT.md` conventions. **No code is ported here** — this manifest is the
unit catalogue later agents work from. Source is READ-ONLY.

Builds on `00-type-dag.md`, `02-process-model.md`, and the W1 `model/` foundation
(`substrate.rs`: `Id<T>`/`Arena<T>`/`NegLink`/`Trail`/`Cint64`; `mod.rs` canonical
ids `ConceptId`/`RoleId`/`IndividualId`/`VariableId`). This wave adds the process
layer ids below and the struct/method units that consume them.

All `.cpp`/`.h` line numbers are into the Konclude checkout at
`/home/leechuck/Public/software/Konclude/Source/Reasoner/Kernel/Process/`.

---

## 1. Process-layer id list (seeds `process/mod.rs`)

Every `Process` class that the engine holds by pointer and allocates from a pool
becomes an `Id<T>` indexing a per-test `Arena<T>` on the process context. `CXxx*`
→ `XxxId`. The `CProcessContext`/`CProcessContextBase` itself is the *ambient
owner* of these arenas (the `&mut` state threaded through every method), NOT an
id. Saturation twins get their own ids so the two phases can coexist.

| Rust id (in `process/mod.rs`) | C++ type it replaces | arena element | notes |
|---|---|---|---|
| `NodeId` | `CIndividualProcessNode*` | `process::node::IndividualProcessNode` | the completion-graph node; most-referenced type in the model |
| `SatNodeId` | `CIndividualSaturationProcessNode*` | `process::sat_node::IndividualSaturationProcessNode` | saturation-phase node twin |
| `EdgeId` | `CIndividualLinkEdge*` | `process::edge::IndividualLinkEdge` | role edge; **folds bases `CNodeEdge`+`CLinkEdge`** (src/dst node + role) into one struct |
| `DistinctEdgeId` | `CDistinctEdge*` | `process::edge::DistinctEdge` | owl:differentFrom edge |
| `DisjointEdgeId` | `CNegationDisjointEdge*` | `process::edge::NegationDisjointEdge` | disjoint-role negative edge |
| `DependencyId` | `CDependencyNode*` (all ~62 `C*DependencyNode`) | `process::dependency::DependencyNode` (the tagged enum, §4) | one arena for the whole dependency-node zoo |
| `TrackPointId` | `CDependencyTrackPoint*` (+`NonDeterministic*`,`ORDisjunct*`) | `process::dependency::DependencyTrackPoint` | branch-point label; det node *is* its own track point |
| `DepLinkId` | `CDependency*` | `process::dependency::Dependency` | intrusive dep edge (`CLinkerBase` chain → `Vec`/index) |
| `BranchNodeId` | `CBranchTreeNode*` | `process::dependency::BranchTreeNode` | search/branching tree node |
| `ConDescId` | `CConceptDescriptor*` (+`Core`/`Reapply`/`CondensedReapply`/`Extended*` variants) | `process::descriptor::ConceptDescriptor` | concept occurrence + polarity + dep track point |
| `ConProcDescId` | `CConceptProcessDescriptor*` | `process::descriptor::ConceptProcessDescriptor` | queued concept + priority + restriction spec |
| `ClashDescId` | `CClashedDependencyDescriptor*` (+`Concept`/`Link`/`Distinct`/`NegationDisjoint`/`Datatype` clash kinds) | `process::clash::ClashedDescriptor` (tagged enum) | unsat-detection records |
| `LabelSetId` | `CReapplyConceptLabelSet*` | `process::label_set::ReapplyConceptLabelSet` | per-node concept label set (triple-buffered on node) |
| `RoleSuccHashId` | `CReapplyRoleSuccessorHash*` | `process::role_succ::ReapplyRoleSuccessorHash` | per-node role→successor index (triple-buffered on node) |
| `RestrictionSpecId` | `CProcessingRestrictionSpecification*` (+`BranchingMerging`/`BranchingOR`/`Link`/`Triggered*` subs) | `process::restriction::RestrictionSpec` (enum or base+variant) | merge/disjunction branching restriction |
| `BranchInstrId` | `CBranchingInstruction*` (+`AddIndividualConcepts`) | `process::branch::BranchingInstruction` | recorded branch decision for restore |

Secondary index/iterator/queue helper classes (`CSuccessorRoleHash`,
`CConnectionSuccessorSet`, `CDistinctHash`, `C*ProcessingQueue`, the saturation
extension data, etc.) are owned *inline* by their parent struct (a field, not a
top-level id) unless a later unit finds them shared across nodes — defer their
id-vs-inline decision to the unit that first needs them.

**`process/mod.rs` seed = the 16 id aliases above** plus `pub mod` lines for
`node`, `sat_node`, `edge`, `dependency`, `descriptor`, `clash`, `label_set`,
`role_succ`, `restriction`, `branch`, `databox`, `context`, `tags`.

---

## 2. Struct-definition units (define before any method compiles)

Field-level translation rules (the global `[ownership]` decision, per `substrate.rs`):
- `CXxx*` back-pointer → `XxxId` (`Id::NONE` for `nullptr`).
- intrusive `CLinker`/`CXLinker`/`CXNegLinker` chain → `Vec<…>` / `Vec<NegLink<…>>`.
- `CPROCESSMAP/HASH/SET` → `HashMap`/`HashSet` (`FxHashMap` later for speed; behaviour-neutral).
- **triple-buffer `mX`/`mUseX`/`mPrevX`** and **double `mX`/`mPrevX`** and
  **loc/use `mLocX`/`mUseX`** → one owned `Option<…>`/`Id` (the local) + an
  "active" id + a saved snapshot pushed on the `Trail` at branch points. These
  are the branch save/restore core; do NOT model them as three live pointers.
- multiple-inheritance bases → embedded composition fields (see each unit).

### SD-1 — `process/mod.rs` + tag bases + edge/descriptor structs
Seeds the id list (§1) and the small shared pieces every later struct embeds.
- **Tag/base composition structs** (`02-process-model.md` §2): `ProcessTag`
  { `process_tag: Cint64` }, `LocalizationTag` { `relocalized: bool` },
  `BlockedTestTag`, `DependencyTracker` { `dep_track_point: TrackPointId` },
  `IndividualProcessNodeReference`. Embedded as fields, not a trait tree.
- **`IndividualLinkEdge`** (`CIndividualLinkEdge.h` + folded `CLinkEdge.h`,
  `CNodeEdge.h`): `process_tag`, `relocalized`, `dep_track_point: TrackPointId`,
  `source: NodeId`, `destination: NodeId`, `role: RoleId`, `creator: NodeId`,
  (+ `next` chain → arena order). [pointer-alias] note: src/dst/creator are node ids.
- **`ConceptDescriptor`** (`CConceptDescriptor.h`, bases `CNegLinkerBase`+`CDependencyTracker`):
  `concept: ConceptId`, `negated: bool`, `dep_track_point: TrackPointId`, `next: ConDescId`.
- **`ConceptProcessDescriptor`** (`CConceptProcessDescriptor.h`, base `CSortedLinkerBase`):
  `concept_des: ConDescId`, `priority: ConceptProcessPriority`,
  `dep_track_point: TrackPointId`, `proc_spec: RestrictionSpecId`, `reapplied: bool`, `next`.

### SD-2 — `process/databox.rs` struct: `ProcessingDataBox`
~208 declared fields (`CProcessingDataBox.h` 565–875). Field groups:
- **50 buffered logical slots** → save/restore: **36 triples** `mX`/`mUseX`/`mPrevX`
  (26 processing queues `.h` 580–697,861–871 + 10 hashes/review-sets/history/tree
  `.h` 701–743) and **14 loc/use pairs** `mLocX`/`mUseX` (`.h` 573–577,745–826,
  855–867). Each → `{ local: Option<…>, active: …Id, saved: Trail-snapshot }`.
- **~72 singleton fields**: ontology/context ptrs (5: `mProcessContext`,
  `mOntologyTopConcept`, `mOntologyTopDataRangeConcept`, `mOntology`,
  `mIndiProcessVector`), clash linker (1), construction/last-processing
  bookkeeping (8), node-linker queues (5), **saturation linkers/vectors/sets (21)**,
  occurrence flags (3), id counters (6), branching (2), incremental expansion (6),
  referred-tracking (2), possible-instance merging (7), backend-cache misc (6).
Standalone (no inheritance). The 50 buffered slots are the whole difficulty —
their handoff is defined by `initProcessingDataBox` (method unit DB-1).

### SD-3 — `process/node.rs` struct: `IndividualProcessNode`
~143 fields (`CIndividualProcessNode.h` 646–848). **Compose 4 bases**:
`IndividualProcessNodeReference`, `LocalizationTag`, `BlockedTestTag`,
`DependencyTracker` (the last supplies `dep_track_point`, touched directly in
`.cpp` 321,367). Field groups:
- **A. 12 triples** `mX`/`mUseX`/`mPrevX` (36 fields): concept-processing queue,
  reapply concept-label set (`LabelSetId`), reapply role-succ hash (`RoleSuccHashId`),
  succ-role hash, connection-succ set, distinct hash, disjoint-succ-role hash,
  sig-block analyzed-expansion data, sig-block follow set, 3× concept-prop/
  var-bind-path/rep-prop set hashes.
- **B. 9 double-buffers** `mX`/`mPrevX` (18 fields): sat/indi/var-prop block data,
  unsat-cache-retrieval, sig-block concept-expansion, reusing-expansion, sat-cache
  retrieval+storing, backend-sync data. (getters take a `local…` flag.)
- **C. 6 loc/use pairs** `mLocX`/`mUseX` (12 fields): reactivation, ATMOST-reactivation,
  nominal-connection set, datatypes value-space, incremental-expansion, merging hash.
- **D. identity/topology (15)**: `indi_id`, `indi_type` (enum BLOCKABLE/NOMINAL),
  `nom_indi: IndividualId`, `processing_restriction_flags: Cint64` (bitset over
  ~55 `PRF*` masks → `const u64`), `indi_anc_depth`, `nominal_level`,
  `ancestor_link: EdgeId`, `merge_into_id`, ctx/alloc, `prev_individual: NodeId`,
  `last_added_link: EdgeId`, `blocker_indi_node: NodeId`, `following_indi_node: NodeId`,
  `disjoint_role_connections: bool`.
- **E. blocking/sig-blocking (10)**, **F. assertion-init linkers/iterators (14)**,
  **G. assertion-init bool flags (7)**, **H. caching/model (3)**,
  **I. propagation/backward-dep (7)**, **J. queue-membership bools + priority (17)**,
  **K. reactivation/merge/datatype/incremental singletons (4)**.

### SD-4 — `process/sat_node.rs`, `label_set.rs`, `role_succ.rs`, `restriction.rs` structs
The four satellite core classes (all single port units — each is cohesive and
< 800 real lines; trivial accessors collapse into Rust fields):
- **`IndividualSaturationProcessNode`** (`.h` 243–295, base
  `IndividualProcessNodeReference`): ctx/alloc, 2 ref-linking back-ptrs, 4 owned
  sub-structs (back-prop hash, reapply sat-label-set, `mIndiExtensionData`
  catch-all [note: needs `CIndividualSaturationProcessNodeExtensionData` ported
  alongside], cache data), ~8 linkers, related-node ptrs, `direct`/`indirect`
  status-flag pair, scalars (`indi_id`, nominal handles, max atleast/atmost
  cardinality, bools). No `mUse`/`mPrev` triples.
- **`ReapplyConceptLabelSet`** (`.h` 124–134, base `CConceptLabelSetModificationTag`,
  virtual dtor → polymorphic base of the saturation twin): `concept_des_dep_map`
  + **COW partner** `additional_concept_des_dep_map`, core/added/prev descriptor
  linkers, value-typed `signature`/`structure`/`flags`, `concept_count`, ctx.
- **`ReapplyRoleSuccessorHash`** (`.h` 110–112): `role_successor_data_hash:
  HashMap<RoleId, ReapplyRoleSuccessorData>`, `link_count`, ctx. The per-role
  value holds the **3-way COW representation** (`link_set` ⟷ `prev_link_set` +
  `located` flag ⟷ `link_linker` list).
- **`BranchingMergingRestrictionSpec`** (`.h` 162–187, **bases
  `CProcessingRestrictionSpecification`+`CDependencyTracker`** → compose): 6
  candidate-linker lists, COW pair `distinct_merged_nodes_set`/`last_…`, counts,
  bool flags, `indi_link: EdgeId`, `merging_dependency_node: DependencyId`, 2
  clash descriptors, dep-track-point. Sibling `BranchingORRestrictionSpec` (⊔)
  folds into `restriction.rs`.

### SD-5 — `process/dependency.rs` enum (§4 design)
The `DependencyNode` tagged enum + `DepKind` + base + track-point types.

---

## 3. Method-batch units (≤ ~800 source lines each)

**12 units across the two giants** + 6 satellite/dependency units = 18 method-batch
units total. Each lists its `.cpp` line range and size. Build the struct (§2)
first, then fill these.

### `CProcessingDataBox.cpp` (2527 L) → 6 units
| unit | concern | `.cpp` lines | size | notes |
|---|---|---|---|---|
| **DB-1** | lifecycle / save-restore: ctor, `initProcessingDataBox(ontology)`, `setProcessingOntology`, `initProcessingDataBox(parent)` | 33–597 | ~565 | **port first** — the parent→child copy defines every buffered slot's save/restore + copied-vs-nulled policy |
| **DB-2** | localised getters + ID counters + indi-queue/vector/top-concept accessors | 600–781 | ~182 | mechanical lazy-alloc |
| **DB-3** | triple-buffered queue `get`/`clear` pairs (26 queues) | 784–1284 | ~500 | highly repetitive; port via one helper over the triples |
| **DB-4** | blocking/reactivation hashes + node-linker take/add queues + construction state | 1295–1675 | ~380 | |
| **DB-5** | saturation subsystem (`mSat*`/`mIndiSaturation*`/ATMOST/nominal-delayed linkers, critical/influenced sets, occurred flags) | 1680–2143 | ~463 | self-contained |
| **DB-6** | incremental / possible-instance merging / backend-cache / branching instruction / referred-tracking | 2146–2517 | ~371 | |

### `CIndividualProcessNode.cpp` (2169 L) → 6 units
| unit | concern | `.cpp` lines | size | notes |
|---|---|---|---|---|
| **PN-1** | init/clone: ctor + `initIndividualProcessNode` + `initIndividualProcessNodeCopy` | 35–482 | ~447 | **highest complexity** — field-by-field buffer handoff (A/B/C conventions); port after SD-3 |
| **PN-2** | assertion/init-concept linkers + init-state flags + identity | 486–836 | ~350 | |
| **PN-3** | lazy label/prop-hash getters + role-successor/edge ops + reapply queues + topology/link install-remove | 838–1273 | ~435 | |
| **PN-4** | model/cache/blocking-data accessors + depth/merge-into + processing-blocked linkers + restriction flags + blocker-candidate counts | 1275–1671 | ~396 | |
| **PN-5** | invalid-sig blocking + backward-dep linkers + backprop/process-node linkers + queue membership + priority | 1673–2009 | ~336 | |
| **PN-6** | reactivation / nominal-conn / datatype / incremental + merge | 2011–2169 | ~158 | |

### Satellite + dependency units (6)
| unit | class / file | `.cpp` lines | size | split? |
|---|---|---|---|---|
| **SAT-1** | `CIndividualSaturationProcessNode` | 35–700 | ~712 | ONE unit; only `initCoping` (94–124) carries logic |
| **LS-1** | `CReapplyConceptLabelSet` | 34–528 | ~537 | ONE unit; COW heart = `initConceptLabelSet` + every insert/get's `additional`-map fold (preserve size thresholds 50, ×10) |
| **RS-1** | `CReapplyRoleSuccessorHash` | 33–375 | ~384 | ONE unit; 3-way succ representation + `ensure…Localated`/`eliminate…PreviousShareData` (thresholds 100, ×10, ≥5); gotcha: coupled-id = integer **sum** |
| **BM-1** | `CBranchingMergingRestrictionSpec` (+`BranchingOR…`) | 33–448 | ~478 | ONE unit; candidate-linker take/add priority + distinct-set COW |
| **DEP-1** | dependency-node ctors/accessors + `CDependency`/track-point methods | (Dependency/ `.cpp` set) | ~split if >800 | enum-dispatch methods; size after struct lands |
| **DEP-2** | `CBranchingTree`/`CBranchTreeNode` + det/nondet track-point logic | (Dependency/ `.cpp` set) | ~ | backjumping spine |

---

## 4. Dependency-tree design — one tagged `enum DependencyNode`

Collapses the **62 concrete `C*DependencyNode` classes** (the `DEPENDENCNODEYTYPE`
enum, `CDependencyNode.h` 75–97) into **7 structural variants**, keyed by payload
shape, while retaining the original 62-value tag as a `DepKind` field (the rest of
the reasoner branches on it). Finding: almost every variant is **tag-only** — the
only per-variant payload is 0/1/2 embedded `CDependency` back-edges, plus one
outlier carrying a `CXLinker<cint64>`.

### Shared base fields (every variant carries `DepNodeBase`)
From `CProcessTag` → `CProcessingTag` → `CDependencyNode` (`.h` 155–164):
```
struct DepNodeBase {
    process_tag:        Cint64,            // CProcessTag::mProcessTag
    concept_descriptor: ConDescId,         // CConceptDescriptor* mConceptDescriptor
    individual_node:    NodeId,            // CIndividualProcessNode* mIndividualNode
    kind:               DepKind,           // DEPENDENCNODEYTYPE mDepNodeType (62 values)
    dep_track_point:    TrackPointId,      // previous CDependencyTrackPoint* mDepTrackPoint
    additional_after:   DepLinkId,         // CDependency* mAdditionalAfterDepLinker (chain)
}
```
`CDependencyTrackPoint` (`.h` 76–77, base `CBranchingTag:CProcessTag`):
`{ dep_node: DependencyId, relevant_flag: bool, process_tag: Cint64 }`. A
**deterministic** node multiply-inherits its own track point (it *is* its
continuation point) — model as `TrackPointId::NONE` + a `deterministic: true`
discriminant, the track point materialised lazily.
`NonDetData` (from `CNonDeterministicDependencyNode.h` 106–114):
`{ branch_track_points: TrackPointId, clash_track_point: TrackPointId(by-value→inline),
   dependency_clashes: ClashDescId, branch_node: BranchNodeId, branch_tag: Cint64,
   closing_track_point: TrackPointId, closed_track_point: TrackPointId }`.
`OrDisjunctTrackData` (from `CORDisjunctDependencyTrackPoint.h` 85–86):
`{ disjunct_concept_linker: Vec<NegLink<ConceptId>>, disjunct_branch_stats: … }`.

### The 7 variants
```
enum DependencyNode {
    IndependentBase  { base: DepNodeBase },                                 // sentinel (DNTINDEPENDENTBASE)
    Deterministic    { base: DepNodeBase },                                 // 30 tag-only det kinds (AND, ATLEAST, SOME, SELF, DISTINCT, EXPANDED, IMPLICATION, CONNECTION, AUTOMATCHOOSE, BIND*, DATATYPE*, ORONLYOPTION, PROPAGATE*, REPRESENTATIVE{AND,IMPLICATION,BINDVARIABLE,GROUNDING}, RepresentativeResolve/Select, VARBIND{AND,GROUNDING,IMPLICATION,VARIABLE})
    DetLink          { base: DepNodeBase, prev: DepLinkId },                // 21 det kinds w/ 1 back-edge (ALL, AUTOMATTRANSACTION, BINDPROPAGATE{ALL,CYCLE}, DATAASSERTION, MERGED{CONCEPT,Individual,LINK}, NEGVALUE, NOMINAL, PROPAGATEBINDINGSSUCCESSOR, PROPAGATEVARIABLEBINDINGSSUCCESSOR, REPRESENTATIVE{ALL,JOIN}, RESOLVEREPRESENTATIVE, REUSEBACKENDVALUE, ROLEASSERTION, SAMEINDIVIDUALSMERGE, VALUE, VARBINDPROPAGATE{ALL,JOIN})
    DetLink2         { base: DepNodeBase, prev1: DepLinkId, prev2: DepLinkId }, // FUNCTIONAL only
    NonDeterministic { base: DepNodeBase, nd: NonDetData },                 // ATMOST, MERGE, QUALIFY, MERGEPOSSIBLEINSTANCEINDIVIDUAL, REUSEINDIVIDUAL, REUSEBACKEND{FIXED,PRIORITIZED}INDIVIDUALEXPANSION, REUSECOMPLETIONGRAPH, REUSECONCEPTS
    Or               { base: DepNodeBase, nd: NonDetData, disj: OrDisjunctTrackData }, // OR (CORDisjunctDependencyTrackPoint)
    ReuseBackendModes{ base: DepNodeBase, nd: NonDetData, involved: Vec<Cint64> },     // REUSEBACKENDEXPANSIONMODES (CXLinker<cint64>)
}
```
`DepKind` = a plain `#[repr(i64)]` enum of the 62 tags (the C++ `DEPENDENCNODEYTYPE`
values), stored in `base.kind`, so per-rule dispatch elsewhere stays exact.
`CDependency` → `Dependency { dep_track_point: TrackPointId, next: DepLinkId }`.
`ClashedDescriptor` (clash family) is a sibling tagged enum (§1 `ClashDescId`).

**Variant count: 7** (carrying a 62-value `DepKind` discriminant).

---

## 5. Dependency order for porting

Struct-defs first (nothing compiles otherwise), then methods, bottom-up so each
unit's referenced ids/structs already exist:

1. **`process/mod.rs` ids + SD-1** (tag bases, edge/descriptor structs). Depends
   only on W1 `model/` + `substrate`.
2. **SD-5 / dependency structs** (`DependencyNode` enum, `DependencyTrackPoint`,
   `Dependency`, `BranchTreeNode`, `DepKind`, clash enum). Referenced by node,
   databox, edge, restriction-spec fields.
3. **SD-4 satellite structs** (`ReapplyConceptLabelSet`, `ReapplyRoleSuccessorHash`,
   `ConceptProcessDescriptor`, `RestrictionSpec`) — node fields reference these ids.
4. **SD-3 `IndividualProcessNode` struct**, then **SD-4 `SaturationProcessNode`
   struct** (references node-reference + extension data).
5. **SD-2 `ProcessingDataBox` struct** (owns node vector + all queues + saturation
   linkers; references every id above).
6. **Method batches** — within each class, the `init*` unit first (it defines the
   buffer-handoff conventions every other method assumes):
   - **PN-1** (node init/clone) → **PN-2…PN-6**.
   - **DB-1** (databox lifecycle/save-restore) → **DB-2…DB-6**.
   - **LS-1, RS-1, BM-1, SAT-1** (each one unit; COW helpers first inside each).
   - **DEP-1, DEP-2** (dependency-node methods + branching tree) — last, since
     they consume node/databox/track-point state for backjumping.

Stub method bodies (`todo!()`) are acceptable at struct-def time so downstream
structs compile; fill per the method-batch units in wave W2.
