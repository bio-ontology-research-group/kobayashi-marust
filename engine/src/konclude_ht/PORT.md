# konclude_ht — direct, exact Rust port of the Konclude hypertableau algorithm

This module is a **function-by-function translation** of Konclude's hypertableau
reasoning algorithm from C++ into Rust, kept as faithful to the original control
flow and data model as Rust allows. It is a **new, self-contained module**: it
does not reuse KM's existing `hypertableau.rs` / `tableau.rs`. Once it compiles
and validates it will be wired into KM as an alternative reasoning core.

## Scope (decided)

**ENTIRE `Reasoner/Kernel/` — literal.** Algorithm (65k) + Process (93k) +
Calculation (1.9k) + Cache (36k) + Manager (5k) + Strategy (1.7k) + Task (6.5k)
≈ **209k LOC**. This is a months-scale, multi-wave effort; `PORT.md` is the
durable tracker so any session/agent can resume from the status table.

## License note (due diligence)

Konclude is LGPL-licensed. A function-by-function translation is a **derivative
work**: if KM with this module is ever distributed, the LGPL terms attach to the
ported module (notice retention, source availability, relink ability). This does
not affect private/research use. Keep this module dirctory self-contained and
LGPL-headed so the obligation stays scoped to `konclude_ht/` and is easy to honor
or excise. (Engineering flag only — the user owns the decision.)

## Source

Konclude (C++), local checkout at `/home/leechuck/Public/software/Konclude`.
The algorithm core lives in `Source/Reasoner/Kernel/`:

| C++ source | lines | role | Rust target |
|------------|------:|------|-------------|
| `Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.{h,cpp}` | 1.6k / 27.7k | the completion engine — all ~60 `apply*Rule` expansion rules + ~450 methods | `completion/` (split by rule group) |
| `Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.{h,cpp}` | / 8.5k | approximate saturation (the cheap pre-pass) | `saturation/` |
| `Calculation/*` | 1.9k | calculation controllers / task handles | `calculation/` |
| `Process/CProcessingDataBox.{h,cpp}` | 2.5k | the per-completion-graph state box | `process/databox.rs` |
| `Process/CIndividualProcessNode.{h,cpp}` | 2.2k | a node in the completion graph | `process/node.rs` |
| `Process/*` (≈40k total) | | dependency lines, reapply label sets, role-succ hashes, datatype value spaces | `process/*` |
| ontology concept model (`CConcept`/`CRole`/`CIndividual`, location TBD by inventory) | | the static concept/role operators the process model wraps | `model/*` |

(The peripheral Algorithm files — backend/association/completion-graph caches,
datatype value-space handlers, message analysers — are infrastructure around the
calculus; whether they are in scope is the one breadth decision noted below.)

## Porting conventions (every ported file MUST follow)

1. **Exact, function-by-function.** One Rust function per Konclude method, same
   name (snake_case of the C++ name, e.g. `applyALLRule` → `apply_all_rule`),
   same control flow, same branch structure, same order of operations. Do **not**
   refactor, merge, reorder, or "improve" the logic. When in doubt, mirror the C++.

2. **Deviation notes.** Where Rust forces or strongly favours a different
   approach (ownership/borrowing, the process/threading model, pointer aliasing,
   manual memory pools, `goto`, exceptions-as-control-flow), keep the port as
   close as possible AND mark it with a tagged comment:

   ```rust
   // KONCLUDE-PORT-NOTE[ownership]: C++ stores a raw CConcept* back-pointer here;
   // ported as an arena index `ConceptId` to avoid a self-referential borrow.
   // Behaviour is identical; only the representation differs.
   ```

   Tag taxonomy (use one): `[ownership]` `[memory-pool]` `[exceptions]`
   `[goto]` `[threading]` `[pointer-alias]` `[overload]` `[template]`
   `[int-width]` `[uninit]` `[macro]` `[api]` `[unclear]`. Use `[unclear]` when
   the original intent is genuinely ambiguous — flag, do not guess silently.

3. **Preserve names as anchors.** Keep the original C++ symbol name in a
   doc-comment on each ported item: `/// Port of `CClass::originalMethod`.` so the
   two trees can be diffed method-by-method.

4. **No behavioural changes for performance.** Performance-motivated Rust
   idioms are allowed ONLY when behaviour is provably identical; otherwise leave
   the faithful (even if slower) translation and add a `[memory-pool]`/`[ownership]`
   note describing the faster option for later.

5. **Memory model.** Konclude uses per-task bump/pool allocators and raw
   pointers heavily. The port uses **arena `Vec`s + typed integer ids**
   (`NodeId`, `ConceptId`, `DependencyId`, …) as the uniform replacement for
   `CClass*`. This is the single global `[ownership]` decision; individual sites
   reference it rather than re-explaining.

6. **Canonical linker (`CLinker`) convention** (W2 Wave-B; from `CLinker.cpp`,
   confirmed by the DB-6 agent). Konclude's intrusive singly-linked `CXxxLinker`
   chains are head-at-front, LIFO: `append(otherChain)` splices the other chain in
   front (prepend), so the idiom `mX = (new CXLinker())->init(…)->append(mX)` makes
   the new node the head. Collapsed to an owned `Vec<ElemId>`, the **head is the
   FRONT of the Vec**:
   - `addX(v)`  → `self.x.insert(0, v)`  (front-splice / prepend)
   - `takeX()`  → `remove(0)` of the head (guarded; `Id::NONE` when empty)
   - head-advance → `remove(0)`
   - `getX()`   → the chain as a slice in head→tail order
   - `setX(v)`  → replace (single-element chain, or empty for `Id::NONE`)

   The take ORDER (LIFO) is identical to a back-stack, but the slice/get order is
   not — every Wave-B linker uses head-at-front so `getX` matches the C++ head→tail
   traversal. (db5.rs originally modelled some chains head-at-back via `push`/`pop`;
   aligned to head-front to match db4/db6.)

## Architecture / wave plan (dependency-ordered)

- **W0 — inventory (in progress).** Parallel agents catalogue every port unit:
  the completion method list (grouped), the data-model classes (fields +
  methods), the saturation method list, and the upstream ontology concept model
  + the full type-dependency DAG. Output fills the status table below.
- **W1 — foundation types.** The ontology concept/role model + the core
  `Process/` structs (node, databox, dependency, reapply sets) as Rust types
  with stubbed method bodies. Everything downstream compiles against these.
- **W2 — data-model method bodies.** Fill the `Process/*` methods.
- **W3 — completion rules.** Port the ~60 `apply*Rule` methods + their helpers,
  in rule-family batches, against W1/W2.
- **W4 — saturation + calculation controllers.**
- **W5 — assembly + ws compile loop.** Wire `mod.rs`, resolve type mismatches,
  build on ws (never the laptop), then validate behaviour against Konclude on a
  small fragment before any benchmark.

## W0 inventory results (manifests under `manifest/`)

- `00-type-dag.md` — 219 external types, 8 dependency layers L0→L7, no cross-layer
  cycles; within-layer cycles (node↔edge, node↔dep-node, ctx↔algo) resolved by
  arena ids. Most-referenced: `CIndividualProcessNode` (563), `CCalculationAlgorithmContextBase` (546).
- `01-completion-methods.md` — 554 method defs / 24,882 body lines in 16 families;
  **36 port units** (≤~830 lines each). Biggest: `handleTask` (800), `takeNextProcessIndividual` (601), `mergeIndividualNodeInto` (553).
- `02-process-model.md` — **347 top-level classes** + `Dependency/` (151 files, ~75
  dep-node types → ONE tagged enum) + `Marker/`. Core: `CProcessingDataBox` (209
  fields/265 methods), `CIndividualProcessNode` (143/~320), `CIndividualSaturationProcessNode`,
  `CReapplyConceptLabelSet`, `CReapplyRoleSuccessorHash`, `CBranchingMergingProcessingRestrictionSpecification`.
- `03-saturation-calc.md` — saturation 195 methods → **12 units**; entry controller
  `CConcurrentTaskCalculationManager` (per-thread algorithm + memory pool, event-driven `CTask`).
- `04-ontology-model.md` — `CConcept`/`CRole`/`CIndividual` in `Reasoner/Ontology/`;
  operator codes = `static const qint64 CCxxx` in `OntologySettings.h`, dispatched
  via `CConceptOperator` flag groups (`CCFS_ALL_AQALL_TYPE`, …).

## Status table (one row per port unit — keep updated as waves land)

**W1 COMPLETE (2026-06-29): the foundation (`model/`) compiles on ws —
`cargo check --release` exit 0, 0 warnings.** Methodology proven end-to-end
(translate → reconcile → compiles). W2 (`process/`) decomposition next.

**W2 Wave-A + Wave-B COMPLETE (2026-06-29): the full `process/` data model
compiles on ws — `cargo check --release` exit 0, 0 konclude_ht errors** (the
10 Wave-B method-body units db2–db6 / pn2–pn6 wired into `process/mod.rs`,
reconciled, compiled). Two node.rs fidelity bugs fixed vs C++; db5 linker ops
aligned to the canonical head-front convention. No PORT-PENDING `todo!`s; the
only deferrals are the `W2-DEFER[api]` satellite lazy-allocations (stub structs,
to be filled when their satellite types are ported). W3 (completion rules) next.

**W3 struct-skeleton COMPLETE (2026-06-29): the completion-engine STRUCT
DEFINITIONS compile on ws — `cargo check --release` exit 0, 0 konclude_ht
warnings.** Three new files under `completion/`: the per-thread algorithm context
(`context.rs`, Layer 7) and the completion task-handle algorithm fields
(`algorithm.rs`), over a `completion/stubs.rs` of Algorithm-layer placeholder
markers (the Process-layer queue/hash markers are reused from `process::stubs`).
Key decisions: (1) the context — not an arena element, one PER WORKER THREAD — is
a plain owned struct, so there are NO completion-layer `Id` aliases; (2) per
type-dag §4 the per-thread context OWNS the completion-graph state, so the single
`CProcessingDataBox` is held BY VALUE in `CalculationAlgorithmContext`, and the
`mProcessingDataBox` back-pointers on the derived context + the algorithm are
opaque `Cint64` aliases of it; (3) memory allocators / `CProcessContext` / Qt
timers / the `TableauRuleFunction` member-fn-pointer jump tables become opaque
`Cint64` (the jump tables are fixed `[Cint64; 200]`); (4) the 8 satisfiable-task
message analysers are held by value as zero-size markers. NO method bodies yet —
they are the `u01..u36` batches (`// W3 method-batch: u01..u36` marker in
`algorithm.rs`).

**W3 method bodies — validation sub-wave u01–u06 ported (2026-06-29), KEYSTONE
FINDING.** The first 6 completion units (core loop u01–u04, expansion rules
u05–u06) translate with faithful control flow, but most bodies are deferred for
ONE structural reason, consistent across all six: **the algorithm has no concrete
arena to resolve `NodeId`/`ConceptId`/`ConProcDescId`/descriptor ids into
objects.** The databox is reachable (held by-value in the context, so its queue
getters wire live), but the per-test node/concept/descriptor **arenas live in the
opaque `CProcessContext`** the struct wave stubbed as `Cint64`. So every
`indi->...` / `concept->...` dereference is currently a `W3-DEFER[api]` stub.
⇒ **NEXT, before more W3 units: port `CProcessContext` as the concrete
arena-owning context** (`Arena<IndividualProcessNode>`, `Arena<ConceptDescriptor>`,
`Arena<Concept>`, … held by the context), and thread `&mut Ctx` through the
completion + process methods so id-derefs resolve. This unblocks the W3 bodies
(they fill in faithfully instead of deferring) and is the concrete realisation of
substrate.rs's deferred "task context owns the arenas" decision. The 6 ported
units stay (their structure is correct); they get a reconcile pass once the
context lands. Porting more u07..u36 first would only generate more stubs.

**W3.5 — the `ProcessContext` arena container LANDED (2026-06-29): the keystone
that closes the arena-resolution gap; `cargo check --release` exit 0, 0
konclude_ht warnings.** `CProcessContext` (Konclude
`Reasoner/Kernel/Process/CProcessContext.{h,cpp}`, a per-test `CTaskContext`) is
the per-test ownership root: it holds `mUsedMemMan`, the single
`CProcessMemoryPoolAllocationManager` from which EVERY per-test object
(`CIndividualProcessNode`, descriptors, dependency nodes, satellites, …) is
bump-allocated; the databox's `mIndividualProcessNodeVector` etc. only TRACK
those pooled objects. The port (`process/context.rs`) realises that single
typeless pool as **16 typed `Arena<T>` fields**, one per per-test object kind,
each indexed by the matching `Id<T>` already aliased in `process/mod.rs`:
- nodes (`Arena<IndividualProcessNode>`), sat-nodes;
- the 3 edge kinds (link / distinct / disjoint);
- the 3 descriptor kinds (concept / concept-process / clash);
- the 5 dependency arenas (dep-node enum / track-point / dep-link / branch-tree /
  branching-instruction);
- the 3 satellite arenas (label-set / role-succ-hash / restriction-spec).
Plus the opaque `mUsedMemMan`/tagger/stats handles `CProcessContext` declares.

**Accessor convention (the C++ pointer-deref replacement).** Each arena exposes a
trio `get / get_mut / alloc` with a per-kind stem:
`node/node_mut/alloc_node`, `con_desc/con_desc_mut/alloc_con_desc`,
`dep_node/dep_node_mut/alloc_dep_node`, … (generated by an `arena_accessors!`
macro). The mapping is:

| C++                              | Rust (port)                                     |
|----------------------------------|-------------------------------------------------|
| `indi->getX()`                   | `ctx.node(id).get_x()`                          |
| `indi->setX(v)` (mutating)       | `ctx.node_mut(id).set_x(v)`                     |
| `new CIndividualProcessNode(…)`  | `ctx.alloc_node(IndividualProcessNode::new(…))` |

So a W3 completion-method body that today writes `// W3-DEFER[api]` because it
cannot resolve a `NodeId` will, on its reconcile pass, write
`ctx.used_process_context().node(id).…` (read) or `…_mut(id)` (mutate). The
`ProcessContext` is reached from the calculation context as
`CalculationAlgorithmContext::used_process_context()` / `_mut()`.

**Static terminology home.** `CConcept`/`CRole`/`CIndividual`/`CVariable` do NOT
live in the process context — they are the TBox/RBox, shared read-only across
tests. They get `model::ontology::OntologyArenas` (4 `Arena<T>` + the same
`concept/role/individual/variable` accessor trio convention), held by value on
the calculation context only as a reachability vehicle (note: semantically
shared, not per-test).

**Wiring.** `completion/context.rs`: the opaque `used_process_context: Cint64`
on `CalculationAlgorithmContext` became `used_process_context: ProcessContext`
held BY VALUE (the same idiom as the by-value `used_processing_data_box`); an
`ontology_arenas: OntologyArenas` field was added alongside; and the Base's
`process_context: Cint64` is now documented as an opaque alias of
`base.used_process_context`. Accessors `used_process_context{,_mut}` /
`ontology_arenas{,_mut}` added (+ Base forwarders). No W2 process files needed
changes (the struct/enum names the arenas reference already existed). The u01–u06
bodies are unchanged; they reconcile in the next wave.

**W3 method bodies u01–u36 RECONCILED + WIRED (2026-06-29): the whole
`completion` module compiles on ws — `cargo check --release` exit 0, 0
konclude_ht errors (24 benign warnings: dead code / never-read assignments in
PORT-PENDING stub bodies).** The 36 parallel-authored units (~31.5k lines) were
wired into `completion/mod.rs` (`pub mod u01..u36` + `pub mod strategy` +
`pub mod pending`) and the cross-unit disagreements reconciled (95 → 0 errors).
Error-class taxonomy + canonical decisions:
- **DUPLICATES (E0592, 2):** `can_delay_representative_neighbour_expansion` /
  `delaying_representative_neighbour_expansion` were independently ported in both
  u25 and u27 with identical faithful signatures; kept u25 (richer PORT-PENDING
  detail), deleted u27's copies.
- **NAME mismatches (E0599):** call sites aligned to the DEFINITION name —
  `create_reuse{individual,concepts}_dependency`, `create_role_assertion_dependency`.
  Two were the reverse: the typo-faithful C++ name wins — `addtriggeredValueSpaceConcepts`
  → `addtriggered_value_space_concepts` (NOT `add_triggered_…`; C++ really is
  lowercase-t), and `get_branching_tag` added to `DependencyTrackPoint` (C++
  `CBranchingTag::getBranchingTag()`; u29 had called the wrong `get_branching_level`).
- **`&mut NodeId` vs `NodeId` (E0308/E0596, ~60):** canonical = the Konclude header.
  `CIndividualProcessNode*&` → `&mut NodeId` (node-advancing getters
  `getAncestorIndividual` / `getSuccessorIndividual` / `individualNodeInitializing`
  / `mergeIndividualNodeInto` / …); `CIndividualProcessNode*` → `NodeId` by value
  (`getUpToDateIndividual`, the dependency-factory wrappers). Applied via `cargo
  fix` for the machine-applicable borrows + `let mut`/`mut <param>` follow-ups.
  `getUpToDateIndividual(cint64)` overload split → `get_up_to_date_individual_by_id`.
- **SIGNATURE mismatches (E0061/E0308):** `add_concepts_to_individual` trailing
  `cint64* conceptCount` → `Option<&mut Cint64>` (u34/u08 call sites pass `None`;
  u08's stray `RestrictionSpecId` was the bug). `createNewIndividualsLinksReapplyed`
  role-linker arg unified to `&[NegLink<RoleId>]` (u34 calls now snapshot
  `role.get_indirect_super_role_list()` before the `&mut`-ctx call, `[ownership]`).
  The blocking family (`is_nominal_/is_anonymous_variable_propagation_binding_*`)
  realigned to the full `block_data: IndiBlockDataId` / `test_continue_blocking` /
  `block_alt_data` param list. `containsIndividualNodeConcepts` label-set overload
  (Rust can't overload) → new `contains_individual_node_concepts_for_label_set`.
- **pending.rs:** one W3-RECONCILE-STUB added —
  `contains_individual_node_concepts_for_label_set` (the `CReapplyConceptLabelSet*`
  overload). All other gaps were name/signature realignments, not missing siblings.

**W4 saturation units s01–s12 RECONCILED + WIRED (2026-06-29): the whole
`saturation` module compiles on ws — `cargo check --release` exit 0, 0
konclude_ht errors (44 benign warnings: dead code / never-read PORT-PENDING stub
bodies).** The 12 parallel-authored units (~10.2k lines) were wired into
`saturation/mod.rs` (`pub mod s01..s12` + `pub mod pending`) and `konclude_ht/mod.rs`
(`pub mod saturation` uncommented). The cross-unit disagreement count was tiny —
**7 → 0 errors**, all in the same classes W3 saw, NO duplicate method defs and NO
missing siblings (pending.rs stayed empty). Error-class taxonomy + canonical
decisions:
- **TYPE divergence — linker payload vs linker id (E0308, 4):** the canonical
  saturation rule-dispatch type is `ConceptSaturationProcessLinkerId`
  (`= Id<ConceptSaturationProcessLinker>`; what `take_concept_saturation_process_linker`
  returns and `apply_tableau_saturation_rule` / `apply_some_rule` take). Two defs
  diverged: s11 `release_concept_saturation_process_linker` took the *payload*
  marker `Id<ConceptSaturationProcess>` and s02 `create_successor_for_concept` took
  the s02-local opaque `ConceptSaturationProcessLinkerHandle = Cint64`. Both realigned
  to `ConceptSaturationProcessLinkerId`. The databox boundary
  (`add_remaining_concept_saturation_process_linker`, in the already-compiling
  `process/db5.rs`) keeps its `Id<ConceptSaturationProcess>` payload key; the s11
  body converts via the shared raw index (`Id::new(linker.raw)`), faithful to the
  C++ payload/linker split — NO change to `process/`.
- **`&mut SatNodeId` vs `SatNodeId` (E0308, 2):** `update_direct_adding_individual_status_flags`
  takes `SatNodeId` by value (the status-update helper is non-node-advancing; most
  callers pass by value). The two s03 BOTTOM/clash rule call sites held `process_indi`
  as `&mut SatNodeId` and were deref'd at the call (`*process_indi`).
- **NAME mismatch (E0599, 1):** s10 called `add_concept_filtered_to_individual_for_label_set`;
  the definition (s11) is `add_concept_filtered_to_individual_label_set` (no `_for_`).
  Call aligned to the definition name.
- **Borrow (E0384, 1):** s10 `get_resolved_individual_node_extension_for_node_created`
  reassigns its `resolve_data` param → `mut resolve_data` (`[ownership]`).
- **pending.rs:** ZERO W4-RECONCILE-STUB siblings needed (the file is wired but
  empty); every gap was a name/type realignment, none a missing sibling. NO sat-node
  accessors or status-flag consts were missing — s11's status-flag masks + bitops
  and the s-units' `IndividualSaturationProcessNode` accessors all resolved against
  `process/sat_node.rs` as-authored.

Legend: ☐ todo · ◐ in progress · ☑ ported (pre-compile) · ✓ compiles · ★ validated

| wave | unit | source | rust target | status |
|------|------|--------|-------------|--------|
| W1 | substrate (ids/arena/trail/linker) | (port design, [ownership]) | `model/substrate.rs` | ✓ (`Id<T>` Copy/Eq/Hash hand-impl'd, no `T:` bound — derive would wrongly require `T: Copy`) |
| W1 | model stubs (placeholder ids) | (port design, [api]) | `model/stubs.rs` | ✓ (RoleChain/RoleData/Terminology/Name ids shared by role.rs + later units) |
| W1 | operator codes + CConceptOperator | `Ontology/OntologySettings.h`,`CConceptOperator.h` | `model/op.rs` | ✓ (63 codes/62 flags/21 group preds; 1 [unclear]: `has_all_operator_code_flags` name≠logic, ported verbatim) |
| W1 | CConcept | `Ontology/CConcept.{h,cpp}` | `model/concept.rs` | ✓ (name-linker now `Vec<NameId>` for CNamedItem coherence) |
| W1 | CRole | `Ontology/CRole.{h,cpp}` | `model/role.rs` | ✓ (22 fields/9 flags/~102 methods; placeholder ids relocated to `model/stubs.rs`) |
| W1 | CIndividual + CVariable | `Ontology/CIndividual.{h,cpp}`,`CVariable.*` | `model/individual.rs` | ✓ (inherited CTagItem/CNamedItem inlined; name-linker now `Vec<NameId>`; opaque CDataLiteral* as Cint64) |
| W2 | process core (6 classes) | `Process/` core set | `process/*.rs` (edge/descriptor/node/sat_node/satellites/databox) | ✓ (struct-def units; the ~90 not-yet-ported placeholder markers the 5 SD agents declared independently were consolidated into one `process/stubs.rs`, resolving the `ConceptSaturationDescriptor` sat_node/databox divergence) |
| W2 | dependency spine (→1 enum) | `Process/Dependency/` | `process/dependency.rs` | ✓ (64-value `DepKind` + 7-variant `DependencyNode` enum + track-point/dep-link/branch-tree/branching-instruction records; compiles) |
| W2 Wave-A | PN-1 node method bodies | `CIndividualProcessNode.cpp` | `process/pn1.rs` | ✓ (init/ctor/buffer-handoff) |
| W2 Wave-A | DB-1 databox lifecycle | `CProcessingDataBox.cpp` | `process/db1.rs` | ✓ (lifecycle / save-restore) |
| W2 Wave-A | SAT-1 saturation-node bodies | `CIndividualSaturationProcessNode.cpp` | `process/sat1.rs` | ✓ |
| W2 Wave-A | LS-1 label-set bodies | `CReapplyConceptLabelSet.cpp` | `process/ls1.rs` | ✓ (COW init_concept_label_set ported byte-exact) |
| W2 Wave-A | RS-1 role-succ-hash bodies | `CReapplyRoleSuccessorHash.cpp` | `process/rs1.rs` | ✓ |
| W2 Wave-A | BM-1 branching-merging spec bodies | `CBranchingMergingProcessingRestrictionSpecification.cpp` | `process/bm1.rs` | ✓ |
| W2 Wave-A | DEP-1 dependency-node/link/track-point bodies | `Process/Dependency/` | `process/dep1.rs` | ✓ (owns DependencyLink chain ops + plain track-point accessors) |
| W2 Wave-A | DEP-2 track-point/branch-tree/branching-instr bodies | `Process/Dependency/` | `process/dep2.rs` | ✓ (6 DependencyLink/track-point accessors deduped to DEP-1) |
| W2 Wave-B | PN-2 node assertion/init-concept/flag bodies | `CIndividualProcessNode.cpp` | `process/pn2.rs` | ✓ |
| W2 Wave-B | PN-3 node role-succ/link/blocked-linker bodies | `CIndividualProcessNode.cpp` | `process/pn3.rs` | ✓ |
| W2 Wave-B | PN-4 node cache/block-data/restriction-flag bodies | `CIndividualProcessNode.cpp` | `process/pn4.rs` | ✓ |
| W2 Wave-B | PN-5 node signature-block/back-dependency bodies | `CIndividualProcessNode.cpp` | `process/pn5.rs` | ✓ |
| W2 Wave-B | PN-6 node nominal-reactivation/conn-set lazy getters | `CIndividualProcessNode.cpp` | `process/pn6.rs` | ✓ (satellite lazy-alloc `W2-DEFER[api]` — stub structs) |
| W2 Wave-B | DB-2 databox id-counters/hash getters | `CProcessingDataBox.cpp` | `process/db2.rs` | ✓ |
| W2 Wave-B | DB-3 databox processing-queue getters/clears | `CProcessingDataBox.cpp` | `process/db3.rs` | ✓ |
| W2 Wave-B | DB-4 databox blocking-candidate/node-linker bodies | `CProcessingDataBox.cpp` | `process/db4.rs` | ✓ |
| W2 Wave-B | DB-5 databox saturation subsystem (linkers + satellites) | `CProcessingDataBox.cpp` | `process/db5.rs` | ✓ (linker ops aligned head-front; satellite lazy-alloc `W2-DEFER[api]`) |
| W2 Wave-B | DB-6 databox incremental/backend-cache bodies | `CProcessingDataBox.cpp` | `process/db6.rs` | ✓ |
| W2 fidelity | node.rs vs C++ fixes (PN-2/PN-4 flags) | `CIndividualProcessNode.cpp` | `process/node.rs` | ✓ `set_individual_node_id` merge-into guard + `has_merged_into_individual_node_id` (`!= mIndiID`) |
| W3 struct | completion-layer Algorithm stubs | (port design, [api]) | `completion/stubs.rs` | ✓ (strategies/factories/14 cache handlers/8 by-value analysers/config-ext markers; Process-layer queue markers reused from `process::stubs`) |
| W3 struct | algorithm context (`mUsed*` + `m*`) | `Algorithm/CCalculationAlgorithmContext{,Base}.h` | `completion/context.rs` | ✓ (`CalculationAlgorithmContext` 26 fields OWNS the databox by value per type-dag §4; `CalculationAlgorithmContextBase` folds it in as `base` + 21 fields; databox back-refs = opaque `Cint64` aliases) |
| W3 struct | completion algorithm fields | `Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.h` | `completion/algorithm.rs` | ✓ (`CompletionTaskHandleAlgorithm` 332 fields = all 335 `.h` members less 3 static-const→`const`; `// W3 method-batch: u01..u36` marker for bodies) |
| W3.5 | CProcessContext arena container | `Process/CProcessContext.{h,cpp}` | `process/context.rs` | ✓ (16 typed `Arena<T>` per-test pools + `get/get_mut/alloc` accessor trio per kind via `arena_accessors!`; opaque mem-man/tagger/stats handles) |
| W3.5 | static terminology arenas | `Reasoner/Ontology/` (TBox/RBox) | `model/ontology.rs` | ✓ (`OntologyArenas`: 4 read-shared `Arena<T>` + `concept/role/individual/variable` accessor trio) |
| W3.5 | wire container into calc context | `Algorithm/CCalculationAlgorithmContext.h` | `completion/context.rs` | ✓ (`used_process_context` now `ProcessContext` by-value; `ontology_arenas` added; Base `process_context` = opaque alias) |
| W3 | completion units 1–36 | completion `.cpp` | `completion/u01..u36.rs` | ✓ (wired + reconciled; `cargo check --release` exit 0, 0 errors) |
| W8 | main driver loop live (take-next + rule dispatch) | `…CompletionTaskHandleAlgorithm.cpp` 2190-2790 / 9496-9549 | `completion/u02.rs` `take_next_process_individual`, `completion/u03.rs` `tableau_rule_processing`/`tableau_rule_choice` | ✓ (3 driver `todo!`s → live; jump table → `match` into `apply_*_rule`; cache-testing + sorted-nominal probes LIVE, queue-contents arms `W3-DEFER`; `cargo check --release` exit 0) |
| W8.1 | processing-queue subsystem (the triple-buffered queues) | `Process/CIndividual{Unsorted,LinkerRotation,Depth}ProcessingQueue.{h,cpp}`, `CConceptProcessingQueue.{h,cpp}`, `CIndividualDepthPriority`, `CConceptProcessingPriorityQueueData` | `process/queues.rs` (+ context/db3/stubs/u01/u02/u04 + completion/context forwarders) | ✓ (4 real queues + 2 helpers; 4 arenas on `ProcessContext`; db3 22/24 getters + 14 u02 probes + `continue_individual_processing` + u01 concept take-next un-defered; `cargo check --release` exit 0) |
| W3 | Strategy/ policies | `Reasoner/Kernel/Strategy/` | `completion/strategy.rs` | ✓ |
| W3 | reconcile sibling stubs | (W3-RECONCILE, [api]) | `completion/pending.rs` | ✓ (1 stub: label-set `containsIndividualNodeConcepts` overload) |
| W4 | saturation struct fields | `…SaturationTaskHandleAlgorithm.h` | `saturation/algorithm.rs` | ✓ (member fields + 7 rule-count getters + ctor `new()`) |
| W4 | saturation-layer stubs | (port design, [api]) | `saturation/stubs.rs` | ✓ (2 by-value analysers + occ-stat collector + backend-cache handler markers) |
| W4 | saturation units 1–12 | saturation `.cpp` | `saturation/s01..s12.rs` | ✓ (wired + reconciled; `cargo check --release` exit 0, 0 errors; 7→0) |
| W4 | reconcile sibling stubs | (W4-RECONCILE, [api]) | `saturation/pending.rs` | ✓ (0 stubs needed — all gaps were name/type realignments) |
| W4.5 | saturation-layer per-test satellites | `Process/` (9 saturation classes) | `saturation/satellites.rs` | ✓ (9 classes ported; 9 arenas + trios on `ProcessContext`; 5 SD-4 stub ids re-aliased/re-exported; 3 s11 create-pool allocs un-defered; `cargo check --release` exit 0) |
| W2.7 | process satellites (varbind/distinct/reapply_sat) | `Process/` (var-binding-path, distinct/conn-succ/disjoint-role, reapply/sig-block/inc-exp) | `process/{varbind,distinct,reapply_sat}.rs` | ✓ (wired + reconciled; 15 arenas + trios on `ProcessContext`; 5 W2 stub ids re-aliased to real structs; `cargo check --release` exit 0, 1→0 errors; W2.7-DEFER bodies kept) |
| W3b | node lazy-getter keystone (2 binding hashes + condensed-reapply iterator + 6 ctx lazy-getters) | `CConcept{Variable,Propagation}BindingSet…Hash.{h,cpp}`, `CCondensedReapplyQueueIterator.{h,cpp}`, `CIndividualProcessNode.cpp` lazy getters | `process/binding_hash.rs` + `process/reapply_sat.rs` + `process/context.rs` | ✓ (3 new arenas + trios; 2 stub ids re-aliased; 6 `ctx.node_*` context-threaded lazy-getters; `cargo check --release` exit 0) |
| W3c | propagation-binding subsystem (the W3b-deferred set) | `CPropagationBinding{,Set,Descriptor,Map,MapData}.{h,cpp}`, `CPropagationBindingReapplyConceptDescriptor.{h,cpp}` | `process/propagation_binding.rs` + `process/{binding_hash,context}.rs` | ✓ (6 classes ported; 4 new arenas + trios on `ProcessContext`; W3b `PropagationBindingSet`/`Descriptor` placeholders re-aliased to the real structs; `getPropagationBindingSet` localise-alloc un-defered; reapply-hash + 2 transition extensions kept as W3c-DEFER markers; `cargo check --release` exit 0) |
| W3.5r | representative variable-binding-path-set subsystem (the u17/u33-deferred reps) | `CRepresentativeVariableBindingPathSet{Data,MigrateData,DataSignature}.{h,cpp}`, `CRepresentativeContainingMap{,Data}.{h,cpp}`, `CRepresentativePropagation{Set,Map,MapData,Descriptor}.{h,cpp}` | `process/representative.rs` + `process/{context,mod,varbind}.rs` | ✓ (9 classes ported; 4 new arenas + trios on `ProcessContext`; the W2.7-DEFER opaque `Cint64` rep-set-data marker in `varbind::RepresentativeVariableBindingPathMapData` re-aliased to the real `RepresentativeVariableBindingPathSetDataId`; per-set joining hash kept as a W3.5r-DEFER marker; isolated `cargo check --release` exit 0) |
| W3c | dependency factory (the create*Dependency allocator) | `Algorithm/CDependencyFactory.{h,cpp}` | `completion/dependency_factory.rs` | ✓ (7 per-variant `alloc_*_dependency_node` on `ProcessContext` + `materialize_continue_dependency_track_point`; additive, wrappers not yet switched; `cargo check --release` exit 0) |
| W3c | clash/stop propagation mechanism | `Algorithm/CCalculation{Clash,Stop}ProcessingException.{h,cpp}` | `completion/clash.rs` + `completion/context.rs` | ✓ (`CalcSignal` enum + `pending_signal` context field + `raise_clash`/`raise_stop`/`has_pending_signal`/`take_pending_signal`; additive; `cargo check --release` exit 0) |
| W3.6 | node-resolution keystone (tagger + node-vector + 5 resolvers) | `Process/CProcessTagger`,`CIndividualProcessNodeVector`, `…CompletionTaskHandleAlgorithm.cpp` 22477–22510 / 26412–26488 | `process/node_resolution.rs` (+ databox/context/edge/pn1 fields) | ✓ (real `CProcessTagger` + `CIndividualProcessNodeVector` by value; ctx-level resolvers on `CalculationAlgorithmContextBase`; `cargo check --release` exit 0) |
| W3.5b | blocking-family satellites (candidate hash/data/iterator + sig-block concept-expansion) | `Process/CBlockingIndividualNodeCandidate{Data,Hash,Iterator}.{h,cpp}`, `CSignatureBlockingIndividualNodeConceptExpansionData.{h,cpp}` | `process/blocking_hash.rs` (+ context/stubs/databox/db4) | ✓ (4 classes ported; 3 new arenas + trios; `SigBlockConExpDataId` re-aliased; databox/db4 `SignatureBlockingCandidateHash` + `BlockingIndividualNodeCandidateHash` un-wired onto real structs; `cargo check --release` exit 0) |
| u15 | merge/nominal process satellites (merging hash + condensed-reapply queue + succ-role hash backend) | `Process/CIndividualMergingHash{,Data}.{h,cpp}`, `CCondensedReapplyQueue.{h,cpp}`, `CSuccessorRoleHash.{h,cpp}` (+ `CSuccessorRole`/`CSuccessor` iterators) | `process/{merging_hash,condensed_reapply,succ_role_hash}.rs` (+ context/stubs/mod/satellites/ls1/pn3) | ✓ (5 classes ported; 2 new arenas + trios; `SuccRoleHashId`+`IndividualMergingHashId` stub ids re-aliased to real structs; placeholder `satellites::CondensedReapplyQueue` re-exported from `condensed_reapply` + 6 unit-construction sites reconciled to `::new()`/value-share; 5 `ctx.node_*` context-threaded succ/disjoint iterators seed the real hashes; `cargo check --release` exit 0) |
| W4 | calculation controllers | `Calculation/` | `calculation/*.rs` | ☐ |
| W6 | Cache / Manager / Strategy / Task | resp. subtrees | `cache/`,`manager/`,… | ☐ |
| W6 cache-skeleton | cache struct skeleton (F0–F8, 9 families) | `Reasoner/Kernel/Cache/` | `cache/{base,value,unsat,reuse,satnode,consequences,sigexpand,occstats,events,backend,backend_data}.rs` | ✓ (`cache/mod.rs` wires all 11 files; `cargo check --release` exit 0, warnings only) |
| W6 cache-methods | family method bodies + F1 facade thirds | `Reasoner/Kernel/Cache/*.cpp` | `cache/backend_facade{1,gap,2,3}.rs` + the 9 family files | ✓ (wired + reconciled; `cargo check --release` exit 0, 0 errors; 0→0 — the parallel authors stayed self-consistent) |
| W6 task | scheduler + satisfiable-task subtree (8 files) | `Reasoner/Kernel/Task/` | `task/{scheduler,config,satisfiable_task,task_data,adapters,status_propagator,callback_executer,stats}.rs` | ✓ (created `task/mod.rs`; wired into `konclude_ht/mod.rs`; `cargo check --release` exit 0, 0 errors; 7→0) |
| W6 calculation | manager/environment/factory/builder controllers | `Reasoner/Kernel/Calculation/` | `calculation/{manager,environment,env_factory,factory,builder}.rs` | ✓ (wired into `konclude_ht/mod.rs`; builder→completion/saturation linkage resolves; 0 errors) |
| W6.5 cache-arena | CacheContext arena container (the cache analogue of ProcessContext) | `Reasoner/Kernel/Cache/*Context.{h,cpp}` (per-family pools, collapsed) | `cache/context.rs` | ✓ (64 typed `Arena<T>` per cache record family + `get/get_mut/alloc` trio via local `cache_arena_accessors!`; standalone root; `cargo check --release` exit 0) |

### W4.5 saturation-layer satellites (2026-06-30): WIRED + COMPILES, exit 0

Ported the per-test saturation satellites the `s02..s12` bodies allocate and
thread, in one new file `saturation/satellites.rs` (9 classes,
pointer→`Id`, intrusive `CLinker`/`CNegLinker`→`next: Id<Self>` head-front,
`CXNegLinker<CRole*>`→`Vec<NegLink<RoleId>>`, `CPROCESSHASH`/`CPROCESSMAP`→owned
`HashMap`):

- **Fully ported (struct + ctor + all trivial methods):** `CConceptSaturationDescriptor`
  (`getConcept`/`getConceptTag`/`getTerminologyTag` resolve the wrapped `ConceptId`
  against `OntologyArenas`, the descriptor.rs pattern), `CConceptSaturationProcessLinker`,
  `CRoleSaturationProcessLinker`, `CBackwardSaturationPropagationLink`,
  `CSaturationSuccessorData`, `CLinkedRoleSaturationSuccessorData`,
  `CConceptSaturationDescriptorReapplyData`.
- **Struct + ctor + accessors, complex bodies kept `W4.5-DEFER`:**
  `CLinkedRoleSaturationSuccessorHash` (the `addLinkedSuccessor`/`hasActive…` family
  needs the opaque `CSaturationSuccessorExtensionData` / `…RoleAssertionLinker`),
  `CIndividualSaturationProcessNodeExtensionData` (only `mLinkedRoleSuccHash` resolves
  to a real type; the other ~12 sub-struct lazy create-getters stay opaque `Cint64`),
  `CReapplyConceptSaturationLabelSet` (init/copy + count/linker/flag accessors +
  `containsConceptOrReapllyQueue`; the insert/iterator surface needs
  `CImplicationReapplyConceptSaturationDescriptor` / `CSaturationModifiedProcessUpdateLinker`
  / `CConceptSetFlags`).
- **Arenas: 9 added to `ProcessContext`** (per the W2.7/W3b convention — saturation
  per-test state lives on the same `ProcessContext` that owns the `sat_nodes` arena,
  not a separate context; `saturation/algorithm.rs` holds its `calc_alg_context` as an
  opaque `Cint64` and reaches the arenas via the threaded `&mut CalculationAlgorithmContextBase`).
  Each got its `arena_accessors!` trio + `Arena::new()` init + import.
  KONCLUDE-PORT-NOTE: these are *Process/*-layer classes; the new file lives under
  `saturation/` per the task and `process/context.rs` imports it from
  `super::super::saturation::satellites` (a same-crate module cycle, legal in Rust).
- **Stub reconcile (the W2.7 re-alias pattern):** the 5 SD-4 markers
  (`ConceptSaturationDescriptor`, `ConceptSaturationProcessLinker`,
  `BackwardSaturationPropagationLink`, `ReapplyConceptSaturationLabelSet`,
  `IndividualSaturationProcessNodeExtensionData`) removed from `process::stubs`'s
  `stub_id!` blocks; their ids re-aliased and struct names re-exported (`pub use`)
  from `saturation::satellites`. Names unchanged → `sat_node.rs` / `db5.rs` /
  s-unit `use super::stubs::{…}` sites keep resolving onto the real arena structs,
  including `Id<ConceptSaturationDescriptor>` in db5 + s11.
- **Un-defered (sole blocker = the satellites): 3 s11 create-pool branches** —
  `createConceptSaturationDescriptor` (→ `alloc_con_sat_desc`),
  `createConceptSaturationProcessLinker` + `createRoleSaturationProcessLinker`
  (→ `alloc_*` then payload-id `Id::new(raw)`, mirroring the existing `release*`
  payload/linker split). Faithful to the C++ `if (pool empty) allocateAndConstruct`.
  The remaining s02–s12 `W4-DEFER` bodies have OTHER blockers (datatype / descriptor
  / backend-cache / extension-data sub-structs) and were left as-is.
- **Error trajectory: exit 0 throughout** (purely additive; one stale-cache
  false-positive unused-import warning on `s11.rs:114` cleared on `touch`+rebuild).
  `cargo check --release` on ws exit 0, 0 konclude_ht errors. Completion / cache /
  task / calculation / the W4 saturation units untouched and still compile.

### W3c propagation-binding subsystem (2026-06-30): WIRED + COMPILES, 0→0 errors

Ported the propagation-binding subsystem that W3b deferred (`binding_hash.rs`'s
`getPropagationBindingSet` localise branch was a `W3b-DEFER[api]` waiting on the set
type). New file `process/propagation_binding.rs` ports six classes faithfully
(pointer→`Id`, intrusive `CLinkerBase`→folded `data`/`next`, `CDependencyTracker`→
`dep_track_point`, `CPROCESSMAP`→by-value `HashMap`): `CPropagationBinding`,
`CPropagationBindingDescriptor`, `CPropagationBindingReapplyConceptDescriptor`,
`CPropagationBindingMapData`, `CPropagationBindingMap`, `CPropagationBindingSet`.

- 4 new arenas + `arena_accessors!` trios on `ProcessContext` (`prop_bindings`,
  `prop_binding_descs`, `prop_binding_reapply_con_descs`, `prop_binding_sets`); the
  map/map-data are held by value (no arena). Imports + `Arena::new()` inits wired.
- `binding_hash.rs`: the two W3b placeholder markers (`PropagationBindingSet`,
  `PropagationBindingDescriptor`) deleted and re-exported (`pub use`) from
  `propagation_binding`, so all existing `binding_hash::PropagationBinding…` paths keep
  resolving. The `getPropagationBindingSet` localise alloc is un-defered with the exact
  lift-init-restore idiom of the `getVariableBindingPathSet` sibling.
- W3c-DEFER (own units, kept as zero-size marker `Id`s, no arena): the set's three lazy
  sub-objects — `CPropagationBindingReapplyConceptHash` and the two transition
  extensions (`CPropagationVariableBindingTransitionExtension` /
  `CPropagationRepresentativeTransitionExtension`). The set holds their ids; the lazy
  `get…(create)` getters and the reapply-hash insertion preserve control flow but defer
  the allocation. The `CPropagationBindingMapData` side of the reapply statement is
  ported for real.
- Additive; the compiling kernel is untouched. `cargo check --release` on ws exit 0
  (warnings only, none from the new file).

### W3.5r representative variable-binding-path-set subsystem (2026-06-30): WIRED + COMPILES, exit 0

Ported the *representative* binding subsystem that the `u17`/`u33` representative-binding
bodies defer over — distinct from the W2.7 varbind arenas and the W3c propagation-binding
subsystem. New file `process/representative.rs` ports nine classes faithfully (pointer→`Id`,
`CLinkerBase`→folded `data`/`next`, `CDependencyTracker`→`dep_track_point`, `CPROCESSMAP`→
by-value `HashMap`, `CLocalizationTag`→opaque `localization_tag`):
`CRepresentativeVariableBindingPathSetDataSignature`, `…SetData`, `…SetMigrateData`,
`CRepresentativeContainingMap{,Data}`, `CRepresentativePropagation{Set,Map,MapData,Descriptor}`.
The set-data's `CLinkerBase<cint64,Self>` carries the representative ID *as* its `data`
(`getRepresentativeID() == getData()`); the descriptor's `CLinkerBase<…SetData*,Self>` carries
the set-data id. `CRepresentativeVariableBindingPathMap{,Data}` are NOT re-ported — they already
landed in `varbind` (W2.7); the migrate-data holds that map by value.

- 4 new arenas + `arena_accessors!` trios on `ProcessContext` (`rep_var_bind_path_set_datas`,
  `rep_var_bind_path_set_migrate_datas`, `rep_prop_descs`, `rep_prop_sets`); the three
  `CPROCESSMAP`s + the signature are held by value (no arena). Imports + `Arena::new()` inits
  wired into `context.rs`; `pub mod representative;` into `mod.rs`.
- **Opaque marker re-aliased**: `varbind::RepresentativeVariableBindingPathMapData
  ::resolve_rep_var_bind_path_set_data` was the W2.7-DEFER opaque `Cint64` stand-in for
  `CRepresentativeVariableBindingPathSetData*`; it now points at the real
  `RepresentativeVariableBindingPathSetDataId` (ctors/getters/setters retyped; the cached
  `…_id` cint64 stays W3.5r-DEFER since reading `getRepresentativeID()` needs `ctx`). No live
  callers existed (all u17/u33 references are PORT-PENDING comment outlines).
- The COW localise (`getMigrateData`), `take/copyMigrateDataFrom`, the linker `append`s, and
  the signature-folding `addIncomingRepresentativePropagation` are ported as associated functions
  over `ctx: &mut ProcessContext` + `Id`s (the W3.5 accessor convention; same lift-init-restore
  idiom as `binding_hash`). The signature is `Copy` so `getKeySignature()` is taken by value.
- W3.5r-DEFER (own unit, marker `Id`, no arena): the set-data's
  `CRepresentativeVariableBindingPathSetJoiningHash` (lazy `getJoiningHash`/`hasJoiningData`).
- **Un-defer enables**: the u17 (`getRepresentativeJoiningKeyData`) and u33
  (`createCommonJoiningAll`, `updateRepresentativePropagationSet`,
  `requiresRepresentativePropagation`, `propagateRepresentativePropagationSet`,
  `areRepresentativesJoinable`) PORT-PENDING bodies can now allocate real
  `RepresentativeVariableBindingPathSetData`/`…MigrateData`/`RepresentativePropagation{Set,Descriptor}`
  via the new arenas, read `getRepresentativeID()`/`getRepresentatedVariableCount()`/
  `getMigrateData()`, and store reps into the resolve maps + containing map.
- Additive; the only errors in the shared working tree are the *parallel* `blocking_hash`
  (W3.5b) agent's in-flight `databox.rs`/`db4.rs` stale `stubs` imports (unrelated to this work).
  Verified in an isolated ws copy that re-exported those two relocated stubs from `stubs`:
  `cargo check --release` **exit 0** (`Finished release`), no diagnostics from `representative.rs`
  or my `context`/`varbind`/`mod` edits.

### W3c dependency factory + clash propagation (2026-06-30): WIRED + COMPILES, exit 0

Two new `completion/` files supply the keystone mechanisms the W3 wrappers deferred:

- **`dependency_factory.rs` — the `create*Dependency` allocator
  (`Algorithm/CDependencyFactory.{h,cpp}`).** Every `createXDependency` has one
  body: bump-allocate `CXDependencyNode` from the per-test process pool, run its
  `initX…`, read back `getContinueDependencyTrackPoint()`. The wrappers (u28/u29/u30)
  already port the `mConfBuildDependencies` guard + `Id::NONE` return and `W6-DEFER`
  the allocation. This file supplies it as an `impl ProcessContext`
  (KONCLUDE-PORT-NOTE[ownership]: the C++ factory allocates from the
  `CProcessContext` pool, which the port realises as the `Arena<T>` fields ON
  `ProcessContext`, so the faithful home is there; `new CX(…)` ≡
  `self.alloc_dep_node(DependencyNode::Variant{…})`). **7 allocators, one per the 7
  structural `DependencyNode` variants** (the manifest collapse), each co-allocating
  the inline members the C++ node holds by value: `alloc_independent_base_…`,
  `alloc_deterministic_…(kind)`, `alloc_det_link_…(kind)` (+1 `DependencyLink`),
  `alloc_functional_…` (DetLink2, +2 `DependencyLink`),
  `alloc_non_deterministic_…(kind)` / `alloc_or_…` / `alloc_reuse_backend_modes_…`
  (each +1 clash `DependencyTrackPoint`, back-linked to the node so
  `setup_non_deterministic`'s deref resolves). Plus
  `materialize_continue_dependency_track_point(dep)` = the
  `getContinueDependencyTrackPoint` read-back (det node → a track point bound to the
  node, the C++ multiple-inheritance `this`, which dep1.rs had left as a
  `W2-DEFER[api]`; non-det → `nd.clash_track_point`). The un-defer wave switches each
  wrapper's `W6-DEFER` line to `ctx.alloc_<variant>_dependency_node(...)` + the
  existing dep1 `init_*` + `materialize_continue_…`.
- **`clash.rs` — clash/stop propagation
  (`CCalculation{Clash,Stop}ProcessingException.{h,cpp}`).** KONCLUDE-PORT-NOTE[exceptions]:
  Konclude throws these deep in the rules and catches once in `handleTask`. Of the
  two faithful encodings — (A) thread `Result<…, signal>` through every rule, (B) a
  pending signal on the per-task context — **(B) is chosen**: the per-task
  `CalculationAlgorithmContext` (already threaded as `&mut` through every rule) is
  exactly the object the C++ raise→catch spans, so the unwind becomes a cooperative
  early-return through the same frames; and it is least invasive — the ~450
  already-compiling rule signatures are unchanged (no `Result` churn). A `CalcSignal
  { Continue, Clash(ClashDescId), Stop{task_completed} }` field `pending_signal` is
  added to the context (init `Continue`), with `raise_clash` / `raise_stop` (the two
  `throw`s), `has_pending_signal` (the per-frame unwind check), `take_pending_signal`
  (the `handleTask` catch), and Base forwarders. The un-defer wave turns each
  `// W3-DEFER[exceptions]: throw …; return` into `self.…raise_clash(c); return …;`
  and drains `take_pending_signal()` into u01's existing `HandleTaskException` match
  (u01's private closure/enum is left untouched — its `into_…` adapter lands with
  that wave).

Error trajectory: 0 errors throughout (purely additive). The only edit to a
compiling file was adding the `pending_signal` field + initialiser to
`completion/context.rs`. `cargo check --release` on ws exit 0 (warnings only, none
from either new file). Rule call sites NOT rewritten — that is the un-defer wave.

### W7 IndividualProcessNode RECONCILE-NEED reconcile (2026-06-30): COMPILES, 0→0 errors

Audited every `RECONCILE-NEED` flag the completion/saturation fill left that names
an `IndividualProcessNode` (process-layer) method. **40 `RECONCILE-NEED` flags
total across `completion/` + `saturation/`; the node-method subset is the 6 flags
in `completion/u15.rs` (×5) + `completion/u09.rs` (×1).**

Finding: nearly all the named node accessors were ALREADY ported by earlier waves
under Rust naming (the port drops the C++ `get_` prefix), so the flags were stale.
Verified-and-annotated (`(PORTED: <where>)` appended in place, call sites NOT
rewritten — that is the un-defer wave):
- `add_processing_restriction_flags` → `pn4.rs` (exists).
- `get_successor_nominal_connection_set` → `pn6.rs` `successor_nominal_connection_set`;
  `get_nominal_individual` → `sat1.rs` (exist).
- 7 assertion-linker getters (`get_assertion_role_linker` …
  `get_asserted_data_literal_linker`) → `pn2.rs` (exist, no-`get_` names).
- `get_ancestor_link` / `get_role_successor_to_individual_link` / `set_ancestor_link`
  / `has_individual_ancestor` → `pn3.rs`; `get_individual_ancestor_depth` →
  `node.rs` `individual_ancestor_depth` (exist).
- `PRF_SATISFIABLECACHED` / `PRF_COMPLETIONGRAPHCACHED` consts +
  `has_partial_processing_restriction_flags` → `node.rs` (exist).

Genuinely-missing method surface PORTED this wave (1 real code change, `pn3.rs`):
the phase-5 link-relocation iterators were zero-size placeholder structs with **no
`has_next`/`next`** (the flag's actual complaint). Added the faithful **empty-iterator**
`has_next`/`next` surface to `SuccessorRoleIterator`, `DisjointSuccessorRoleIterator`,
`RoleSuccessorIterator`, `RoleSuccessorLinkIterator`, and `SuccessorIterator`
(`next_link`/`next_individual_id`), each returning the C++ default-constructed
iterator result (`hasNext == false`, `next == nullptr/0`). This is the `else`-branch
empty iterator the getters yield while `mUseSuccRoleHash` / `mUseDisjointSuccRoleHash`
are absent, so the relocation loops now COMPILE + run zero iterations.

LEFT (still-missing subsystem, noted in the flags): the `SuccessorRoleHash` /
`DisjointSuccessorRoleHash` process-hash backends (W2-DEFER) so the iterators yield
real links; the phase-5 `depTrackPointHash` dedup; the sat-exp cache that *sets*
the PRF flags; the nominal-connection-set backend. `get_predecessor_link` (a task
example) does NOT exist in Konclude's `CIndividualProcessNode` — no such method.
The non-node `RECONCILE-NEED` flags (representative map in `u33`, dependency-factory
in `u12`, propagation bindings in `u06`/`u07`, saturation status masks in `s08`) are
separate unported subsystems, out of this wave's scope.

`cargo check --release` on ws exit 0 (warnings only, none from `pn3.rs`). Additive;
the compiling kernel is intact.

### W6 task/calc reconcile (2026-06-30): WIRED + COMPILES, 7→0 errors — KERNEL COMPLETE

The `task/` (8 files) and `calculation/` (5 files + mod) subtrees, struct-defs +
method bodies filled in parallel, were wired and reconciled to compile:

- **Wiring:** created `task/mod.rs` (declares all 8 task files: scheduler, config,
  satisfiable_task, task_data, adapters, status_propagator, callback_executer,
  stats). `calculation/mod.rs` already existed (declares builder/environment/
  env_factory/factory/manager + the `TaskHandleAlgorithmBuilderId` alias). Added
  `pub mod task; pub mod calculation;` to `konclude_ht/mod.rs`.
- **Error trajectory: 7 → 0.** All 7 errors were the SAME class: `INVALID` used
  but not imported in `task/scheduler.rs` (the `Task::clear`/`init` resets assign
  `INVALID` to its `Cint64` fields task_result/task_context/completion_negator/
  callback_linker/task_owner). Fix: add `INVALID` to the existing
  `use super::super::model::substrate::{Cint64, Id, NegLink}` import. All target
  fields are `Cint64`, so the assignment type-checks.
- **builder→algorithm linkage:** `calculation/builder.rs` constructs
  `SaturationTaskHandleAlgorithm::new()` and `CompletionTaskHandleAlgorithm::new()`
  — both are no-arg ctors in the real algorithm files, so the cross-subtree paths
  resolved with NO edits. The `CCalculationChooseTaskHandleAlgorithm` wrapper stays
  a `// W6-DEFER[api]` opaque `Cint64` (INVALID) return, as authored.
- **Stubs: 0.** No `task/pending.rs` or `calculation/pending.rs` needed — no
  unresolved siblings, no duplicate/dedup, no Default/borrow fixes. The parallel
  authors stayed self-consistent (adapters' 18 zero-size markers, the SatTaskId/
  TaskId/TaskDataId Id-aliases, and the config extension all matched their callers).
- `cargo check --release` exit 0 (warnings only). **MILESTONE: the entire
  konclude_ht kernel — model + process + completion + saturation + cache + task +
  calculation — now compiles clean.** Deferred bodies remain as W6-DEFER stubs.

### W6.5 cache-arena keystone (2026-06-30): WIRED + COMPILES, exit 0

The cache analogue of the W3.5 `ProcessContext` keystone. The cache subtree was
ported as struct skeletons + facade methods, but the family bodies defer
id-resolution (`W6-DEFER[api]`) because there is no arena root holding the cache
record families. `cache/context.rs` closes that gap.

- **No single `CCacheContext` in Konclude.** Unlike `CProcessContext` (one per-test
  pool), Konclude's cache pools are split across ~11 per-family context objects
  (`CComputedConsequencesCacheContext`, `COccurrenceStatisticsCacheContext`,
  `CReuseCompletionGraphCacheContext`,
  `CSaturationNodeAssociatedExpansionCacheContext`,
  `CSignatureSatisfiableExpanderCacheContext`,
  `CBackendRepresentativeMemoryCache{Base,Ontology,IndividualAssociation}Context`,
  `CCacheTaggingPool`, …), each holding its own `CObjectAllocator<T>` pools.
  KONCLUDE-PORT-NOTE[memory-pool]: `CacheContext` COLLAPSES all of them into one
  typed-arena container, the same collapse `ProcessContext` did for the per-test
  pool. The collapse is faithful: cache records are addressed by `CXxx*` = `Id<T>`
  either way; only the pool boundary moves.
- **64 record families → 64 `Arena<T>` fields**, one per `Id<T>` alias the cache
  files declare: value 3, unsat 6, reuse 4, satnode 7, consequences 6, sigexpand 7,
  occstats 2, events 2 (`CachingValueList`/`CachingDepHash` — the events placeholder
  duplicates of value/consequences write-data are NOT arena'd), backend 8,
  backend_data 19. Each gets a `get/get_mut/alloc_<stem>` trio via a local
  `cache_arena_accessors!` macro (mirrors `process::context`'s `arena_accessors!`,
  adapted to key off `Id<$ty>` directly because the cache files' `…Id` aliases
  collide by short name across modules — `ReaderId`/`WriterId`/`CacheEntryWriteDataId`/…).
- **Threading:** `CacheContext` is a STANDALONE root (not a `ProcessContext` field —
  cache records outlive a single satisfiability test; in Konclude the caches are
  long-lived singletons held by the cache manager). Cache facade methods that
  resolve/allocate records take `&CacheContext` / `&mut CacheContext`. This is safe
  and additive: the cache subtree has NO callers outside `cache/` yet, so widening
  facade signatures within `cache/` breaks nothing in the rest of the kernel.
- **Un-defered (3 bodies, the pure-id-resolution subset):**
  `value::CacheValueHasher::{get_hash_value, eq_hasher}` (resolve `self.cache_value`
  against `cache_values` → `q_hash` / by-value `CacheValue` compare; the C++
  `qHash(*mCacheValue)` / `operator==`), and
  `satnode::AssociatedConceptExpansion::get_dependent_nominal_set` (the lazy
  `allocateAndConstructAndParameterize<…> + initDependentNominalSet()` bump-alloc
  into `dependent_nominal_sets`). Each gained a `ctx` param + faithful body.
- **Left deferred (the honest finding):** the VAST majority of cache `W6-DEFER`
  sites have a SECOND blocker beyond id-resolution — threading (`postEvent` /
  `processCustomsEvents` write-event drains), backend-IO, cross-subtree
  `CConcept*`/`CIndividualProcessData*` (Ontology) bindings, or an
  un-modelled-API piece (e.g. `add_concept_expansion_linker` needs the linker's
  `getCount()`, not yet modelled; `get_computed_types_cache_entry_for_node`'s alloc
  is gated behind a cross-subtree `indProData` that is always `INVALID` here). The
  keystone unblocks them STRUCTURALLY (an arena now exists), but each still needs
  its other piece — so they stay as authored.
- **What remains for a cache un-defer wave:** (1) unify the per-family opaque
  `CCacheValue → Cint64` aliases onto `value::CacheValue` and re-key the linkers
  (`SaturationNodeAssociatedConceptLinker.cache_value` is `Cint64`, not
  `CacheValueId`) so cache-value-keyed hashing resolves; (2) model the missing
  linker/counting-base APIs (`getCount()` on the concept-expansion linker); (3)
  port the F8 cache-event family + a single-thread write-event drain so the
  `installWriteCacheData`/`processCustomsEvents` bodies un-defer; (4) thread the
  Ontology `CConcept*`/`CIndividualProcessData*` accessors for the entry-for-node
  bindings; (5) sweep every facade method that resolves an entry/reader/writer id
  onto `ctx.<stem>(id)` once its other blocker is cleared. `cargo check --release`
  on ws exit 0 (warnings only, none from `context.rs`).

### W6 cache-methods reconcile (2026-06-30): WIRED + COMPILES, 0→0 errors

The 9 cache families had method bodies filled, and the F1 backend facade's methods
landed in 4 new unwired files (`cache/backend_facade1.rs` cpp 34–1619,
`backend_facade_gap.rs` cpp 1620–2762 = the single giant `installAssociationUpdate`,
`backend_facade2.rs` cpp 2763–3957, `backend_facade3.rs` cpp 3958–5343), each an
`impl super::backend::BackendRepresentativeMemoryCache`. Reconcile to compile:

- **Wiring:** added `pub mod backend_facade{1,_gap,2,3};` + `pub mod pending;` to
  `cache/mod.rs`; created `cache/pending.rs` (header only).
- **Error trajectory: 0 → 0.** Wiring the 4 facade files + `pending.rs` was the
  whole job — no duplicate methods, no unresolved siblings, no name/overload
  realignments, no borrow fixes. `cargo check --release` exit 0 (only benign
  warnings; one `mut` in `backend_facade1.rs:593`). konclude_ht/cache rebuilt
  clean under `touch src/konclude_ht/cache/*.rs`.
- **CCacheValue TYPE SPLIT — already resolved by the authors, no edits needed.**
  Every file whose methods CALL CacheValue's API (`.get_tag`/`.is_cached_concept`/
  value-keyed hashing) already `use super::value::{CacheValue, …}` — `unsat.rs`
  (`type CCacheValue = value::CacheValue`), `satnode.rs`, `backend_facade1.rs`,
  `backend_data.rs`, `backend_facade3.rs`. The files keeping `pub type CCacheValue
  = Cint64` (`sigexpand.rs`) or `pub type CacheValue = Cint64` (`reuse.rs`) only
  store/pass the value opaquely, so the opaque alias compiles. Each file is
  internally consistent and the facade (which drives cross-family calls) is on
  `value::CacheValue`. No `= Cint64`→`value::CacheValue` switch was required.
- **pending.rs:** ZERO W6-RECONCILE-STUB siblings needed (wired, header-only) —
  the cache-arena fill wave starts from an empty pending file.
- Completion / saturation / process / model untouched and still compile.

### W2.7 satellite reconcile (2026-06-30): WIRED + COMPILES, 1→0 errors

Three `process/` satellite units, ported in parallel, were wired into the
arena-owning `ProcessContext` and the W2 stub-id reconcile applied:

- **Files wired** (`process/mod.rs`): `pub mod varbind;` (variable-binding-path
  subsystem), `pub mod distinct;` (distinct / connection-successor / disjoint-role),
  `pub mod reapply_sat;` (reapply label-set iterator / signature-blocking-candidate
  / incremental-expansion).
- **Arenas added to `process/context.rs`: 15** — 7 varbind (`var_bindings`,
  `var_binding_descs`, `var_binding_paths`, `var_binding_path_descs`,
  `var_binding_path_sets`, `var_binding_path_join_datas`,
  `var_binding_trigger_linkers`), 4 distinct (`distinct_hashes`, `conn_succ_sets`,
  `conn_succ_corr_hashes`, `disjoint_succ_role_hashes`), 4 reapply_sat
  (`sig_block_cand_hashes`, `blocking_test_datas`, `blocking_alt_datas`,
  `inc_exp_datas`). Each got its `arena_accessors!` trio (exact names from the
  files' `// W2.7-ARENA-ADDITIONS` blocks) + `Arena::new()` in `new()` + imports.
- **Stub-id re-aliases (5), done in `process/stubs.rs`** (where the ids are declared
  and re-exported from): the marker entries `ConnectionSuccessorSet=>ConnSuccSetId`,
  `DistinctHash=>DistinctHashId`, `DisjointSuccessorRoleHash=>DisjointSuccRoleHashId`,
  `IndividualNodeBlockData=>IndiBlockDataId`,
  `IndividualNodeIncrementalExpansionData=>IncExpDataId` were removed from the
  `stub_id!` block and re-declared as `pub type … = <real satellite id>`
  (`distinct::ConnectionSuccessorSetId`, `distinct::DistinctHashId`,
  `distinct::DisjointSuccessorRoleHashId`,
  `reapply_sat::BlockingTestDataId`, `reapply_sat::IncrementalExpansionDataId`).
  The alias NAMES are unchanged, so `node.rs`'s `conn_succ_set` / `distinct_hash`
  / `disjoint_succ_role_hash` / `indi_block` / `use_inc_exp_data` / `loc_inc_exp_data`
  fields (and every `use super::stubs::{…}` site) keep resolving — only the
  pointed-at type changed (stub → real). **No `node.rs` edit was needed** (the
  re-alias handled the retype).
- **Keep-both:** `stubs::SignatureBlockingCandidateHash` (the inline marker) is
  RETAINED because `databox.rs` / `db4.rs` hold it as `Id<stubs::…>`; the real
  `reapply_sat::SignatureBlockingCandidateHash` arena is added separately (distinct
  module path, no name clash). Un-wiring databox onto the real type is a later pass.
- **Error trajectory: 1 → 0.** The lone error: `reapply_sat::LabelSetMapEntry`
  derives `Clone` but holds `satellites::CondensedReapplyQueue` by value, which
  lacked `Clone`; fixed by adding `Clone` to that placeholder's derive. No other
  reconcile edits (no dedups, no import fixes, no deferral churn).
- W2.7-DEFER stubs (the LS-1/u11/u33 getter bodies etc.) were left untouched —
  not un-deferred. `cargo check --release` on ws exit 0 (warnings only).
- Completion / saturation / cache / task / calculation / model untouched and still
  compile.

### W3b node lazy-getter keystone (2026-06-30): WIRED + COMPILES, 4→0 errors

The prerequisite that unblocks un-defering the completion bodies that touch
node-owned satellites. Konclude's `CIndividualProcessNode` lazy getters allocate a
satellite from the task pool on first access (`if (!mX) { mX = new CX(mProcessContext);
mX->initX(mPrevX); mUseX = mX; }`). In the arena port these cannot live as `&mut self`
node methods — the allocation needs the `ProcessContext` arena — so they are lifted
onto `ProcessContext` as `NodeId`-threaded methods.

- **2 container hashes ported (`process/binding_hash.rs`, new file):**
  `ConceptVariableBindingPathSetHash` (concept-tag→`CVariableBindingPathSet`, value
  type already ported in `varbind` → `getVariableBindingPathSet` is faithful
  end-to-end) and `ConceptPropagationBindingSetHash` (concept-tag→`CPropagationBindingSet`,
  which is NOT yet ported → its localise-alloc is a `W3b-DEFER[api]`, control flow
  preserved). Each is a real `CPROCESSHASH`-modelled struct (owned `HashMap` + `init…`
  COW-clone/clear + last-descriptor get/set) with a `…HashData` value (loc/use pair).
  `CPropagationBindingSet`/`CPropagationBindingDescriptor` kept as local `Id<T>`
  placeholder markers (no arena yet).
- **Condensed-reapply-queue iterator ported (`process/reapply_sat.rs`):**
  `CCondensedReapplyConceptDescriptor` (the `CLinkerBase` reapply-descriptor it walks)
  as a real arena struct + `CondensedReapplyQueueIterator` (all 3 ctors — empty /
  pos-neg / only-positive — `next`/`hasNext`, the polarity-skip while-loop factored
  into `skip_filtered`, threading `&ProcessContext`). Distinct, real port from the W2
  by-value placeholders in `process::pn3`/`process::ls1` (left untouched — completion
  units still reference them; the un-defer wave reconciles those call sites onto this).
- **3 arenas + `arena_accessors!` trios added to `ProcessContext`:**
  `con_var_bind_path_set_hashes`, `con_prop_binding_set_hashes`, `cond_reapply_con_descs`.
- **6 context-threaded lazy-getters added (`process/context.rs`):**
  `node_connection_successor_set`, `node_reapply_concept_label_set`,
  `node_distinct_hash`, `node_disjoint_successor_role_hash`,
  `node_concept_variable_binding_path_set_hash`,
  `node_concept_propagation_binding_set_hash`. Each is faithful to the C++ create
  path (alloc-if-absent + `init…(prev)` + set `mX`/`mUseX`); the same-arena
  `init…(prev)` borrow is resolved with `mem::replace` (lift parent out, init, restore).
  The old `&mut self` pn3/pn6 stub getters are KEPT and marked `// superseded by
  ctx.node_*` (signatures unchanged) — the un-defer wave calls the ctx methods.
- **Node field retypes:** the two stub markers `ConceptPropagationBindingSetHash` /
  `ConceptVariableBindingPathSetHash` were removed from `process/stubs.rs`'s `stub_id!`
  block and `ConceptPropBindingSetHashId` / `ConceptVarBindPathSetHashId` re-aliased to
  the real `binding_hash` ids (the W2.7 "stub relocates to its own module" reconcile).
  No `node.rs` edit needed — the alias names are unchanged, so the node fields + every
  `use super::stubs::{…}` site (incl. `u32.rs`) keep resolving onto the real structs.
- **Error trajectory: 4 → 0.** All 4 were the same class: `#[derive(Default)]` on the
  two `…HashData` structs, which hold `Id<T>` fields — `Id<T>` has no `Default` derive
  by design (`substrate.rs`). Fixed by dropping `Default` from the derive and adding a
  manual `impl Default { Self::new() }` (the `descriptor.rs` / `value.rs` pattern).
  `cargo check --release` on ws exit 0 (warnings only; additive). Completion /
  saturation / cache / task / calculation untouched and still compile.
- **What the un-defer wave still needs:** (1) `CPropagationBindingSet` +
  `CPropagationBindingDescriptor` port + arena, to un-defer
  `ConceptPropagationBindingSetHash::get_propagation_binding_set`'s alloc branch;
  (2) the completion call sites (`u06`/`u07`/`u10`/`u11`/`u33`/`u34`/`u36` etc.) to
  switch their `getConceptPropagationBindingSetHash` / `getConceptVariableBindingPathSetHash`
  / `getReapplyConceptLabelSet` / `getDistinctHash` / `getConnectionSuccessorSet` /
  `getDisjointSuccessorRoleHash` `W3-DEFER[api]` stubs onto `ctx.node_*`, and the
  `CondensedReapplyQueueIterator` placeholders (pn3/ls1) onto the real
  `reapply_sat::CondensedReapplyQueueIterator`; (3) a `getConceptReapplyIterator`
  builder on the label set to seed the iterator's descriptor chain.

### W3b.1 label-set iterator + concept-tag accessor un-defer (2026-06-30): WIRED + COMPILES, exit 0

Two small process-layer gaps that blocked the blocking / label-set-iteration
un-defers (u16/u18/u19/u30/u34/u35) are now closed. Additive; `cargo check
--release` on ws exit 0 (warnings only, none from the edited files).

- **`descriptor.rs` — `ConceptDescriptor::get_concept_tag(&self, onto: &OntologyArenas)
  -> Cint64`.** Port of `CConceptDescriptor::getConceptTag` (`return
  getData()->getConceptTag()`): resolve the wrapped `ConceptId` against the static
  concept terminology (`onto.concept(id).get_concept_tag()`). This un-defers the
  `getConceptTag` member of the descriptor W2 method-batch (the `get_data_tag`
  linker branch W2.7 left as `INVALID`).
- **`reapply_sat.rs` — `ReapplyConceptLabelSetIterator::get_data_tag`** now takes
  `(&ProcessContext, &OntologyArenas)` and its linker branch calls
  `ctx.con_desc(it).get_concept_tag(onto)` (was W2.7-DEFER `INVALID`). The
  merged-map branches were already exact (read the map key).
- **`ls1.rs` — `getConceptLabelSetIterator` now builds the REAL
  `reapply_sat::ReapplyConceptLabelSetIterator`** (the local zero-size placeholder
  for it is deleted; the real one is imported). The C++ branch structure is
  faithful: sorted/deps/structure → merge the main + additional reapply maps
  (linker = `NONE`, skipEmpty = `!getAllStructure`); else → walk the
  `mConceptDesLinker` chain (both maps empty, skipEmpty = `true`, the C++ ctor
  default). New helper `snapshot_sorted_entries` snapshots a `HashMap` reapply map
  into the key-SORTED `Vec<LabelSetMapEntry>` the iterator's merge logic requires
  (the W2.7-DEFER the reapply_sat author flagged). The `Shared` additional-map
  alias stays `W2-DEFER[api]` (empty) — it needs the label-set arena to follow.
- **`ls1.rs` — `getConceptReapplyIterator{,_des}`** now thread `&ProcessContext`
  and return the REAL `reapply_sat::CondensedReapplyQueueIterator` via the new
  `build_reapply_iterator` builder (seeds the descriptor-chain head). The
  `CCondensedReapplyQueue` placeholder still has no head, so every branch seeds
  `Id::NONE` (empty real iterator) `W2-DEFER[api]` until the queue ports its
  dynamic descriptor linker; the iterator TYPE is real so callers can walk it. The
  local `ls1::CondensedReapplyQueueIterator` placeholder is RETAINED (the
  `insertConcept*` out-iterator params + `completion/u36.rs` still reference it).
- **Error trajectory: 0 → 0.** Purely additive; no caller of the four getters
  exists yet (the completion units hold them as W6-DEFER comments), so the two
  signature extensions (`get_data_tag` + ctx on the reapply getters) broke
  nothing. `cargo check --release` on ws exit 0.
- **What un-defer can now call:** the `getConceptLabelSetIterator(true,false,false)`
  / `(false,false,false)` walks in u16/u18/u19/u30/u34/u35 (currently W6-DEFER
  comment stubs) resolve onto `label_set.get_concept_label_set_iterator(…)` +
  `it.get_data_tag(ctx, onto)` / `it.move_next(ctx)`; the reapply-queue walks onto
  `label_set.get_concept_reapply_iterator(ctx, …)`.

### W6 cache-skeleton status (struct skeleton)

The 9 cache families were authored in parallel as self-contained struct-definition
files (per-file local `Id` aliases; cross-family refs held opaque as
`CCacheValue → Cint64` etc., still un-unified by design). Reconcile to compile:

- Created `cache/mod.rs` declaring all 11 files; added `pub mod cache;` to
  `konclude_ht/mod.rs`.
- Error trajectory: 1 → 0. The single error was a derive failure:
  `CacheValueHasher` in `value.rs` derived `Default` while holding a bare
  `Id<CacheValue>` field (`Id<T>` has no `Default` derive, by design — see
  `substrate.rs`). Fixed by dropping `Default` from the derive and adding a manual
  `impl Default` using `CacheValueId::NONE` (the same pattern the process layer
  uses, e.g. `process/descriptor.rs`).
- No dedups, no import-path fixes, no stubs needed — the parallel authors kept
  each file self-contained, so cross-module same-named placeholder types
  (`CCacheValue = Cint64`, etc.) coexist fine at distinct paths. Method bodies
  remain deferred behind the `// W6-CACHE method-batch` markers; the per-family
  opaque value aliases are intentionally NOT yet unified onto `value::CacheValue`
  (that is a method-batch-era decision).
- Completion / saturation / process / model untouched and still compile.

### W3.6 node-resolution keystone (2026-06-30): WIRED + COMPILES, exit 0

The `getUpToDateIndividual` / `getLocalizedIndividual` / `getSuccessorIndividual` /
`getAncestorIndividual` / `getAvailableUpToDateIndividual` resolver family — the
protocol dozens of deferred completion bodies route every (possibly relocalised /
merged) node through to get the *current* node in *this* branch's localisation.

- **New file `process/node_resolution.rs`.** It ports the two small Process-layer
  types the resolvers stand on + lifts the resolvers onto the context:
  - **`CProcessTagger`** (real struct): the 7 monotone tag counters + `get_current_*`
    / `inc_*`. Supersedes the W3-DEFER opaque `Cint64` placeholder. Only the
    localization tag participates in resolution; the rest carry the branching /
    blocking / label-set-modification protocols.
  - **`CIndividualProcessNodeVector`** (real struct): the databox's `mIndiProcessVector`,
    a two-sided (signed-id, nominals are negative) `Vec<NodeId>` with
    `get_data` / `has_data` / `set_local_data` (+ `get_item_*` helpers). Merging /
    relocalisation update it, so `get_data(id)` already yields the merge-target /
    relocalised node ⇒ `getUpToDateIndividual` is one lookup, not a chain walk.
  - **5 resolvers + 2 edge helpers** as methods on `CalculationAlgorithmContextBase`
    (it owns BOTH the databox holding the vector AND the `ProcessContext` holding
    the node arena + tagger): `get_up_to_date_individual{,_by_id}`,
    `get_localized_individual{,_by_id}`, `get_successor_individual`,
    `get_localized_successor_individual`, `get_ancestor_individual`,
    `get_available_up_to_date_individual` (+ `is_nominal_individual_node_available`).
    Edge opposite resolution (`getOppositeIndividual{,ID}`) compares by INDIVIDUAL
    NODE ID (not arena identity), so a localised copy resolves correctly; it needs
    the node arena, hence ctx-level.
- **Databox/context/edge/pn1 wiring (additive):** databox `indi_process_vector`
  now holds the real vector BY VALUE (relocated out of `process::stubs`; getter →
  `&IndividualProcessNodeVector` + a new `_mut`); `ProcessContext::used_process_tagger`
  now holds the real `ProcessTagger` by value (+ `used_process_tagger{,_mut}`
  accessors); `is_localization_tag_up_to_date(cint64)` added to the node (pn1) and
  the link edge (`mProcessTag >= tag`).
- **DEFER notes:** the `getUpToDateIndividual(id)` MISS path (materialise a fresh
  temporary nominal node + load assertions/backend cache + queue) is
  algorithm-driven and stays `W3-DEFER[api]` (the vector-HIT path is what the
  successor/ancestor resolvers need); the `getLocalizedIndividual`
  completion-graph-cached re-flag branch is gated on the algorithm's
  `mConfCompletionGraphCaching` config (not reachable from the ctx receiver) and is
  inert when CG caching is off (the ORE default). `set_local_data` is a single
  store; the C++ local-overlay save/restore for backtracking is a separate unit
  ([unclear]).
- **Error trajectory: cargo check 0 → (3 unresolved imports) → (1 E0308) → 0.** The
  3 imports were other files (`saturation/{algorithm,s02}.rs`, `process/db1.rs`)
  pulling `IndividualProcessNodeVector` from `stubs`; repointed to
  `node_resolution`. The E0308 was `db1.rs`'s save/restore local (typed
  `Id<…>`) now capturing a by-value vector; retyped + `.clone()` (behaviour
  unchanged — it was already a capture-and-discard). 0 warnings on the new file.
- **What completion un-defer can now call:** the W3-DEFER stubs in `completion/u36.rs`
  (`get_localized_individual{,_by_id}` / `get_successor_individual` /
  `get_localized_successor_individual` / `get_ancestor_individual`, marked
  `// superseded by ctx.*`) and the `_indi_node_vec` placeholders in
  `u04`/`u16`/`u18`/`u32` resolve onto `calc_alg_context.get_up_to_date_individual(…)`
  etc. and `…individual_process_node_vector().get_data(i)`.
- `cargo check --release` on ws exit 0 (additive; only pre-existing benign warnings).

### W3.5b blocking-family satellites (2026-06-30): WIRED + COMPILES, 0→0 errors

The remaining blocking-family `Process/` satellites the signature / dynamic-blocking
un-defers (`completion/u18`/`u19`/`u20`/`u31`/`u35`) reach into. New file
`process/blocking_hash.rs` (the W2.7 `reapply_sat.rs` already ported the
`CSignatureBlockingCandidateHash` family + the concrete `CBlockingAlternative…Data`,
NOT duplicated here).

- **4 classes ported:** `CBlockingIndividualNodeCandidateData` (the
  `CConceptLabelSetModificationTag + CNodeSwitchTag` candidate data; ordered
  `CPROCESSMAP<cint64,node*>` → owned `BTreeMap<Cint64,NodeId>` keyed by `-id`),
  `CBlockingIndividualNodeCandidateIterator` (the `upperBound(-id)`-onward walker;
  full ordered snapshot + `begin/end/last` `usize` cursors; `next` / `hasNext` /
  `hasIndividualCandidate(s)` / `removeLast`), `CBlockingIndividualNodeCandidateHash`
  (`(ConceptId,bool)` → candidate-data; triple-buffer collapsed to one owned
  `HashMap` + eager COW `init…`, the copy-ctor `candidate=null,keep prev` reset
  preserved; `get_blocking_individual_candidate_data(create)` allocates the child
  data via the `binding_hash` `mem::replace` parent-init pattern), and
  `CSignatureBlockingIndividualNodeConceptExpansionData` (`SigBlockConExpData` — the
  per-node blocker + cached signature/counts + review/subset markers; full
  getter/setter + `initBlockingExpansionData`).
- **3 arenas + `arena_accessors!` trios on `ProcessContext`:**
  `blocking_indi_node_cand_hashes`, `blocking_indi_node_cand_datas`,
  `sig_block_con_exp_datas` (+ `Arena::new()` in `new()` + imports).
- **Stub reconciles:** `SigBlockConExpDataId` removed from `stubs.rs`'s `stub_id!`
  block and re-aliased to `blocking_hash::SignatureBlockingIndividualNodeConceptExpansionDataId`
  (name unchanged → `node.rs`'s `sig_block_con_exp_data` field + `pn4.rs` getters
  keep resolving, no `node.rs` edit). The `SignatureBlockingCandidateHash` and
  `BlockingIndividualNodeCandidateHash` markers removed from the `stub!` block.
- **Databox retype: DONE** (not deferred). `databox.rs` + `db4.rs` now import
  `SignatureBlockingCandidateHash` from `reapply_sat` and
  `BlockingIndividualNodeCandidateHash` from `blocking_hash` instead of `stubs`, so
  the `Id<…>` field/getter types point at the real structs. No cascade: these were
  the only two consumers of those stub markers and `Id<T>` is type-agnostic, so the
  retype is a pure import swap. (This is the "un-wiring databox onto the real type
  is a later pass" the W2.7 reconcile flagged for `SignatureBlockingCandidateHash`.)
- **What the un-defer wave can now call:** `u18`'s `rebuildSignatureBlockingCandidateHash`
  / `getSignatureBlockingCandidateHash` + the `SigBlockConExpData` review/subset
  reads, `u19`/`u20`/`u31`/`u35`'s blocking-candidate iteration
  (`get_blocking_individual_candidate_data` + `BlockingIndividualNodeCandidateIterator`),
  and the `pn4` `get/setSignatureBlockingIndividualNodeConceptExpansionData` node
  getters now resolve onto real arena structs (`ctx.alloc_sig_block_con_exp_data(…)`
  / `ctx.blocking_indi_node_cand_hash(…)`).
- **DEFER notes:** `BlockingIndividualNodeCandidateData` has no `#[derive(Clone)]`
  (its `modification_tag` base is not `Clone`; never whole-cloned). The iterator's
  `removeLastIndividualCandidate` mutates the snapshot and is faithful for reads,
  but propagating the erase back to the arena-owned `BTreeMap` needs `&mut ctx` the
  snapshot iterator does not hold (`W3.5b-DEFER[api]`, the un-defer wave threads it).
  The `CProcessTagger`-driven node-switch-tag protocol stays opaque (only the
  marking word modelled), matching `reapply_sat::IndividualNodeBlockingTestData`.
- **Error trajectory: cargo check exit 0 → 0** (only pre-existing benign warnings;
  no errors at any point — additive, parallel `W3.5r representative` work present
  and also compiling). Completion / saturation / cache / task / calculation
  untouched and still compile.

### W6-Task incremental-consistency adapter (2026-06-30): REAL + WIRED + COMPILES, exit 0

The first of the 18 `task::adapters` zero-size markers turned real and reached from
completion. Additive; `cargo check --release` on ws exit 0 (no warnings from the
edited files).

- **`task/adapters.rs` — `SatisfiableTaskIncrementalConsistencyTestingAdapter` now a
  real struct** (removed from the `adapter!` zero-size macro). Faithful port of
  `CSatisfiableTaskIncrementalConsistencyTestingAdapter.{h,cpp}`: 4 fields
  (`ontology`, `prev_cons_ontology` = the prev-completion-graph handle the retest
  diffs against, `cons_observer`, `incremental_revision_id`), the 4-arg ctor
  `new(testing_ontology, prev_cons_ontology, inc_rev_id, observer)`, and the 4
  getters. The two `CConcreteOntology*` + the `CConsistenceObserver*` stay opaque
  `Cint64` ([api]); only `incremental_revision_id` is concrete.
- **Task instance already carries it.** `task::satisfiable_task::SatisfiableCalculationTask`
  already had the `sat_inc_cons_testing_adapter: Id<Adapter>` field + the
  `get/set_satisfiable_task_incremental_consistency_testing_adapter` pair (W6) — no
  task context/arena invented (Konclude has none); the adapter is held on the task,
  resolved by id per convention §5.
- **Reachability from completion.** `completion/stubs.rs`'s `SatisfiableCalculationTask`
  marker re-exported onto the real task (the established stub→real re-alias), so the
  context's `sat_calc_task` / `used_sat_calc_task` `Id`s point at the real task.
  `completion/context.rs` gained two thin resolution arenas (`sat_calc_task_arena`,
  `inc_cons_testing_adapter_arena`) + accessors and the resolver
  `satisfiable_task_incremental_consistency_testing_adapter(sat_task) -> Id<Adapter>`
  (`= satCalcTask->getSatisfiableTaskIncrementalConsistencyTestingAdapter()`, guarded
  `Id::NONE`), plus a base forwarder. These are convention-§5 `CClass*→Arena`
  resolution, NOT a heavyweight task container; empty until the deferred
  `initCalculationAlgorithmContext` populates them.
- **Un-defered (faithful):** the u01 `handleTask` adapter presence test (cpp 1031,
  `if (satCalcTask->getSatisfiableTaskIncrementalConsistencyTestingAdapter())`) — the
  hardcoded `false` is now the live resolver call. **Left deferred:** the inner
  incremental-compatibility seeding loop (blocked by `getIncrementalCompatibilityCheckingQueue`
  / `getIndividualImmediatelyProcessingQueue` / `getLocalizedIndividual`, not the
  adapter); all of u26 (`requires_incremental_node_expansion` reads `inc_exp_data`,
  not the adapter; `incremental_node_expansion`'s terminal is blocked by
  `getUpToDateIndividual`; the `HandleTaskException` drain is unrelated). No other
  completion/saturation body's sole blocker was this adapter.
- **Error trajectory: 0 → 0** (purely additive). `cargo check --release` on ws exit 0.

### u15 merge/nominal process satellites (2026-06-30): WIRED + COMPILES, exit 0

The three still-missing `Process/` satellites that block the merge (u15 phases 5/6)
+ nominal expansion (u17 `getIndividualMergingHash`), in three new files:

- **`merging_hash.rs` — `CIndividualMergingHash{,Data}`.** The Qt-hash subclass
  `CPROCESSHASH<cint64, CIndividualMergingHashData>` → wrapper owning a
  `HashMap<cint64, IndividualMergingHashData>`; `CXLinker<cint64>* mMergedIndividualLinker`
  → head-front `Vec<cint64>`; `CIndividualMergingHashData : CDependencyTracker` folds
  the track-point base + holds a `CCondensedReapplyQueue` by value. `hasMergedIndividual`
  faithfully reproduces Qt `value(key)`'s default-on-absent (`false`).
- **`condensed_reapply.rs` — `CCondensedReapplyQueue`.** The dynamic reapply-queue:
  a `CondensedReapplyConceptDescriptorId` head into the existing `cond_reapply_con_descs`
  arena. `getIterator` constructs the ALREADY-PORTED `reapply_sat::CondensedReapplyQueueIterator`
  seeded from the head (clear-on-take); `addReapplyConceptDescriptor` is the head-front
  splice via the arena node's `next`. The W2 zero-size `satellites::CondensedReapplyQueue`
  placeholder is deleted and re-exported from here; 6 unit-construction sites
  (satellites + ls1) reconciled (`::new()` for fresh, value-share for the COW copy).
- **`succ_role_hash.rs` — `CSuccessorRoleHash` + `CSuccessorRoleIterator` + `CSuccessorIterator`.**
  The `QMultiHash<cint64, CIndividualLinkEdge*>` → `HashMap<cint64, Vec<EdgeId>>`; the
  shared `mPrevSuccessorLinkHash` COW partner → owned `Option<…>` clone with the full
  size-threshold COW (`<=100` share / `>100` keep-prev / `*10` combine) of
  `initSuccessorRoleHash` reproduced; the iterators snapshot the relevant buckets into
  owned `Vec`s (the `CSuccessorIterator` distinct-key dedup reproduced by one
  `(indi, first-link)` per bucket).

- **2 arenas + trios on `ProcessContext`** (`individual_merging_hashes`,
  `succ_role_hashes`). 2 stub ids re-aliased (`SuccRoleHashId` → `succ_role_hash::SuccessorRoleHashId`,
  `IndividualMergingHashId` → `merging_hash::IndividualMergingHashId`; names unchanged so
  node.rs/pn3/pn6 fields keep resolving onto the real arena structs).
- **Iterator wiring (low-risk path):** 5 `ctx.node_*` context-threaded methods added —
  `node_successor_role_hash` (lazy alloc), `node_successor_role_iterator`,
  `node_successor_iterator`, `node_has_successor_individual_node`,
  `node_disjoint_successor_role_iterator` (the last seeds the ALREADY-real
  `distinct::DisjointSuccessorRoleIterator` — `CDisjointSuccessorRoleHash` was already
  ported in W2.7). These resolve the node's `use_*` hash id and seed the REAL iterator;
  the existing pn3 `&self` getters stay empty-but-typed with `// superseded by ctx.node_*`
  notes (the W3b supersedes-stub pattern), so no call site breaks. The un-defer wave
  routes the phase-5 relocation loops through the `ctx.node_*` siblings.
- **Error trajectory: exit 0 throughout** (purely additive apart from the 6 mechanical
  `CondensedReapplyQueue` construction reconciles). `cargo check --release` on ws exit 0,
  0 konclude_ht errors. `DisjointSuccessorRoleHash` needed NO new port (already real in
  `distinct.rs`); the population path (`install_individual_link` insert + `getOppositeIndividualID`)
  stays W2-DEFER, so the iterators run zero rows until that un-defers — the plumbing is
  real and typed.

### W8 main driver loop — take-next + rule dispatch LIVE (2026-06-30): COMPILES, exit 0

The heartbeat that turns the (already-ported) `handleTask` skeleton into a runnable
satisfiability test. Three `todo!`s on the driver path were replaced with faithful,
live bodies; `cargo check --release` on ws exit 0, 0 konclude_ht errors.

- **u01 `handle_task`** — already a full faithful port (no `todo!`); LEFT AS-IS. Its
  outer `while take_next_process_individual(...)` drive, the per-frame `drain_pending!`
  clash/stop check (the `clash.rs` `take_pending_signal` → `HandleTaskException` catch),
  completion detection and the result epilogue are all present. It is GATED OFF for now
  only because `satCalcTask` acquisition (`dynamic_cast<CSatisfiableCalculationTask*>` +
  `getProcessContext`) is a `W3-DEFER[api]` task-adapter dependency, so the body short-
  circuits (`sat_calc_task == Id::NONE` → returns `false`) until the Task/Calculation
  controllers seed a real task. No `todo!` on the path.
- **u02 `take_next_process_individual`** — `todo!` REPLACED with the faithful probe
  cascade. Probe 1 (cache-testing nodes) and probe 24 (sorted nominal-non-deterministic
  nodes) are LIVE — both are backed by real `process/db4.rs` linkers
  (`mIndividualNodeCacheTestingLinker` / `mSortedNominalNonDeterministicProcessingNode
  Linker`). The other ~34 triple-buffered-queue probes are kept DEFERRED behind ONE
  consolidated `W3-DEFER[api]` block: the `CIndividual*ProcessingQueue` CONTENTS
  subsystem is unported (`process/db3.rs` getters return `Id::NONE`,
  `initProcessingQueue` is `W2-DEFER`, the queue stub types carry no `isEmpty`/`takeNext`),
  and several of those arms also call still-deferred merge/nominal/cache/backend helpers.
  The fixed 1-36 probe order stays recorded verbatim in the method doc-comment. On the
  trivial (non-merge/non-cache) path the function returns `Id::NONE` cleanly (no work
  queued), so the driver loop runs zero iterations and concludes — no `todo!`.
- **u03 `tableau_rule_processing` + `tableau_rule_choice`** — both `todo!`s REPLACED.
  `tableau_rule_processing` is a full faithful port (the three guard helpers
  `try_delay_nominal_processing` / `needs_individual_node_expansion_blocking_test` /
  `is_individual_node_{backend_cache_synchronization_processing,expansion}_blocked` were
  already LIVE in u16/u18/u20). `tableau_rule_choice` ports the member-fn-pointer jump
  table (`m{Pos,Neg}JumpFuncVec`, opaque per the struct wave) as an explicit `match` on
  the operator code mirroring the algorithm-ctor table 1:1 (cpp 238-345): ~60 positive +
  17 negative opcode arms dispatching into the LIVE `self.apply_*_rule` siblings
  (u05-u09), with the two config gates (`conf_specialized_automate_rules` →
  `apply_automat_and_rule`; `conf_representative_propagation_rules` → the
  `apply_representative_*` family). `mLastJumpFunc` is recorded as a fired/not-fired bit
  (`W3-DEFER[pointer-alias]`: no fn-pointer identity to store; no current reader needs it).
- **Reachable now:** the whole `apply_*_rule` engine is now wired from the driver — AND
  (`apply_and_rule`, fully live), BOTTOM (`apply_bottom_rule`), OR/ALL/SOME, automat AND/
  choose, NOT, SELF, ATLEAST/ATMOST, NOMINAL, VALUE, IMPLICATION, the datatype family,
  the bind/varbind/representative propagation families, and the `*IMPLI` variants.
- **What a trivial run still hits (deeper, off the driver path):** the `apply_*_rule`
  bodies retain their own `W*-DEFER` internals (u08 = 6, u09 = 1 `todo!`s on the
  ∃/atleast/atmost/nominal/value sub-paths needing saturation-node / backend-cache /
  successor subsystems); and the inner concept-drain loop in `handle_task` only fires
  once the concept-processing-queue subsystem lands (today `continue_individual_processing`
  returns `false` — the queue-contents `W3-DEFER` — so the rule dispatch is wired but not
  yet exercised). Seeding a real root node + a concept on its processing queue (the
  Task/Calculation seed + the queue-contents port) is the next unblock.
- **Error trajectory: exit 0** throughout (the only edits are u02/u03 bodies + 3 new u03
  imports `ConDescId` / `op` / `ConceptId` + `INVALID`). No unreachable-pattern warnings
  in the dispatch ⇒ all opcode groupings are value-distinct.

### W8.1 processing-queue subsystem — the inner drain made LIVE (2026-06-30): COMPILES, exit 0

The concept / individual **processing-queue** layer the W8 driver short-circuited
on (`take_next_process_individual`'s ~34 deferred probes, db3's `Id::NONE` queue
getters, `continue_individual_processing` returning `false`) is now REAL. New file
`process/queues.rs` ports the workhorse queue family faithfully:

- **4 real queues + 2 value helpers.** `CIndividualUnsortedProcessingQueue`
  (LIFO node linker), `CIndividualLinkerRotationProcessingQueue` (two-stage
  process/rotation), `CIndividualDepthProcessingQueue` (depth-priority +
  remaining-depth bucketing), `CConceptProcessingQueue` (the per-node 15-slot
  concept-descriptor priority vector that drives the rule loop); plus
  `CIndividualDepthPriority` (the `(depth,id)` `Ord` key) and
  `CConceptProcessingPriorityQueueData`. Each queue has the faithful
  `init_processing_queue`(COW)/`is_empty`/`take_next`/`insert`/`clear` ops in
  Konclude order (priority where applicable: depth queue = `BTreeMap` begin();
  concept queue = high-index-first with default-then-sorted chains).
- **Where held — arena on `ProcessContext`.** KONCLUDE-PORT-NOTE[ownership]:
  across a non-deterministic branch the child databox shares the parent queue via
  `mPrevX` (a pointer into the per-test pool), so the queue objects must live in
  the ONE shared pool, not per-databox. The port keeps that faithful: 4
  `Arena<T>` on `ProcessContext` (`indi_unsorted/rotation/depth_proc_queues`,
  `concept_proc_queues`) addressed by the `Id<T>` triples already on the databox.
  The queued ENTRIES are bare `Vec<NodeId>`/`BTreeMap` by value inside each queue
  (no linker arena); the concept queue's descriptor chains use the existing
  `con_proc_descs` arena. The COW `initProcessingQueue(prev)` is a deep `clone()`
  (behaviour-identical, sharing optimisation dropped — `[memory-pool]` note); the
  depth queue's `mAdditionalPriorityIndiDesMap` overlay is likewise collapsed.
- **db3 getters un-defered (22 of 26).** Each `getXxx(create)` now threads
  `ctx: &mut ProcessContext` and allocates via
  `ctx.alloc_{unsorted,rotation,depth}_proc_queue_from_prev(prev)` +
  `initProcessingQueue`. The 2 whose container is still a stub
  (`var_bind_concept_batch` = `CIndividualConceptBatchProcessingQueue`,
  `incremental_exansion` = `CIndividualCustomPriorityProcessingQueue`) keep the
  `W2-DEFER`. Callers reach them through new forwarders on
  `CalculationAlgorithmContextBase` (`db_queue_forward!`) that destructure `base`
  for the disjoint databox + process-context borrows (the W3.6 pattern); the 14
  external call sites in u04/u16/u18/u20/u26 were rewritten to the forwarders.
- **`continue_individual_processing` LIVE** (u02): reads the node's
  `getConceptProcessingQueue(false)` (lifted to
  `ProcessContext::node_concept_processing_queue`, the W3b lazy-getter pattern) +
  `isEmpty` + `getNextConceptProcessPriority` against the `min_concept_processing_priority_level`.
- **`take_next_process_individual` — 14 probes LIVE** (u02): immediately (2),
  role-assertion (4), depth-det-exp preprocessing (5), depth-first-det-exp (6),
  distinct-VS-sat (7) + VS-triggering (8) [+ `getLocalizedIndividual`],
  backend-sync-retest (9), backend-direct-influence (10), nominal (21),
  depth-normal (25), depth-first (27), blocking-update (29), blocked-react (30),
  delaying-nominal (35). The fixed 1-36 order is preserved; the probes needing
  still-separate subsystems (batch/custom queues, reactivation queue,
  `getUpToDateIndividual` MISS, signature/reusing review, backend
  neighbour/reuse, the INQT_OUTDATED descriptor queue) stay `W3-DEFER`.
- **u01 inner concept drain LIVE.** The `while continue_processing_individual`
  loop now takes the real `conProcDes =
  getConceptProcessingQueue(true)->takeNextConceptDescriptorProcess()` and feeds
  it to `tableau_rule_processing` → `tableau_rule_choice` → `apply_*_rule` (W8's
  live dispatch). The reinsert path passes the real queue id.
- **Insert side (u04): the individual-queue inserts un-defered** (real `NodeId`):
  `add_individual_to_processing_queue`'s depth-first / det-exp / blocked-react /
  depth inserts now call `insert_indiviudal_process_node` /
  `indi_depth_queue_insert`. The **concept-queue insert stays deferred** — its
  blocker is the `CConceptProcessDescriptor` allocation (the concept-priority
  strategy + concept reads), a genuinely-separate subsystem (rule 3), not the
  queue; the queue's `insert_concept_process_descriptor` method is real and
  waiting on a real descriptor. The node-flag dedup (`setProcessingQueued`) also
  stays deferred (separate restriction-flag subsystem).
- **What the driver can now drain.** `take_next_process_individual` returns real
  nodes off the populated individual queues; `continue_individual_processing`
  reads the real per-node concept queue; the inner loop pops real concept
  descriptors and dispatches into the live `apply_*_rule` engine. The end-to-end
  run still bottoms out only where the concept-descriptor allocation +
  satisfiable-task seed land (the `handle_task` `satCalcTask` acquisition is still
  `W3-DEFER`, so `handle_task` short-circuits until Task/Calculation seeds a
  task).
- **Error trajectory: 3 → 0 → 0.** The only build errors were two `Default`
  derives on structs holding `Id<T>` (`ConceptProcessingPriorityQueueData`, the
  array init) — fixed with manual `impl Default` (the `descriptor.rs`/`value.rs`
  pattern); `ConceptProcessDescriptor` gained `#[derive(Copy,Clone)]` so
  `initCopy` is `*dst = *src`. The depth queue's node-field reads while mutating
  the queue arena are resolved by disjoint `ProcessContext` wrappers
  (`indi_depth_queue_take_next`/`_insert`). `cargo check --release` on ws exit 0
  (51 benign warnings, dead-code in not-yet-called queue ops). Completion /
  saturation / cache / task / calculation / model untouched and still compile.

### W5 FIRST RUN — the port produces its first consistency verdicts (2026-06-30): 3/3 TESTS PASS on ws

The behavioural milestone: the kernel RUNS for the first time and returns trivial
consistency verdicts. `cargo test --release konclude_ht` on ws = **6 passed / 0
failed** (3 new `completion::selftest` + 3 pre-existing `model::op`); full lib
build exit 0.

- **Seed primitives un-defered (gap a + b):**
  - `completion/u36.rs` `add_concept_to_individual` now routes the node's concept
    queue + reapply label set through the W3b/W8.1 context-threaded lazy getters
    (`ctx.node_concept_processing_queue(node,true)` /
    `ctx.node_reapply_concept_label_set(node)`) instead of the superseded
    `&mut self` node getters that returned `Id::NONE` (they cannot run the arena
    allocation) — so the label set + concept queue actually materialise.
  - `process/queues.rs` `CConceptProcessingQueue::insert_concept_process_descriptor`
    / `take_next_concept_descriptor_process` (already real, W8.1) are exercised
    directly in `concept_queue_insert_primitive` over a freshly-allocated
    `CConceptProcessDescriptor` (gap a — the seed the future drive loop pops).
- **Clash detection + raise made live (the verdict):** `insert_concept_get_clash`'s
  W2-DEFER shims keyed the label-set map by the descriptor id (`con_des.raw`) and
  read negation as a constant `false`, so A vs ¬A never collided/compared. New
  `process/ls1.rs` `insert_concept_get_clash_resolved` takes the descriptor's REAL
  concept tag + negation (resolved by the caller, which holds the context) + a
  `desc_negated` resolver for the stored descriptor — the faithful C++
  `insertConceptGetClash` keying/polarity-compare. `u36`
  `insert_concepts_to_individual_concept_set` resolves the tag, lifts the label set
  out of the arena (`mem::replace`, the established pattern) so the
  `&ProcessContext` resolver is free of the `&mut` borrow, runs the clash insert,
  restores the label set, and on a detected clash allocates a `CClashedDependency
  Descriptor` and `raise_clash`es the pending signal (the `clash.rs` stand-in for
  `throw CCalculationClashProcessingException`).
- **Thin test entry (gap c + d):** `completion/selftest.rs` (`#[cfg(test)]`, wired
  in `completion/mod.rs`) bypasses the still-`W3-DEFER` Task/scheduler adapter and
  drives a constructed `CalculationAlgorithmContextBase` directly. It hand-builds a
  one-concept TBox, allocates a root `IndividualProcessNode` + registers it in the
  databox node vector (minimal `initializeCompletionGraph`/`buildCompletionGraph`),
  then `addConceptToIndividual`s the test concepts. Verdict = the per-task pending
  signal (handleTask's catch semantics): `sat_single_atomic_concept_is_consistent`
  (A → no signal = CONSISTENT/COMPLETE), `clash_a_and_not_a_is_inconsistent`
  (A + ¬A → pending `Clash` = INCONSISTENT), `concept_queue_insert_primitive`.
- **What remains for a FULL drive loop:** the saturation loop in `handleTask`
  (`take_next_process_individual` → `individual_node_initializing` →
  rule drain) is still gated by the `individualNodeInitializing` `todo!`
  (`completion/u03.rs:175`) + the `satCalcTask` task-adapter seed (`u01`
  short-circuits on `sat_calc_task == Id::NONE`). The W5 verdict is the
  clash-at-initialization path, which does not need either; the next wave un-defers
  `individual_node_initializing` (or seeds a real `satCalcTask`) to run the rule
  engine over the concept queue.

## Build / validate

Never build on the laptop. Sync to `ws` and `cargo build --release` there.
Validate behaviour against Konclude itself on small/validated fragments (the
exact-port goal means a per-ontology classification diff vs Konclude is the
acceptance test), not against KM's existing tableau.
