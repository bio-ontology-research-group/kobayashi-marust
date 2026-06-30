# 07 — Cache subtree port manifest (`Reasoner/Kernel/Cache/`)

W0 inventory of `/home/leechuck/Public/software/Konclude/Source/Reasoner/Kernel/Cache/`
**283 files / ~36,143 lines** (incl. `Events/`). These are the saturation /
backend-association / completion-graph / unsatisfiable / computed-consequences /
occurrence caches the hypertableau worker threads share. Scheduled wave **W6**
(after completion+saturation bodies land); the `completion/stubs.rs` cache-handler
markers are the algorithm-facing facades this subtree fills in.

## How the algorithm reaches these caches

The completion/saturation algorithms NEVER touch a Cache class directly. They go
through the **Algorithm-layer cache *handlers*** (in `Kernel/Algorithm/`, stubbed
in `completion/stubs.rs`). Each handler owns a `*CacheReader` + `*CacheWriter`
facade pair for one cache. Confirmed wiring:

| stub in `completion/stubs.rs` | Algorithm/ handler | Cache/ family it drives |
|---|---|---|
| `SatisfiableExpanderCacheHandler` | `CSatisfiableExpanderCacheHandler` | Signature-satisfiable expander cache |
| `UnsatisfiableCacheHandler` | `CUnsatisfiableCacheHandler` | Occurrence-unsatisfiable cache |
| `SaturationNodeExpansionCacheHandler` | `CSaturationNodeExpansionCacheHandler` | Saturation-node assoc-expansion cache |
| `IndividualNodeBackendCacheHandler` | `CIndividualNodeBackendCacheHandler` | Backend representative-memory cache |
| `ComputedConsequencesCacheHandler` | `CComputedConsequencesCacheHandler` | Computed-consequences cache |
| `CompletionGraphCacheHandler` / `ReuseCompletionGraphCacheHandler` / `IncrementalCompletionGraphCompatibleExpansionHandler` | resp. handlers | Reuse-completion-graph cache |
| `OccurrenceStatisticsCacheHandler` | `COccurrenceStatisticsCacheHandler` | Occurrence-statistics cache |
| `DatatypeIndividualProcessNodeHandler`, `ConceptNominalSchemaGroundingHandler` | resp. handlers | (no Cache/ class — Algorithm-only; out of scope here) |

So the **port boundary** is: handlers stay in `completion/`/`algorithm`-layer
(W3/later); this subtree (`cache/`) provides the `*Cache` facade + `*Reader` +
`*Writer` + the entry/slot storage each handler talks to.

## Cache families (top-level classes, grouped)

### F0 — Generic cache base + shared infra (~1.4k lines)
Abstract bases and the shared value/entry/tagging machinery every family builds on.
- `CCache` (130, empty abstract base), `CSatisfiableCache` (136), `CUnsatisfiableCache` (136),
  `CSaturationCache : CSatisfiableCache` (136), `CCompletionGraphCache` (136), `CBackendCache` (136) — marker bases.
- `CCacheValue` (213) + `CCacheValueHasher` (160) — the generic hashed cache key/value.
- `CCacheEntry` (130) + `CCacheEntryWriteData` (143) — generic entry + write payload.
- `CCacheStatistics` (160), `CCacheModificationTagSet` (163), `CCacheTaggingPool` (186) — incremental bulk-reset tagging.
- `CacheSettings.h` (150) — forward-decls + `CCACHINGHASH/LIST/SET = CQtManagedRestrictedModification{Hash,List,Set}` typedefs (the shared concurrent-modification containers).
- per-cache `*Reader`/`*Writer` bases: `CSatisfiableCacheReader/Writer`, `CUnsatisfiableCacheReader/Writer`.

### F1 — Backend representative-memory association cache (~18–19k lines — THE BULK, ~half the subtree)
The realisation/association store: per-individual label associations, role-set
neighbours, cardinalities, nominal indirect connections. `CIndividualNodeBackendCacheHandler`,
`CBackendAssociationCacheHandler`, `CSaturationNodeBackendAssociationCacheHandler` drive it.
- **Facade/IO:** `CBackendRepresentativeMemoryCache` (5,812!), `CBackendRepresentativeMemoryCacheReader` (1,643), `*Writer` (144), `*WriteData` (150), `*BaseContext`/`*Context`/`*OntologyContext` (~500), `*Utilities` (349), `*CachingFlags` (257), `CBackendCache`/`CBackendCacheWriteData` (271).
- **Ontology/label storage:** `*OntologyData` (928), `*OntologyDataRecomputationReferenceLinker` (202), `CBackendRepresentativeMemoryLabelCacheItem` (319) + `*ExtensionData`/`*CardinalityData`/`*CardinalityExtensionData`/`*IndividualAssociationMapExtensionData` (339) /`*MapIterator` (271)/`*IndividualRoleSetNeighbourArrayIndexExtensionData`/`*TagLabelResolving*`, `*LabelSignatureResolveCacheItem`, `*LabelValueLinker`, `*CardinalityCacheItem`/`*CardinalitySignatureResolveCacheItem`/`*CardinalityValueLinker`.
- **Individual association:** `*IndividualAssociationData` (562) + `*IndividualAssociationContext` (241), `*IndividualNeighbourRoleSetHash` (213), `*IndividualRoleSetNeighbour{Array,Data,IndividualIdLinker}`, `*RoleAssertionLinker`, `*ItemIndividualDataAssociationLinker`, `*NominalIndividualIndirectConnectionData`, `*SlotItem` (195).
- **Temporary write-data linker chains (RECORD FAMILY → enum, see below):** `*TemporaryAssociationWriteDataLinker` (430), `*TemporaryAssociationUseDataLinker`, `*TemporaryLabelWriteDataLinker`, `*TemporaryLabelReference{,DataLinker}`, `*TemporaryCardinalityWriteDataLinker`, `*TemporaryIndividualRoleSetNeighbourUpdateDataLinker`, `*TemporaryInvolvedIndividualDataLinker`, `*TemporaryNominal{IndirectConnectionDataLinker,RoleConnectionData}`, `*TemporaryPropagationCutDataLinker` (~13 linker types).
- `CBackendIndividualRetrievalComputationUpdateCoordinationHash{,Data}` (610) — cross-thread retrieval-update coordination.

### F2 — Signature-satisfiable expander cache (~3k lines)
Caches satisfiable label signatures so the expander can skip re-saturating known-sat
labels. `CSatisfiableExpanderCacheHandler`.
- `CSignatureSatisfiableExpanderCache` (720), `*Hasher` (284), `*Entry` (247) + `*EntryExpandWriteData`/`*EntrySatisfiableBranchWriteData`/`*EntryWriteData`, `*Reader` (227), `*Writer` (150), `*SlotItem` (205), `*RedirectionItem` (155), `*Context` (185).
- shared satisfiable bases `CSatisfiableCache{,Reader,Writer}`, `CSatisfiableCache` (an `CSaturationCache` parent too).
- `CExpanderBranchedLinker` (155), `CExpanderCacheValueLinker` (161) — expander value chains.

### F3 — Occurrence-unsatisfiable cache (~2.7k lines)
Caches clash signatures so a known-unsat label set short-circuits. `CUnsatisfiableCacheHandler`.
- `COccurrenceUnsatisfiableCache` (546), `*Reader` (585), `*Writer` (162), `*Entry` (331), `*EntriesHash` (161), `*UpdateSlotItem` (229).
- `CUnsatisfiableCache{,Reader,Writer}` bases, `CIncrementalUnsatisfiableCacheReader` (158).

### F4 — Reuse-completion-graph cache (~2.2k lines)
Caches whole completion-graph fragments for reuse across satisfiability tests.
`CCompletionGraphCacheHandler` / `CReuseCompletionGraphCacheHandler` / incremental handler.
- `CReuseCompletionGraphCache` (327), `*Reader` (422), `*Entry` (234) + `*EntryExpandWriteData`/`*EntryWriteData`, `*Writer` (137), `*SlotItem` (205), `*Context` (165), `*CompatibilityEntryHash{,Data}` (~290).
- `CCompletionGraphCache` base.

### F5 — Saturation-node associated-expansion cache (~3.1k lines)
The saturation pre-pass cache: per-saturation-node associated concept expansions.
`CSaturationNodeExpansionCacheHandler`.
- `CSaturationNodeAssociatedExpansionCache` (404), `*Reader` (157), `*Writer` (139), `*Entry` (218), `*Context` (219), `*ExpansionWriteData` (258), `*UnsatisfiabilityWriteData` (154), `*WriteData` (142).
- `CSaturationNodeCacheUpdater` (278), `CSaturationNodeAssociated{Concept,Deterministic,Nondeterministic}Expansion` (250/148/140), `*ConceptLinker` (153), `*DependentNominalSet` (135).
- `CSaturationCache` base.

### F6 — Computed-consequences cache (~1.6k lines)
Caches derived consequences (types) per individual for the consequence-driven path.
`CComputedConsequencesCacheHandler`.
- `CComputedConsequencesCache` (301), `*Reader` (148), `*Writer` (139), `*Entry` (129), `*Context` (218), `*WriteData` (142), `*WriteTypesData` (165), `CComputedConsequencesTypesCacheEntry` (166).

### F7 — Occurrence-statistics cache (~2.2k lines)
Caches concept/role occurrence stats that feed processing-priority heuristics.
`COccurrenceStatisticsCacheHandler`.
- `COccurrenceStatisticsCache` (245), `*Reader` (188), `*Writer` (226), `*Data` (176), `*OntologyData` (264) + `*Vector` (143), `*Context` (185), `*WriteData` (135), `COccurrenceStatistics{Concept,Role}Data` (134/160), `COccurrenceStatisticsData` (194).

### F8 — Cache events (`Cache/Events/`, ~1.8k lines, 11 event pairs)
Cross-thread message records posted to the writer thread (the concurrency seam):
`CWrite{ExpandCached,SatisfiableBranchCached,SatisfiableCacheEntry,UnsatisfiableCacheEntry,SaturationCacheData,CachedData,ComputedConcequencesCacheEntry,BackendAssociationCached}Event`,
`CRetrieveIncompletelyAssociationCachedEvent`, `CInitializeIndividualAssociationsCacheEvent`,
`CReportMaximumHandledRecomputationIdsEvent`. → ONE tagged enum `CacheEvent` (see below).

## Core vs deep-internal split

**CORE (algorithm actually reaches, via handlers — port first, must be faithful):**
the per-family **facade + Reader + Writer**, plus the **Entry** types and the F0
shared `CCacheValue`/`CCacheValueHasher`/`CacheSettings` containers:
`CBackendRepresentativeMemoryCache{,Reader,Writer}`, `CSignatureSatisfiableExpanderCache{,Reader,Writer}`,
`COccurrenceUnsatisfiableCache{,Reader,Writer}`, `CReuseCompletionGraphCache{,Reader,Writer}`,
`CSaturationNodeAssociatedExpansionCache{,Reader,Writer}` + `CSaturationNodeCacheUpdater`,
`CComputedConsequencesCache{,Reader,Writer}`, `COccurrenceStatisticsCache{,Reader,Writer}`, and the 6
abstract bases. ≈ 22 classes but they carry most of the algorithmic logic (the giant
`CBackendRepresentativeMemoryCache.cpp` = 8k of it).

**DEEP-INTERNAL (storage internals, reachable only THROUGH a facade — port lazily / collapse):**
all `*SlotItem`, `*EntriesHash`, `*Hasher`, `*RedirectionItem`, every `*WriteData`/`*WriteTypesData`,
the ~13 backend `*Temporary*Linker` chains, the `*IndividualAssociationData`/`*Map*`/`*RoleSetNeighbour*`
storage, `*LabelCacheItem`/`*CardinalityCacheItem` variants, `*OntologyData`, `*Context`/`*BaseContext`,
`CCacheTaggingPool`/`CCacheModificationTagSet`. These never appear in a handler signature.

## Proposed port units (dependency order, ≤~800 src lines each)

W6 is downstream of W1–W5, so all model/process/completion ids already exist.

1. **F0 base + shared infra** → 2 units: `cache/base.rs` (the 6 abstract bases + Reader/Writer bases, mostly empty), `cache/value.rs` (`CacheValue`+hasher+entry+statistics+tagging-pool+modification-tag-set + `CacheSettings` container typedefs).
2. **F8 events → 1 enum unit:** `cache/events.rs` (one tagged enum `CacheEvent`, 11 variants).
3. **F7 occurrence-statistics** → 3 units (data/ontology-data, cache+reader, writer+context).
4. **F6 computed-consequences** → 2–3 units (entry+types-entry, cache+reader+writer, write-data).
5. **F3 occurrence-unsatisfiable** → 4 units (entry+entries-hash, cache, reader (585) + incremental-reader, writer+update-slot-item).
6. **F2 signature-satisfiable expander** → 4–5 units (entry+write-data variants, hasher+slot+redirection, cache (720), reader, writer+context+expander-linkers).
7. **F4 reuse-completion-graph** → 3 units (entry+compat-hash+write-data, cache+reader (749), writer+slot+context).
8. **F5 saturation-node expansion** → 4–5 units (assoc-expansion record family (concept/det/nondet/linker/nominal-set), entry+write-data, cache+reader+writer, `CacheUpdater`).
9. **F1 backend representative-memory** → ~26–28 units (the dominant block):
   - `*OntologyData` (2), `*IndividualAssociationData`+context+map-iterator (3), role-set-neighbour family (3), label-cache-item family (3), cardinality family (2), nominal-indirect family (1),
   - **temporary write-data linkers → 2–3 enum units** (collapse ~13 linker types),
   - the facade `CBackendRepresentativeMemoryCache.cpp` (5.8k) → ~8–9 method-batch units, `*Reader` (1.6k) → 2–3 units, `*Writer`+`*WriteData`+contexts+utilities+flags (3), `*RetrievalComputationUpdateCoordinationHash` (1).

**Total estimate: ≈ 55 port units** (F1 backend alone ≈ 27; F0+F2–F8 ≈ 28).
Structure-skeleton sub-wave first (all struct defs + the record-family enums →
compiles with stubbed bodies), then method-batch bodies family-by-family, cheapest
family (F7) first to prove the pattern, backend (F1) last.

## Record-families to collapse to one tagged enum (mirrors the W2 `DepKind` collapse)

- **Backend temporary write-data linkers** (~13 intrusive `*Temporary*DataLinker` chains:
  Association/AssociationUse/Label/LabelReference/Cardinality/IndividualRoleSetNeighbourUpdate/
  InvolvedIndividual/NominalIndirectConnection/NominalRoleConnection/PropagationCut/…) →
  ONE `BackendTempWriteRecord` enum + an owned `Vec<Id>` chain (head-front CLinker convention).
- **All `*WriteData`/`*WriteTypesData`** across families (~15 small payload structs) →
  one `CacheWriteData` tagged enum (or one per cache facade).
- **Cache events** (F8, 11 types) → one `CacheEvent` enum.
- **`*SlotItem`** (Backend/Signature/Reuse/OccurrenceUnsat-UpdateSlotItem, 4 open-addressing
  hash-slot variants) → a generic `SlotItem<T>` rather than 4 structs.
- **Saturation associated expansions** (concept / deterministic / nondeterministic) →
  one `AssociatedConceptExpansion` enum with a determinism tag.

## Shared data structures

- **`CCacheValue` + `CCacheValueHasher`** — the generic hashed key used by every cache; port once in `cache/value.rs`.
- **`CCACHINGHASH/LIST/SET` = `CQtManagedRestrictedModification{Hash,List,Set}`** — the shared
  concurrent-modification containers all caches store entries in. In Rust → arena `Vec<Entry>` +
  `HashMap` keyed by `CacheValue`, gated by the **`CCacheModificationTagSet` / `CCacheTaggingPool`**
  generation counter (bulk-reset between incremental recomputations) — `[memory-pool]`.
- **Reader / Writer / Context triad** per cache: facade owns the hash; `*Reader` = per-thread read
  cursor (read-mostly, lock-free); `*Writer` = applies pending writes drained from the event queue;
  `*Context` = per-thread scratch. Keep the triad — it is the unit of the concurrency model.
- **Intrusive `*Linker` chains** → owned `Vec<Id>`, head-at-FRONT (W2 canonical CLinker convention).

## Concurrency concerns (these caches ARE the shared-mutable surface)

These are the ONLY structures shared across hypertableau worker threads, so the whole
subtree carries `[threading]`. 23 files use `QMutex` / `QAtomic*` / `QReadWriteLock`
(concentrated in F1 backend, F2 signature, F3 occurrence-unsat, F4 reuse-cg, F6/F7).

- **`[threading]` — the Reader/Writer/Event split is the model.** Workers READ through
  per-thread `*Reader` cursors (read-mostly, atomic version/modification-id guarded, mostly
  lock-free); mutation is SERIALISED through the writer: writes are posted as `Cache/Events/CWrite*Event`
  messages drained by a dedicated writer, NOT applied inline. The `SlotItem` atomics are CAS-style
  lock-free slot reservation; the top-level `QReadWriteLock`/`QMutex` guard whole-hash rehash/reset.
- **Faithful-but-staged port:** KM runs process-per-ontology, so the first faithful port can run the
  Event channel **single-threaded** (the worker IS the writer — drain the event queue inline after each
  read), deferring true cross-thread `Reader`/`Writer` concurrency. Mark every such site `[threading]`;
  preserve the Reader/Writer/Event class boundary so real concurrency can be re-enabled later.
- **`[memory-pool]`** — every cache uses per-ontology pool allocators + `*TaggingPool`/`ModificationTagSet`
  to bulk-invalidate entries between recomputations (incremental reasoning). → arena `Vec` + a generation/tag
  counter; reset = bump generation, not free.
- **Atomics** (`QAtomicInt`/`QAtomicPointer` version counters, refcounts, slot-reservation CAS) →
  `AtomicU64`/`AtomicUsize`/`AtomicPtr`-free arena-id CAS; `QReadWriteLock` → `std::sync::RwLock`,
  `QMutex` → `Mutex`, applied ONLY at the facade hash, never per-entry (match Konclude's granularity).
- **`[ownership]`** — SlotItem ↔ Entry ↔ WriteData ↔ Linker raw back-pointers → arena ids
  (`BackendEntryId`, `SlotId`, …); the single global arena decision from `PORT.md §5`.

## Out of scope for this subtree (live elsewhere)
The cache **handlers** themselves (`C*CacheHandler`, `CIndividualNodeManager`,
`CConceptNominalSchemaGroundingHandler`, `CDatatypeIndividualProcessNodeHandler`) are in
`Kernel/Algorithm/` and are already stubbed in `completion/stubs.rs`; they are ported with the
completion engine (W3+), not here. This subtree provides the caches they hold.
