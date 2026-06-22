# Changelog

All notable changes to the kobayashi-marust reasoner. Newest first.

## [unreleased] — CB engine scaling (ORE 2015 coverage push)

### Hypertableau toward SHIQ: sound inverse + functional-merge primitive, two routing-gate fixes, and the Konclude saturation diagnosis (foundations, gated)

Groundwork for solving the disjunction / SROIQ family (`ore_ont_1603, 12653,
16444, 7581, 6934, 9540, 10702, 10908, 15672`) by extending the `Ht`
hypertableau from ALC(H) toward SHIQ, following HermiT's calculus and Konclude's
saturation architecture. Everything here is **gated** (`KM_HT_NUMBER`,
`KM_HT_FORCE`), **zero production impact**, and validated by unit tests; no
ORE coverage change yet — this lands the validated base plus the diagnosis that
re-targets the remaining work.

**Inverse roles in `Ht` — sound, unit-tested.** The `cb_to_ht` inverse bridging
clauses (`r(x,y) → r⁻(y,x)`) already propagate through the existing
`role_triggers → fire_anchor_edge → HeadItem::Edge` path; the prior "inverse is
inert" assumption was wrong about the mechanism. Two tests
(`inverse_role_propagates_universal_back`, `inverse_role_consistent_without_clash`)
confirm `∀r⁻` propagates back along the materialised inverse edge with no
over-propagation. `in_edges` now carries a `DepSet` (the shared structural change
for inverse soundness and node merging).

**Qualified-number node merge (≤n / functional).** Replaced the `apply_head`
`Eq`-head soundness bail with a node-merge primitive (`Ext::merge_into` +
`resolve` + `Trail::Merge`, modelled on HermiT's `MergingManager`): the victim's
concept label and incident edges are copied onto the lower-id survivor under the
union dependency, trail-recorded so backtracking undoes the whole merge; merged
victims are excluded from obligation expansion and blocking. A single `Eq` head
(functionality / ≤1) is a unit merge; multi-`Eq` (≤n, n≥2) still bails soundly.
Three tests (`functional_merge_forces_clash`, `functional_merge_consistent_when_compatible`,
`merge_inverse_existential_terminates`). A gated `RMF_STEP_CAP` bounds the body
matcher so an explosive join falls back soundly to CB instead of hanging.

**Two routing-gate fixes (the reason nothing reached `Ht` before).**
- `tableau.rs` `run_json` had a second in-fragment gate
  (`!inp.number && !inp.inverse && nominals.is_empty()`) independent of the
  `race.rs` routing guard, so every inverse/number ont fell through to the legacy
  tableau (which hangs on real ORE onts) and never reached `Ht`/QoSat. It now
  honours `KM_HT_FORCE`, so the engine actually runs on inverse/number onts for
  measurement.
- `QoSat` (the non-branching saturator) capped at `QO_NODE_CAP = 8000` nodes,
  tuned for the tiny 5303-family. Since QoSat seeds one shared node per concept,
  this bailed instantly on a real ontology (7581 has 72 989 concepts) → fell back
  to the per-concept branching classify, which hangs. The cap now scales with the
  concept count.

**Diagnosis (Konclude trace of 7581).** Konclude classifies 7581 in 5.6 s with
expressiveness `SRIF` (inverse + functional + chains + transitivity; no qualified
cardinality, no nominals): "*ontology has been sufficiently saturated, extracting
data for classification*" + 525 ms classification, i.e. essentially **zero**
tableau tests — the non-branching saturation is sufficient. With the two gates
fixed, KM's QoSat now runs on 7581 and is **bounded** (~73k nodes, no divergence)
but **too slow** (naive worklist + an `O(nodes)` match scan for unbound-source
role atoms; ~860k pending edges). It is a scale/efficiency problem, not soundness
or termination. The next lever is to make QoSat's saturation edge-indexed — the
same ELK backward-link-propagation optimisation already in `elc` — or to extend
`elc` to SRIF and route such onts there.

### QoSat saturation made edge-indexed (the elc backward-link optimisation, ported)

Removes the two `O(nodes)`/`O(#role-clauses)` scans that made QoSat diverge at
the 73k-node scale the 7581 diagnosis identified, porting the exact two index
structures `elc` already uses for ELK backward-link propagation. **Result-identical
by construction** (same clauses fire, same matches found — only located without
the full scans), so it is purely a speed change; gated paths (`KM_HT_QO`,
`KM_HT_HARVEST`) keep their semantics.

- **Incoming-edge index (`QoSat::in_edges`).** `match_body`'s unbound-source role
  case (`r(x, tn)` with `tn` bound, `x` free) scanned all nodes
  (`for sn in 0..label.len()`) to find predecessors of `tn` — `O(#nodes)` per
  match, the dominant cost on transitive / role-chain onts. It now reads
  `in_edges[tn]` (the `(role, source)` list maintained alongside `out_edges`),
  so predecessor enumeration is `O(in-degree)`. The index is trail-recorded and
  rolled back with its out-edge (residue-test DFS stays consistent).
- **Role-keyed clause firing (`QoSat::role_clause_trig`).** The edge worklist
  cloned the entire `role_clauses` list and fired every one on each new edge.
  Role clauses are now indexed by the exact role(s) in their body, so an `r`-edge
  fires only clauses mentioning `r` (a clause without `r` cannot anchor — a
  guaranteed no-op), and clones a tiny per-role bucket instead of the whole list.

New test `qosat_edge_index_role_chain` drives both paths through a transitive
`r`-chain (`A ⊑ ∃r.B, B ⊑ ∃r.G, r∘r ⊑ r, r(x,z) ⊓ G(z) ⊑ H`) and asserts the
closure is unchanged (`H` derived at `node(A)`). Also removed the per-node
`self.global.clone()` in the node-drain loop (an `O(#nodes × |global|)`
allocation), result-identical.

**Measurement (IBEX, 7581, `KM_HT_FORCE`+`KM_HT_QO`, CB isolated).** This
re-targets the prior diagnosis. With the indexes in, 7581 QoSat saturation still
does **not** converge in 420 s (≈1 GB, CPU-bound). Split drain-loop counters
(`QODRAIN`/`QONODE`/`QOEDGE`) show the run never leaves the **literal**
(concept-clause) propagation phase: one `QODRAIN` tick (2M lit-pops), **zero**
node-loop or edge-loop pops. So the role/edge phase the indexes optimise is not
even reached within budget — 7581's wall is the `O(#seeded-nodes × concept-clause
fires)` volume of saturating one shared node for each of its 72 989 concepts
against 455 583 clauses, upstream of the indexed edge phase. The edge index is
correct and necessary (and a clean win on transitive/role-chain onts that *do*
reach the edge phase), but it is not by itself the 7581 lever. The genuine next
lever is architectural, not more saturation indexing: don't seed + saturate 73k
independent nodes — either extend `elc` to SRIF and route such onts to its
told-subsumer single pass, or make the gate per-concept (saturate only the
concept under test). This is the saturation core Phase 5's lazy per-concept gate
needs; the indexing is a prerequisite, the node-count is the remaining work.

### Routing: EL-safe giants retry the repair certificate before CB — recovers 15803 + 6212 (565 → 567)

A head-to-head against ELK and Konclude on our 22 remaining failures (their
recorded `peak_mb`/`wall_s` in the bigsweep) showed that **8** of them ELK
classifies *correctly* (gold-match) in seconds at <3 GB while KM times out — and
two, **15803** and **6212**, are EL-safe **>100 MB giants**. For giants the
`elc`-portfolio is suppressed (racing CB and `elc` concurrently OOMs on a
>100 MB ont), so an EL-safe giant with a non-EL TBox residual (a covering
disjunction here) fell to *bare* `elc` with the certificate **off**, bailed
before saturating, and went to the CB engine — which blows up to 18 GB and times
out at 240 s.

Fix (`orchestrate/mod.rs`): when the bare-`elc` attempt on an EL-safe giant
returns "not EL", **retry `elc` with the repair certificate** (`KM_ELC_CERT=2`),
bounded by the existing `elc_force` wall (100 s) and RSS (14 GB) budgets, before
falling through to CB. When the canonical EL model certifies the residual — an
inert / covering disjunction whose EL answer is already complete, exactly what
ELK computes by dropping the non-EL axioms — `elc` answers soundly in EL time and
memory. The retry runs `elc` alone (sequential), so it does not reintroduce the
concurrent-race OOM the giant suppression avoids; the pure-EL giants (8737,
16744, no residual) solve on the first attempt and are untouched.

Result (full `km classify`, default config, gold = Konclude):
- 15803: 240 s timeout / 18 GB → **20.7 s / 1.26 GB, gold-clean** (2 432 194 subs)
- 6212: 240 s timeout / 18 GB → **76.8 s / 1.24 GB, gold-clean** (243 963 subs)
- 8737 / 16744: unchanged, gold-clean.

The other 6 ELK-correct failures (1603, 12653, 6934, 10908, 16444, 7581) are
`el_rbox_safe=False`: their residual is an uncheckable shape (nominals / inverse)
on which the certificate bails, or it saturates then fails — they remain CB/HT
work. The other 14 of the 22 are cases where ELK only *approximates* (drops the
non-EL axioms and disagrees with gold), so they are not EL-recoverable. Note: on
the genuine EL giants KM now uses **less** memory than ELK (8737: ELK 16.4 GB JVM
vs KM 5.5 GB).

### `elc` ELK backward-link propagation + parse-tree discard — 8737 classify 63s → 22s, peak 9.7GB → 5.5GB

Ported ELK's core EL++ saturation optimisation (the *backward-link propagation*
join, "The Incredible ELK" §5) into `elc`, after mapping the ELK Java source
(`ContextImpl`, `SubsumerBackwardLinkRule`, `SubsumerPropagationRule`,
`PropagationFromExistentialFillerRule`). Both changes are **result-identical**
(113 tests pass; 8737 and 16744 both gold-clean, 0 unsound / 0 incomplete).

**Backward-link propagation (time).** After the filler-label indexing, the
Edge-NF4 rule still rescanned `role_supers(r) × nf4_label[d]` per edge — 4.33B
hashmap *probes* on 8737 (`KM_ELC_PROFILE`), most of them missing. ELK instead
keeps, per context, a *propagation* store keyed by role. `elc` now maintains
`prop[(d, r)] = {E : ∃r.X⊑E, X∈label[d]}` keyed by the **exact** edge role
(role-subsumption is already handled by the pre-existing edge-lift, which
materialises every super-role edge as its own worklist item). A new edge `(c,r,d)`
fires `prop[(d,r)]` with a single hashmap lookup; a new filler-subsumer at `c`
registers its conclusions into `prop[(c,·)]` and fires the exact-role backward
links already at `c`. Each (backward link, propagation) pair fires exactly once,
whichever is created second — the same join ELK's two rules perform. Edge-rule
hashmap lookups collapse from **4.33B to 23M** (one `prop.get` per edge); the old
`(role,filler)->[sup]` index is removed. **8737 classify 63s → 22.4s.**
A propagation-Set dedup (ELK's `propagatedSubsumers_` is a Set) was implemented
and measured: bucket-duplication on 8737 is <0.5%, so it only added a `contains`
cost — reverted.

**Parse-tree discard (memory).** ELK drops the OWL parse tree once axioms are
indexed; `elc` was holding the full input — millions of `JClause`, each owning
`String` IRIs — alive through saturation (the `&[JClause]` borrow kept it pinned
in `run_elc`). `to_nf` already interns the EL part into `nfs` (u32-keyed) and
clones the non-EL part into the residual, so the original clause set is dead from
there. `classify` now takes the clauses **by value** and drops them right after
`to_nf`, before saturation, so the parse tree never coexists with the peak
saturation state. **8737 peak RSS 9.7GB → 5.5GB (−43%)**, 16744 likewise; the
explicit dealloc adds a few seconds of allocator work on the giants (the OS would
otherwise reclaim it at process exit) but the giants sit far under the 240s
timeout, and the headroom matters under the parallel memcap.

### `elc` NF4 saturation: filler-label indexing — 8737 classify 84s → 63s

Profiling `elc` on the EL giant 8737 (the slowest EL-routed ORE ont) showed the
saturation is entirely NF4 (`∃R.D⊑E`): the Edge rule scanned **8.6 billion**
`(super_role, d_super)` probes (the whole subsumer label `sub_super[d]` per edge)
and the Sub rule another **1.68 billion** (`KM_ELC_PROFILE` counters; `perf` is
unavailable on the cluster). NF2/NF7 were zero.

ELK only ever propagates over *existential fillers*, so the label entries that can
fire NF4 are exactly the ones that are NF4 fillers. Two changes, both
**byte-identical** (113 tests, same 409836 subjects on 8737):
- **Edge rule** scans `nf4_label[d]` — the maintained subset of `sub_super[d]`
  whose members are NF4 fillers (`is_filler` set once at init; the subset is
  appended in `add_sub`) — instead of the full label. 8.64B → 4.33B probes (about
  half of 8737's label entries are not fillers).
- **Sub rule** is gated on the new subsumer `d` actually being an NF4 filler
  (`nf4_by_filler`), so the predecessor scan runs only when it can fire, not on
  every Sub item. 1.68B → 505M.

8737 classify **84.3 s → 63.3 s (−25%)**, no result change. (An earlier attempt
that iterated the NF4 axioms per edge instead was *slower* — 8737 has many NF4
axioms per role — and was discarded; the filler-label subset is `⊆ sub_super[d]`,
so it is never worse than the original.) A gated `KM_ELC_PROFILE` prints the
per-rule scan counters.

### EL++ reflexive roles in the EL completion (`elc`) — ELK-guided

Native support for `ReflexiveObjectProperty` in the EL fast path, so ontologies
whose only non-EL RBox feature is reflexivity route to `elc` instead of the CB
engine. Studied ELK's source first (`liveontologies/elk-reasoner`): it normalizes
`Reflexive(R)` to `⊤ ⊑ ∃R.Self` and decomposes that into a self-loop link at every
context (`IndexedObjectHasSelfDecomposition`), letting the ordinary composition /
range rules fire over it.

The port mirrors that semantics by **seeding self-edges**: `to_nf` parses the
frontend's reflexive fact `[] → R(x,x)` into a `reflexive_roles` set (instead of
dumping it to the residual), `build_idx` closes it up the role hierarchy
(`R(x,x) ∧ R⊑S ⟹ S(x,x)`), and `classify_inner` adds a self-edge `(C,R,C)` at
every satisfiable concept node. Every existing rule (NF4 `∃R.D⊑E`, NF7 `R∘S⊑T` in
**both** chain positions, ⊥-edge, role-lift) then fires through the normal
fixpoint — no new rule logic. Because a materialized self-edge feeds NF7 in both
directions, this also covers the reflexive-role-plus-chain case ELK marks only
partially supported.

Routing: `rbox.rs` splits the old shared `"reflexivity"` fence into
`ReflexiveObjectProperty` (now EL-safe, admitted by `el_rbox_safe` /
`el_rbox_safe_relaxed`) and `IrreflexiveObjectProperty` (the `R(x,x)→⊥` constraint,
still fenced to CB).

Validation: 2 new `elc` unit tests (NF4 elimination + reflexive∘chain), full suite
113/113. On the ORE corpus the change is confined to the 13 reflexive ontologies —
4 newly route to `elc` (10326, 13078, 8298, 869). The 2 *scored* ones are
gold-clean **byte-identical** (8298 12200/12200 subs, 869 12224/12224; 0 unsound /
0 incomplete) and now finish in ~0.25 s / 42–65 MB on `elc`. Full-corpus
regression sweep: 0 unsound / 0 incomplete (the 9 remaining reflexive onts keep
their CB routing unchanged).

### HT speed: blocking refinements + the per-build floor — 5303 10s→8s seq, 5s→4s par

Two more refinements to incremental subset blocking (`KM_HT_INCRBLOCK2`), both
result-identical (`KM_HT_INCRBLOCK2_CHECK` asserts equality with the full scan every
pass: 0 mismatches over all ~250k recomputes; subs 238/238; 111 tests):
- backtrack now rebuilds only the affected **suffix** — track the smallest node
  whose subset-blocking label changed (a concept removed, or the node removed) and
  set `i2_lo` to it, instead of forcing a full rebuild (`i2_lo = 0`) every backtrack.
- `i2_recompute` clears/retains only the posting-list slots that ever received an
  entry (`i2_touched` + a dedup bitmap), instead of scanning the whole
  `2x|concepts|` slot table on every pass.

Standalone 5303: 10s → 8s single-threaded, 5s → 4s on 8 threads. Corpus-clean
(5303 + the emelim canaries + sampled normals, 0 unsound / 0 incomplete).

**Two larger levers investigated and ruled out — with data:**
- **"Build the deterministic core once, clone per test"** (HermiT/Konclude-style
  amortization of a query-independent backbone). `KM_HT_COREPROBE` shows the
  empty-seed (⊤+TBox) model of 5303 is a **single node**, and the per-concept
  models (256–3064 nodes) share **0%** of their nodes with it — every model is
  100% derived from its own seed concept, so there is no backbone to amortize.
  Consistent with the HermiT trace (it builds 134 fresh models in 0.94s, ~7ms each,
  with no core-sharing). Not viable here.
- **Cutting the blocking suffix further.** `KM_HT_STATS` reports
  `calls / full_rebuilds / avg_suffix`: 249k recomputes, only 1.3% full rebuilds,
  avg suffix 98 nodes. The suffix is already minimal: subset blocking is a
  *sequential dependency* (`blocked[n]` = does any earlier UNBLOCKED node's label
  contain n's), so a change at position `lo` can flip every later node and
  `[lo..nn]` is the smallest correct recompute. `lo` stays low only because the
  live-disjunction family resolves ⊤-disjunctions on mid-id nodes throughout the
  search — intrinsic, not an artifact. Cutting further would need a different
  blocking *signature* (positive-only — changes which nodes block, an ALC+⊔
  completeness risk) or bitset labels (a large `Ext` refactor), not a cheaper
  recompute.

Net for the live ∀+⊔ family's canonical member: **ore_ont_5303 went from a 207s
timeout to ~4s** (parallel) across this work, all sound + complete + result-identical
to the reference search; HermiT (~0.94s) is ~4x off, the practical floor for the
sound+complete subset blocking that this fragment requires (the cheaper core-hashing
modes explode on it).

### HT speed: incremental ∃-obligations (KM_HT_INCROBLIG) — 5303 10s seq / 5s par

With blocking fixed, profiling (`KM_HT_STATS` now splits the per-test wall into
block / prop / expand) put **72% of the wall in the obligation loop** of
`process_obligations`: it re-scanned EVERY accumulated ∃-obligation on every
saturation pass — 240M iterations on 5303 (~933 per pass), each re-running
`has_rsucc` (an out-edge scan). 92% of obligations sit on blocked nodes (skipped
every pass) and most of the rest were already discharged — pure rescan.

Two parallel structures make the loop incremental:
- `node_obligs[n]` indexes a node's obligation positions, so a pass gathers only
  the obligations of currently-UNBLOCKED nodes (the few that can expand), processed
  in index order so the expansion sequence — and the result — matches the flat scan.
- `oblig_sat[i]` marks an obligation discharged (a successor exists), so even among
  unblocked nodes a satisfied obligation is skipped without an edge rescan. Both are
  pruned/cleared on backtrack (a removed edge can un-satisfy one → re-verify).

Together the obligation loop drops from **240,853,407 to 3,155,424 iterations
(76x)** and from 25.8s to 2.3s (11x). Standalone 5303: **25s → 10s single-threaded,
~5s on 8/16 threads**; RESULT-IDENTICAL (subs 238/238, set byte-identical to the
flat scan), 111 tests pass. From the original 207s timeout this is ~40x; HermiT
(~0.94s) is now ~5x off. Wired ON in `orchestrate/race.rs` `spawn_ht`.

### HT speed: incremental subset blocking (KM_HT_INCRBLOCK2) — 5303 25s seq / ~10s par

Profiling the solved-but-slow 5303 (KM_HT_STATS) located the residual cost
exactly: **blocking recompute was 65% of the per-test wall**, and the models are
only ~313 nodes, 92% blocked — **tighter than HermiT's 690-node models**. So KM
was never over-expanding (it folds more than HermiT); the gap was that
`compute_blocked` rescanned every node on every saturation pass (O(n²) per build).
A battery (all under the EAGER+NEGTRIED+ORD=1 combo) confirmed the only viable
lever: the O(n)-hashed blocking modes (core / pairwise) explode the model
(24684 / 14631 nodes, timeout) — **only subset blocking folds 5303** — and
`KM_HT_WITREUSE` is both incomplete (236 ≠ 238) and slower. So subset blocking had
to be made cheap, not swapped out.

`KM_HT_INCRBLOCK2` does exactly that. Blocking is strictly by an EARLIER node
(`m < n`), so `blocked[n]` depends only on nodes `<= n`. Tracking `i2_lo` = the
smallest node id whose label changed since the last compute (a fresh
`add_concept`, a new node, or a backtrack → 0) means a recompute re-evaluates only
the suffix `i2_lo..nn` in id order — a forward pass equal to a full pass because
every node `< lo` is unchanged. In tableau the frontier (label growth + new nodes)
sits at high ids, so the suffix is usually tiny. The posting lists hold only
**unblocked** candidate blockers (the prior `KM_HT_INCRBLOCK` kept all nodes and
was slower on heavily-blocked models).

**Result-identical** to the full scan: `KM_HT_INCRBLOCK2_CHECK` asserts equality
on every pass — 0 mismatches across all 94 5303 builds, output set byte-identical
(238/238 gold-clean), 111 tests pass. Blocking dropped 65% → 23% of wall;
standalone 5303 **54 s → 25 s single-threaded, 24 s → 10 s on 8 threads, 9 s on
16**. Wired ON in `orchestrate/race.rs` `spawn_ht` alongside the search combo
(respecting env overrides). HermiT is ~0.94 s, so KM is now ~10x off (from
~25-50x); the remaining cost is propagation + expansion (the next frontier).

### ore_ont_5303 SOLVED: sound + complete via HT search discipline + fast blocking

`ore_ont_5303` (the canonical ALC(H) member of the live ∀+⊔ disjunction family,
KM's longest-standing timeout) now classifies **sound + complete** — 238/238
subsumptions byte-equal to Konclude gold, unsound=0 incomplete=0 — for the first
time. Standalone HT: **207 s → 23 s single-threaded → ~10 s on 8 threads.** The
+1 completeness gap (CarbonHydrogenSubstructure ⊑ Hydrocarbon) vanished under the
new search; no frontend / transitivity fix was needed.

The gap was never algorithmic — HermiT classifies all of 5303 in ~0.94 s (traced:
134 SAT tests, ~129 backtracks/test). It was **search discipline that KM had but
left OFF by default**, plus a per-step blocking cost:

- **Search combo (the lever).** `KM_HT_EAGER` (fire ⊤-disjunctions only on
  unblocked nodes) + `KM_HT_NEGTRIED` (HermiT startNextChoice: assert ¬D_di after
  a disjunct clashes so siblings unit-propagate) + `KM_HT_ORD=1` (least-failing-
  first disjunct order). Each is inert alone; together they cut the hard concept
  from 6779 backtracks to **41** (fewer than HermiT). Wired ON for the HT racer in
  `orchestrate/race.rs` (respecting explicit env overrides). Sound + complete:
  these reorder / unit-propagate a complete search, never changing SAT/UNSAT.
  Model-shaping levers (pairwise blocking, trigger absorption, harvest) and
  contrapositive determinism were measured and do NOT crack 5303 — search
  ordering does. Conflict learning / QO / SATFOLD remain dead-ends
  (`docs/5303-ATTEMPTS.md`).

- **Inverted-index subset blocking (per-step cost).** `compute_blocked` mode 1
  (subset, the only mode that folds the family enough) was an O(n²) pairwise scan
  recomputed every propagation pass — ~73 % of the per-test wall. Replaced with a
  posting-list intersection over a **reused, concept-id-indexed flat buffer**
  (`BlockBuf`, no per-call HashMap alloc/hashing): a node is blocked iff it
  appears in the posting list of every concept of an earlier unblocked node, so
  only the rarest concept's list is scanned. **Result-identical** to the O(n²)
  scan (canonical set-equal confirmed; old scan kept under `KM_HT_BLOCK_SLOW`).
  114 s → 23 s on 5303; speeds every HT-routed ont.

- **Parallel classify (`KM_HT_PAR=N`).** `Ht::classify`'s 94 per-concept SAT
  tests + Phase-2 confirmations now run across N worker threads via dynamic
  work-stealing (shared atomic index; each worker builds its own `Ht`, 512 MB
  stack for the deep ORD=1 recursion). Set-identical to sequential (a true
  subsumer is in every model's root label; Phase 2 confirms), no Lean re-cert
  (a scheduling change over the same search). The HT racer defaults `KM_HT_PAR`
  to the core count; `nice` keeps it yielding to CB on CB-winning onts.

No soundness regressions: the emelim canaries (9024/12141/541/11460/15491/4604/
9635) and sampled normals stay gold-clean. Lean re-certification deferred (HT and
`cb_to_ht` are not the certified CB calculus).

### QuasiOrderClassification (KM_HT_QO): validated as a dead-end for the disjunction family, gated OFF

The QO driver (`hypertableau.rs::quasi_order_classify` + `QoSat`, ~1265 lines)
ports the Konclude/HermiT architecture both trace docs identify as the reason
Konclude solves the live ∀+⊔ family in <0.2 s: ONE non-branching global
shared-node saturation (disjunctions parked, never case-split; common-disjunct
consequences harvested deterministically), then sat/unsat + possible-subsumers
read off that single model, with a real residue SAT test ONLY for the
"insufficient" concepts that still anchor open parked disjunctions. The premise
is that ~95% of concepts are decided for free.

**That premise is false for this family — proven, not assumed.** Added the
`KM_HT_QO_TALLY` diagnostic (counts dead/sufficient/insufficient per ont without
bailing on the first residue test). On the target onts (IBEX job 47644078):

- **5303**: global model builds, but `queries=94 dead=3 suff=0 insuff=91`,
  median 17 / max 18 open disjunctions per insufficient concept. EVERY concept
  needs a full branching residue SAT test — zero QO leverage. The 22 global
  ⊤-disjunctions saturate every node, so no concept is ever "sufficient".
- **10702 / 1603 / 12653 / 541**: the non-branching global park-saturation
  itself does not terminate in budget (the ∃-chain / transitive blow-up).

**Validation sweep (job 47644343, 587 onts × 2 arms over `km classify`):** arm
`qo` (default-on) vs arm `noqo` (`KM_NO_HT_QO`) differ on exactly 2 onts — 9024
and 12141 both go gold-clean → incomplete-by-623-subsumptions under QO. QO
recovers 0, regresses 2, introduces 0 new unsoundness, no timeout change. So
default-on QO is a strict −2.

**Decision: gated OFF.** `orchestrate/config.rs` `ht_qo` is now opt-IN
(`KM_HT_QO` env), was opt-out (`KM_NO_HT_QO`); the HT racer reverts to the
validated `Ht::classify` (the 565 gold-clean baseline). All QO code stays behind
the flag, inert by default, kept for the record. Build green, 111 lib tests pass.
Confirms the structural diagnosis (`project_km_5303_diagnosis`,
`project_km_family_diagnosis`): this family needs HermiT-grade absorption +
model-based classification, not the QO harvest. The naive `qo_branch_dfs`
residue search (chronological backtracking, depth-64 guard) is itself strictly
weaker than the `Ht::classify` it falls back to.

### Live-disjunction family (5303): decision-on-demand + contrapositive enrichment (in progress, all gated default-off)

Attack on the live ∀+⊔ family (5303/10702/1603/9540). Two mechanisms added, both
sound clause-level enrichments, gated, default-off (no production impact, no Lean
re-cert until empirically validated):

- **`KM_HT_DOD`** (`tableau.rs`): DPLL-style unit propagation over disjunctions —
  inside the saturation fixpoint, a fired disjunction whose disjuncts are all
  refuted but one asserts that survivor deterministically (sound resolution, dep =
  body ∪ refuting deps), one with all refuted clashes; only ≥2-open disjunctions
  branch. The branch loop also skips refuted disjuncts (deps folded into the
  no-good). `KM_HT_CONTRA` companion: contrapositive Horn clauses for clash clauses
  (`A⊓B⊑⊥ ⇒ A→¬B, B→¬A`) so negative literals propagate and feed unit propagation.

- **Key finding:** `run_json` (`tableau.rs:4482`) routes every ALC(H) KB to
  `hypertableau::Ht`, not the legacy `Tableau`, whenever `KM_HT=1` (always set by
  the orchestrator). The family runs on `Ht`. `Ht` already implements
  decision-on-demand (`eval_disj`: Clash/Unit/Branch) plus `KM_HT_WATCH`,
  `KM_HT_NEGTRIED`, `KM_HT_EAGER`, but a clash clause only `raise_clash`es when
  both literals are present — `Ht` never derives the negatives its unit-propagation
  needs. The contrapositive generator was therefore ported into **`Ht::new`**
  (`hypertableau.rs`, `KM_HT_CONTRA`); the `tableau.rs` DOD/CONTRA remain for the
  out-of-fragment fallback. Build green, 111 lib tests pass.

- **Konclude divergence trace:** `docs/konclude-trace-5303.md` (showboat,
  verify-clean) traces Konclude vs KM from source on 5303: Konclude keeps one
  shared node per concept (not model-size), parks disjunctions and never splits
  (harvesting subsumers via common-disjunct extraction), and SAT-tests only the
  INSUFFICIENT residue (~5%); KM's HT builds a model-sized graph and case-splits.
  CONTRA/DOD make individual disjunctions cheaper but do not change that structural
  blow-up — empirical CONTRA×WATCH/NEGTRIED/EAGER measurement on `Ht` underway.

### Hybrid CB/HT main reasoner: KM_HT hypertableau fills CB's coverage gap (monotone-safe)

The ported HermiT-style hypertableau (`hypertableau.rs`, `KM_HT`, driven via
`cb_to_ht`) is sound on its routable fragment (lossless conversion, no inverse,
no nominals; ALCQ allowed) and classifies central-blow-up / context-explosion
ontologies the CB engine times out on. Verified gold-clean through the *same*
`ore_canon.canonicalize` that produces the gold signatures (`engine/py/ht_check.py`):
HT is sound everywhere (no wrong subsumption) but incomplete on the live
disjunction family, with no structural rule separating its complete from its
incomplete onts — so it can never safely replace a CB answer.

`owl_classify` gains `_spawn_ht` + `_race_cb_vs_ht` (gated `KM_HT_RACE`). CB is
the certified primary on one fewer core; the HT racer (single-threaded, niced)
fills only CB's gap:

* `KM_HT_MODE=fallback` (default): HT's answer is used only on a CB failure /
  `KM_HT_BUDGET_S` timeout — monotone, cannot regress a CB-solved ontology.
* `KM_HT_MODE=race`: first valid finisher wins (faster, but can take an
  HT-incomplete answer).

Full ORE sweep (587 onts, 240 s / 20 GB, gold byte-clean; jobs 47570890 /
47571283 / 47571284): base 558, **fallback 562 (+4: ore_ont_4604 9635 11460
15491, 0 regressions)**, race 559 (+3, 2 regressions). Fallback deployed as the
new main hybrid; race not used. HT engine brought from the `ht-port` branch (3
files; CB core unchanged), all gated/inert by default. See `docs/HYBRID-CB-HT.md`.

### Tableau race un-shadowed by the absorption portfolio + gate relaxation for faithfully-encoded number/inverse/nominals (KM_TAB_FEAT)

Side-by-side ORE benchmark (Konclude/ELK/HermiT/KM, one ont per job, all
reasoners sequential on the same IBEX node, 600 s / 56 GB) showed KM and HermiT
time out on DISJOINT sets: 17 onts time out KM but HermiT solves (the live ∀+⊔
disjunction family), 12 time out HermiT but KM solves (near-Horn throughput).
Attacking the HermiT-solves-KM-does-not set surfaced two issues:

1. **The tableau racer was dead in production.** Routing was
   `if KM_ABSORB_PORTFOLIO and KM_ABSORB: _race_absorbed_plain(...)` /
   `elif KM_TAB_RACE: _race_cb_vs_tableau(...)` — mutually exclusive, and the
   production config sets both absorb flags, so `KM_TAB_RACE` was never reached.
   `_race_cb_vs_tableau` now takes an `engine_run` callable and the absorb
   portfolio runs *inside* the tableau race (the tableau is lazy/niced/
   single-threaded, so it costs ~nothing on onts the engine finishes fast).
2. **The race gate deferred on any number/inverse/nominal flag**, even when
   cb_to_ht encoded the feature losslessly (`dropped==0`, `fenced==[]`).
   `KM_TAB_FEAT` lets the tableau race those when nothing was dropped; soundness
   is validated by gold comparison.

Diagnosis of the 15 gold-having targets (none out-of-fragment — all
`dropped==0, fenced==[]`): with the race reached + gate relaxed, **9635 is
recovered gold-clean** (0.4 s, 159 subsumptions, byte-identical to Konclude
gold). The other 14 still time out at 600 s: KM's cache tableau does not
converge on them (5303/9024: 4–5 M dpll steps, depth 400–760, 1000+ restarts;
1603/12653/15672: number/nominals route to the non-cache careful/expand path
which does not terminate). Closing those needs HermiT-grade tableau search
(anchored/pairwise blocking + dependency-directed backjumping), not a gate flag.

### Cache-tableau convergence control — Glucose dynamic restart + no-good DB reduction (KM_TAB_CONV)

Targets the live `∀ + ⊔` disjunction family (5303, 1603, 12141, 10702, 9540, …):
onts the cache tableau reaches but where the DPLL search *oscillates* and never
converges (5303: ~8 M dpll steps, depth 483, still times out). The machinery
that should help — Luby restarts, VSIDS, phase saving — already existed but was
gated off and "recovered 0", because two things were missing:

1. **Unbounded no-good store.** `learn_cap` defaulted to 2 000 000 and
   `check_nogood` runs on *every* DPLL step over the watch lists, so the store
   itself made each step super-linear. Added **size/quality-based DB reduction**
   (`maybe_reduce`): once the store passes `reduce_at` (30 000), keep all "glue"
   (size ≤ 2) lemmas plus the shortest half and rebuild the watch index. Sound —
   a no-good is an entailed lemma, so dropping it only loses pruning.
2. **Pure-Luby restarts fight the deep ∃-chain cache.** A fixed schedule
   restarts mid-chain and discards the conditional pseudo-model cache, forcing a
   full re-walk. Replaced with a **Glucose dynamic restart** (`note_conflict`):
   restart when the *recent* conflict quality (proxied by reason size, smaller =
   better) is materially worse than the global average — the oscillation
   signature — **unless the search is currently deep** (the blocking rule: it is
   building a large model, so do not throw the deep chain's cache away just as it
   converges). Driven off *every* resolved conflict, tainted or not, so it
   engages on the imposed-disjunction (∀+⊔) family where global learning rarely
   fires; VSIDS activity + phase saving still accumulate across restarts to
   redirect the fresh search.

`KM_TAB_CONV=1` bundles the stack (VSIDS + phase + dynamic restart + reduction);
individual flags (`KM_TAB_DYNRESTART`, `KM_TAB_REDUCE`, `KM_TAB_VSIDS`,
`KM_TAB_PHASE`, tunables `KM_TAB_DYN_MARGIN`/`_BLOCK`/`_WIN`, `KM_TAB_REDUCE_AT`)
still override. All of it is pure search-order / redundant-lemma management — it
cannot change the SAT/UNSAT verdict — so no Lean re-cert. Reached in the pipeline
via the existing `KM_TAB_RACE` cache racer (which inherits the job env). Default
OFF pending the IBEX A/B (disjbase vs disjconv, jobs 47529537/8).

### Auto-route KM_SEQ_ORDER by DISJ_INT — self-selecting Sequoia ordering (+6, net faster, gold-clean)

Commit `9aee987`. Rather than ship `KM_SEQ_ORDER` default-on (which taxes
near-Horn onts — 6423 went 6 s → 126 s forced), the engine now decides per
ontology. `Reasoner::saturate` computes **DISJ_INT** (does any clause head hold
≥ 2 concept literals with ≥ 1 internal/normaliser definer?) and calls
`calc::set_seq_order_auto`, enabling the Sequoia definer ordering only when
DISJ_INT ≥ 1. Env still wins: `KM_SEQ_ORDER` forces on, `KM_NO_SEQ_ORDER` forces
off. Both orderings are complete (named concepts stay mutually incomparable
either way), so the router only selects the faster validated regime — no Lean
delta beyond the definer-ordering follow-up already noted below.

Why DISJ_INT is the right feature (`results/seqorder-routing-20260615.txt`,
full-corpus DISJ_INT × regression wall-deltas): `KM_SEQ_ORDER` only changes
derivation when same-term literals include internal definers, so it helps exactly
the onts with definer-disjunctions and merely adds `is_internal` overhead on the
rest. The rule keeps all +6 recoveries and 7/11 speedups, avoids 27/28 slowdowns
(incl. the 6423 +120 s outlier, DISJ_INT = 0 → off); only 18/540 passers route on.

Confirmed two ways on IBEX (new binary, 83 cargo tests pass):
- **Auto sweep, no env flag** (47522857, 587 onts): **546 MATCH, 0 DIFF**,
  gained the same +6 (5107 6246 6682 10908 11016 11291), lost none — set
  *identical* to forced-on. `results/auto-route-confirm-20260615.txt`.
- **Same-sweep base(forced-off) vs auto A/B** (47523500, 2×587, same nodes):
  base 540 / auto 545 MATCH, both 0 DIFF, lost none; on the 540 both-pass onts
  **auto is net −24.6 % wall** (1968 s vs 2610 s) — it captures the
  disjunction-ont speedups while routing pure-Horn onts off (6423 back to 13 s).
  10908 (~190 s) is borderline: ok in the dedicated sweep at 133 s, timed out
  under the heavier 2-arm contention here; base misses it too, so not a
  regression. `results/auto-route-AB-20260615.txt`.

Combination round 2 (47521666, `results/combo2-20260615.txt`): `seqorder` ×
{corecap, earlyunsat, unitsfirst, split, tabrace} recovered **0** of the 29
hardest remaining onts — the residual (disjunction-convergence + throughput
memory) is algorithmically hard, not reachable by composing these performance
levers. (The memory levers do reduce RSS — corecap/units/split flip 15491/10860
memout→timeout — just not enough to finish.)

Deploy: the auto-routing binary is the deliverable (no config change needed —
auto is the default). ws was down this session, so it was built on IBEX; a
production rollout means deploying the rebuilt binary to unimatrix and a
confirmation sweep.

### KM_SEQ_ORDER regression sweep: +6, zero regressions, gold-clean (deploy gate PASSED)

The portfolio (below) found `KM_SEQ_ORDER` recovers +6 onts. Before deploy, the
open risk was whether the Sequoia ordering regresses any currently-passing ont
(memory had it OOMing 5303). Regression sweep (IBEX job 47520358, 1174 jobs = 2
arms × 587 gold onts, 240 s / 20 GB, `KM_ABSORB=1`; raw =
`results/regress-seqorder-20260615.txt`, script `…-20260615.sbatch`):

| Arm | GOLD=MATCH | NOSIG | DIFF (unsound) |
|---|---|---|---|
| base       | 540 | 47 | 0 |
| seqorder   | 546 | 41 | 0 |

- **GAINED** (seqorder ok, base not): 5107 6246 6682 10908 11016 11291
- **LOST / regressed** (base ok, seqorder not): **NONE**

`KM_SEQ_ORDER` **strictly dominates** base on the full gold corpus: +6, 0
regressions, 0 unsound (every one of its 546 answered onts is byte-identical to
Konclude). 5303 stays a non-ok in both arms (it is in neither MATCH set), so its
known OOM is not a regression. This is the strongest validation available — not
just "no regression vs KM base" but "matches the gold reasoner on every ont it
answers." **Verdict: deploy `KM_SEQ_ORDER=1` in the production config** (expected
554 → 560 on the unimatrix pipeline; production sweep validates at scale).

Soundness/completeness note (`engine/src/calc.rs:481`): `KM_SEQ_ORDER` keys the
literal order on named-vs-auxiliary (Sequoia's `ContextLiteralOrdering`): named /
query concepts stay mutually incomparable at the bottom (the unrestricted
`CompletenessProp` regime the Lean proof certifies, so the forward `⊤→B(x)`
readout remains complete), and only internal definers are totally ordered above
(ordered resolution, resting on Sequoia's published SROIQ-classification
completeness). The definer-ordering restriction is the one piece not covered by
KM's current Lean proof; a follow-up Lean cert of ordered resolution on definers
is warranted, but the corpus-wide gold-clean result is decisive empirical backing.

### Candidate portfolio vs the 36 failing onts (branch `portfolio-candidates`, IBEX)

Method (user-directed): instead of deep-diving one improvement, implement several
gated candidates in one binary and race them — and the existing flags — against
the exact failing set on IBEX, gold-compared at 240 s / 20 GB, then combine the
winners. Self-validating: a wrong arm shows as GOLD=DIFF, never a false win.

Failing set = the 36 onts where Konclude=ok but KM≠ok in sweep 6524 (554 ok / 34
timeout / 2 memout): 10621 10702 10860 10908 11016 11291 11460 1194 12141 12653
14817 15491 15516 15672 15803 1603 2669 3215 4604 4669 5107 5303 541 6246 6682
6934 7246 7499 7581 7914 8737 9024 9540 9635 9663 9724.

New gated candidates (all default OFF/inert; commit `31764e0`):
- `KM_CORE_CAP=K` — cap the central successor core size; excess fact triggers
  ride back as `p→p` hypotheses (completeness-safe), bounding the core-growth
  cascade (the shared root cause of the throughput and disjunction blow-ups).
- `KM_SEED_FROM_SUBSET` — seed a grown-core successor from its (subset-core)
  predecessor-in-the-chain instead of re-deriving; sound, fixpoint-preserving.
- `KM_TODO_UNITS_FIRST` — work off empty-body (fact) clauses first; confluent.
- `KM_EARLY_UNSAT` — clear a context's todo once it derives ⊥ (subsumes all).

Portfolio arms (14): base, corecap4, corecap8, seedsubset, unitsfirst,
earlyunsat, combo(all 4), nocentral(ST), highcap(MSG_CAP=200M), split, seqorder,
notrigskip, threads16, tabrace(cache tableau).

**Results (IBEX job 47519642, all 504 jobs complete; raw =
`results/portfolio-20260615.txt`, script = `results/portfolio-20260615.sbatch`):
9 GOLD=MATCH, 0 GOLD=DIFF (zero unsound across the whole grid), 495 NOSIG.**
6 distinct onts recovered out of 36:

| Ont | Recovered by | Fastest wall | Base |
|---|---|---|---|
| 5107  | seqorder, combo, unitsfirst | 28 s  | timeout |
| 6246  | seqorder (137 s), tabrace (31 s) | 31 s | timeout |
| 6682  | seqorder | 24 s  | timeout |
| 10908 | seqorder | 197 s | timeout |
| 11016 | seqorder | 1 s   | timeout |
| 11291 | seqorder | 1 s   | timeout |

Per-arm recovery count: **seqorder = 6** (all of them), combo = 1, unitsfirst = 1,
tabrace = 1 — and every non-seqorder win is a subset of seqorder's. So the entire
portfolio collapses to a single lever: **`KM_SEQ_ORDER` recovers +6, gold-clean.**
The four new candidate flags (corecap/seedsubset/unitsfirst/earlyunsat) recover
nothing seqorder doesn't, and corecap/highcap/threads16/notrigskip recover 0.
`seqorder` also flips 2 base memouts into the converged set (base: 2 memout / 33
timeout → seqorder: 1 memout / 6 ok / 29 timeout), so total-order resolution both
bounds memory and converges faster on these. 11016/11291 finish in 1 s, meaning
base's per-context ordering was the entire problem there, not the instance size.

`KM_SEQ_ORDER` overturns the prior 6246 verdict (memory had it as a "genuine
timeout, not recoverable"; total-order resolution cracks it at 137 s, 31 s under
the cache-tableau race). 8737 reports STATUS=error in every arm — it is a giant
absent from the IBEX corpus (already `ok` in production via `elc`), not a failure.

Caveat before deploy: `KM_SEQ_ORDER` is known to OOM 5303, so it cannot go
default-on without a regression check on the 554 currently-passing onts. Next step
is a full-corpus sweep with `KM_SEQ_ORDER=1`; if it regresses passers it ships as a
router/race (run on the failing tail only, additive-by-construction like
`KM_ABSORB_PORTFOLIO`), otherwise default-on. Either way the +6 are sound (every
recovery is byte-identical to Konclude gold).

Why this replaced the shelved single-candidate work: the shared-successor parallel
strategy was **measurement-falsified** this session (`KM_CTXSPLIT` diagnostic,
commit `2674a11`). On 9663 the clause arena is only 6–8 % of memory; ~half is
per-context `head_indexes` across ~79k contexts, and single-thread central exceeds
20 GB at convergence (115 GB at 4M messages), so query parallelism only multiplies
per-context memory. The cluster is intrinsic-scale, not parallelizable-duplication.

### Absorption portfolio deployed + validated: sequential plain/absorbed (545 → 554, gold-clean)

`KM_ABSORB_PORTFOLIO` (in `owl_classify.py`, gated; enabled in the `kmpf` sbatch
alongside `KM_ABSORB=1` and the `ofn-absorb` frontend) runs the absorbed clause
set as the primary and, *sequentially* (one engine resident at a time, to respect
the 20 GB memcap), probes the plain clause set first for `KM_ABSORB_PROBE_S` (8 s)
to catch the absorption-cliff cases before committing to the absorbed run. A
concurrent race is ruled out by memory: legitimate absorbed runs already reach
~18 GB, so a second engine alongside blows the cap (the concurrent variant caused
7 memouts in cancelled sweep 6338).

Validation sweep **6524** (sequential portfolio) vs the 545 baseline:
**554 ok / 34 timeout / 2 memout**, gold table **554 agree / 0 unsound /
0 incomplete / 0 both** — fully gold-clean at corpus scale. **+10 recovered**
(1340, 2397, 3905, 4205, 6212, 7775, 12698, 14450, 16303, **16444**); **−1
regressed: ore_ont_6246**. Net **+9 (545 → 554)**.

6246 is the lone miss and the gap to the intended +11/−0: its plain run is
sub-second on an idle node but pathologically slow under contention, and the
8 s wall-clock probe landed on a busy node (node007), missed, took the absorbed
path, and blew to 18.6 GB / timeout. The probe is wall-clock so it is node-load
sensitive; the clean fix is a cheap static plain/absorbed router (decide from the
clause set, not from a timed race) rather than widening `KM_ABSORB_PROBE_S` (which
would delay the genuinely absorbed-only onts). The 2 memouts (10860, 15491) were
already not-ok in the baseline, not regressions. The portfolio is verdict-equal by
construction (absorption is equisatisfiable; whichever clause set answers first is
sound + complete).

### Frontend absorption: polarity-gated definitional clausification (+10 ORE coverage, 545 → 555)

`KM_ABSORB` (default off) extends the clausifier's polarity pre-pass to And/Or/Not
definers and emits only the definition direction the concept's polarity needs
(Plaisted-Greenbaum): `Q → C` only when C occurs positively, `C → Q` only when it
occurs negatively; unseen concepts (e.g. ABox assertions) keep both directions.
This drops, at the source, the unguarded excluded-middle disjunction `⊤ → Q ∨ A`
emitted for every reified negation that never appears on a subclass LHS (the
disjointness idiom `X ⊑ ¬A`), and turns an LHS disjunction into Horn rules.

Measured (`ofn`, on vs off): ore_ont_1340 104 → 0 disjunctive heads, 3905 106 → 0,
14450 106 → 0 (fully Horn); residual disjunctions are genuine RHS disjunctions and
are untouched (5303 38 → 37, so 5303 still times out — needs CB ordered resolution).

Validation sweep 6304 (`KM_ABSORB=1`, tableau race off) vs the 545 baseline:
**555 ok / 34 timeout / 1 memout**, gold table **0 unsound / 0 incomplete / 0 both**
(verdict-preserving confirmed at corpus scale — the synthetic definers are never
query targets, so their polarities are fixed by the ontology). 11 recoveries
(1340, 3905, 14450, 12698, 16303, **16444 the long-standing memout**, 2397, 4205,
6212, 7775, **8737 a giant**); 1 regression: **ore_ont_6246** goes 0.35 s/78 MB →
18.5 GB OOM/timeout — dropping the (PG-redundant) AND def directions on a DOLCE-
style covering+disjointness TBox perturbs the CB engine into a blow-up. Net +10.
Kept gated pending a safe deployment (absorbed/plain portfolio for +11/-0, or a
fix for the 6246 cliff) — see memory `project_km_absorption`.

### Tableau Tier-1 search heuristics: VSIDS + phase saving + Luby restarts (gated; not a coverage win)

`KM_TAB_VSIDS` / `KM_TAB_PHASE` / `KM_TAB_RESTART` (all default off) add CDCL-style
search control to the label-caching tableau's per-node DPLL. Pure decision-order /
redundancy, so no Lean re-cert; 2313 stays byte-identical under every combination.
Empirically they reduce distinct-seed count ~26 % and learn 5× more no-goods on
ore_ont_5303 but recover none of the 7 cache-eligible ORE timeouts: their wall is
the ∃-chain seed-space explosion (depth ~483, tens of thousands of incomparable
successor labels), not per-node propositional search. Kept as gated infrastructure;
the live-disjunction family needs disjunction reduction at the source (absorption,
above) or CB-side ordered resolution.

### CB-vs-tableau race hardened: provably zero-cost to the engine

`_race_cb_vs_tableau` now starts the engine first at full cores and spawns the
tableau lazily off the critical path (`KM_TAB_RACE_DELAY`, default 30 s) at
`nice 19`, with robust cancellation. An ontology the engine finishes within the
delay pays zero tableau cost. (A faithful same-node/same-binary A/B showed the
prior race was already net-neutral on the sweep, exonerating it as a regression
cause; the apparent 18-ont drop vs the stale 564 baseline was the Jun 12-13
correctness commits, not the race.)

### Direction C cache path: taint-aware learning + incremental pruning + pseudo-model caching (recovers ore_ont_2313)

Profiling the label-caching tableau (`KM_TAB_CACHE`) on the live-∀+⊔ family
(ore_ont_5303) pinned the wall: a deep ∃-chain (∃-depth 96 → 226+) of
*incomparable* node labels, where (a) no-good learning was disabled at exactly
those nodes and (b) blocking-SAT seeds were recomputed endlessly (cache stuck
~200 against 100k+ seed evaluations). Four sound, gated optimisations, validated
set-identical to the trusted `expand_inc` on 19 in-fragment ORE ontologies (0
wrong answers, 0 panics); commits `dbb474a`, `8231873`.

- **Taint-aware global learning at imposed nodes** (the key algorithmic lever).
  Learning was gated to `key.imposed.is_empty()`, which switches it off at every
  deep ∃-chain node (all carry imposed universals). Replaced with per-literal
  taint propagation in `close_dep`: a derived literal is tainted iff its
  derivation used an imposed (node-specific) clause, and a conflict is learned
  globally iff its whole derivation is untainted (provable from the TBox alone) —
  sound even under imposed constraints, which a coarse "any imposed fired" flag
  would wrongly forbid. `succ_conflict` and `first_disj` report taint;
  `local_search` threads it. On 5303 this breaks the hard-stop at ∃-depth 96 and
  the search advances to 144+ (no-goods 166 → 800+).

- **Pseudo-model caching of blocking-SAT verdicts.** The `used: bool` blocking
  flag became `block_level: usize` = the shallowest stack level any blocking in a
  subtree relied on (`blocked()` returns the deepest blocking ancestor for
  locality). (1) *Self-contained*: a subtree that only blocks on itself-or-deeper
  (`block_level >= own level`) is a self-contained finite cyclic model → cache
  unconditionally. (2) *Conditional*: a seed satisfiable only by blocking on an
  ancestor at level i is cached in a `cond` map valid while that ancestor is on
  the stack (purged on its pop) — every lookup then happens inside the ancestor's
  subtree, which is discarded if it fails. This caches the deep chain whose
  verdicts depend on a stable shallow ancestor, turning re-search into hits.

- **Incremental eager ∃-pruning** (`KM_TAB_EAGER`, default on). The eager
  successor check ran ~59 `build_succ` calls at every one of >1M DPLL steps. A
  step adding no *trigger* literal (one that can change an obligation or fire a
  universal) leaves obligations + successors unchanged, so the rescan is skipped.
  Plus a per-role uni index for `build_succ`. ~1.77x throughput on 5303.

- **Disjunct ordering** (`KM_TAB_ORD`, default 0 = program order). Floats vacuous
  `∀r.L` markers first (`ORD=1`). Measured: program order beats the shallow-model
  bias on 5303 (depth 363 vs 96); pure reordering, set-identical.

**Results (cache path, ord=0):** RECOVERS **ore_ont_2313** — a live-∀+⊔ family
timeout — finishing with 13967 subsumptions **byte-identical to the Konclude gold
signature**. Recovers ore_ont_2066 and ore_ont_5089 (previously timed out on the
cache path). 5303 runs ~3x faster (2.5M → 8M DPLL/280s, ∃-depth 483) but still
does not finish — the search accelerates and deepens yet oscillates rather than
converging (590k no-good hits); 1603, 12141 also still time out. The family is
not fully closed within budget: the residue is Konclude-grade search control, not
a missing soundness/completeness mechanism. Diagnostics: `KM_TAB_HB`,
dpll/depth/cache counters. `engine/py/tab_emit.py` emits a cached TInput from an
ontology for standalone cache-path tuning.

### Direction C: label-caching (global-caching) tableau (`KM_TAB_CACHE`, gated OFF)

A from-scratch rewrite of the tableau's non-careful (ALCH, no inverse / number /
nominals) path from a single global DFS over one shared completion graph into a
**label-keyed global-caching** decision procedure (Goré–Nguyen). The motivating
fact: in ALCH without inverse roles, a node's satisfiability depends ONLY on its
concept label, so a label proven (un)satisfiable stays so wherever it recurs — the
result caches across every node AND across every classify query. `expand_inc`'s
no-good learning could not exploit this because its no-goods were over node-
INSTANCE `(node, literal)` decisions (commit 16ec50b, measured insufficient).

Design (in `tableau.rs`, behind `KM_TAB_CACHE`; `build_cprog` falls back to the
complete `expand_inc` on any clause outside the recognised shapes, so soundness is
never at risk):
- **Two levels.** Level 1 (per node, transient, never cached): a propositional
  DPLL over the node's disjunctions. Level 2 (cached across nodes + queries): the
  satisfiability of each ∃-successor *seed* (its filler plus the universals
  propagated onto it), keyed by `CKey`.
- **`∃r.C ⊑ D` internalisation.** The someValuesFrom-on-LHS clauses
  `r(x,y) ∧ C(y) → D(x)` (82 of them in ore_ont_5303) become the disjunction
  `D ⊔ ∀r.¬C`, the universal disjunct represented as a synthetic marker concept
  carrying a `Uni` that pushes `¬C` to the node's r-successors when chosen.
- **Sound cycle handling without an SCC pass.** UNSAT seeds are always cached
  (sound: unsat under optimistic blocking ⇒ unsat in every context); a SAT verdict
  is cached only when its witness used no on-stack blocking (`used == false`) — a
  genuine finite model, sound to reuse anywhere.
- **Eager ∃-pruning** (every active obligation's successor checked at every DPLL
  level, sound because a partial node-set imposes fewer universals), **subset
  blocking** over the ancestor stack (sound GFP blocking for ALCH; Dickson's lemma
  bounds every ∃-chain), and a **semi-naive indexed `close()`** (Horn closure fires
  only clauses a newly-derived literal triggers; ~50× over the naive scan).

**Correctness validated:** 16 tableau unit tests pass through the cache path; on 5
real ALCH ORE ontologies (ore_ont_11949/9509/10309/13503/2485) the cached
classification is **set-identical** to the validated `expand_inc` output (132 / 81
/ 6 / 113 / 1 subsumptions). No regression to the default build (66 + 16 tests).

**Conflict-directed backjumping + label-based no-good learning (per-node DPLL).**
`local_search` now tracks, for every derived literal, the set of source concept
literals (seed-base + disjunction decisions) it depends on (`cdep`, maintained on a
trail so branches undo in place instead of cloning the working set). On a clash —
complementary pair, ⊥-clause, or an unsatisfiable ∃-successor — the conflict is
that source-literal reason. When asserting a disjunct `d` yields a conflict not
mentioning `d`, the choice was irrelevant and the search backjumps past the whole
disjunction. When every disjunct of a node fails, the resolved conflict
(`guard ∪ ⋃(conf_i \ {d_i})`) is learned as a no-good. Crucially these no-goods
range over CONCEPT LITERALS, not node instances, so one no-good prunes EVERY node
whose label contains it — the cross-node generalisation the earlier
`(node, literal)` learning (16ec50b) lacked. Learning is restricted to nodes with
no imposed clauses (where the derivation is node-independent), keeping it sound.
Validated: 16 tableau tests + the 5 real ALCH onts still set-identical to
`expand_inc` (a trail-undo bug that briefly produced unsound extra subsumptions on
ore_ont_9509/10309 was caught by the A/B and fixed — a clashing literal must be
trailed before the early return). Measured on ore_ont_5303: learning fires hard
(134 no-goods, ~9.7k prune hits) yet the ontology still times out — the search
backtracks through an exponential per-node region at ∃-depth ~226 that learning
prunes but does not eliminate, and smaller no-goods (`KM_TAB_LEARN_MAX=64`)
generalise better than large ones. The production-stack optimisations are in place
and sound but do not close this family within budget; this is the 5th technique to
reach the same wall.

**Recovery of the live-`∀ + ⊔` timeout family = 0** (honest negative result). On
ore_ont_5303 the checker builds a genuinely deep ∃-chain (>1000 successors) whose
labels are pairwise incomparable, so subset blocking rarely fires — the same
deep-model wall that already makes 5303 a timeout for `expand_inc` itself. The
per-node propositional search (120 disjunctions on the ⊤ node) is partly tamed by
eager pruning but the combined depth × width is not. On three other ALCH onts
(8937 / 1420 / 4856) the cached path is *slower* than `expand_inc` (deep-recursion
+ eager re-checking underperform the global DFS), so it is not a strict win and
stays gated OFF. The architecture is sound, validated, and the foundation for a
caching tableau; closing the gap to Konclude on this family needs the full
production-reasoner stack (dependency-directed backjumping + label-based learning
inside the per-node DPLL, smarter blocking), a multi-session engineering effort
rather than an algorithmic gap. This is the 4th approach (CB resolution, CB
splitting, tableau no-good learning, caching tableau) to hit the same wall on this
family; KM stays sound + complete on everything it finishes.

### Direction B: disjunction case-splitting (`KM_SPLIT`, increment 1, gated OFF)

The algorithmic lever for the live-`∀ + ⊔` timeout family (the largest timeout
group, out of parallelism's reach). Design: docs/DISJUNCTION-SPLITTING.md.
Instead of unrestricted resolution on incomparable disjunctions (the blow-up),
classify a query by semantic case splitting: branch on a derived fact-disjunction
`⊤ → l1(x) ∨ … ∨ lk(x)`, intersect the forced units over the open branches, and
close a branch on `⊥`. Each branch runs the tame ordered-resolution closure (a
per-thread `BRANCH_ORDERED` total order); the fallback runs the complete
(unordered) regime — ordered resolution alone is incomplete (the `KM_ORDERED_ALL`
verdict), so the two must be separated per-run, not by a process-global flag.

`classify_assume(query, assume)` runs a branch closure on a fresh engine
(isolation by construction) and reads `ClosureFacts` (forced units, split-point
disjunctions, `⊥`). A **conservative completeness guard** sets `foreign` →
fall back to the complete default engine whenever ANY context holds a
disjunction that is not a query-context body-empty concept-on-x fact-disjunction
(a conditional/role/equality disjunction, or a successor-context disjunction):
the total order could hide a forced unit there and the propositional-on-x driver
does not split it. So `KM_SPLIT` is **SOUND + COMPLETE on every ontology** — the
recovered fragment is the queries whose only nondeterminism is concept
disjunctions on `x` over Horn successors; everything else falls back.

Validation (66+16 tests; A/B vs the default engine):
- **14/14 byte-identical** on the finishable small onts (the guard only ever
  increases fallback, and fallback == default).
- **ore_ont_13383: identical**, where split fully classifies all 368 queries
  with **0 fallback** — the splitting itself (not the fallback) yields the
  correct complete answer on a real named-disjunction ontology.
- Honest correction: an earlier pre-fix run appeared to "solve" 5107 — that was
  the incomplete ordered *fallback* finishing fast with WRONG answers; with the
  per-run ordering fix 5107 correctly falls back to the complete engine.
- **Recovery on the disjunction timeout family: 0** (5107, 5303, 12698, 2313,
  …). Their hard nondeterminism is at the successor/conditional level, so they
  either fall back (→ complete-engine timeout) or the per-branch closure itself
  times out. Recovering them needs **structural splitting** — splitting
  disjunctions inside successor contexts and conditional disjunctions, with
  branch-scoped messaging — which is increment 2 (the genuinely multi-session,
  Lean-cert'd core). Direction A (ordered + selection + residue readout) layers
  on increment 2.

Increment 1 lands the correct splitting machinery and the soundness+completeness
guard; it is a no-op on the benchmark (falls back on the hard family) and stays
default OFF.

**Increment 2 — structural splitting (`d57e30d`).** Generalises the split from
query-root fact-disjunctions to disjunctions in ANY context, keyed by the
context's core (`branch_decisions: core → assumed disjunct facts`, seeded when a
context with that core is created; cores are deterministic given the decisions,
so the same successor context arises and gets the same seed across the
fresh-engine-per-branch runs). This is how a disjunct is assumed in a SUCCESSOR
context — the structure the live-`∀ + ⊔` family actually has (`A ⊑ ∀R.(C ⊔ D)`).
SOUNDNESS guard `chain_unique_contexts`: split only contexts reachable from a
root by single successor edges — the central strategy merges contexts by core,
so a context reached by ≥2 edges represents successors that could pick disjuncts
independently and a shared split would force them to agree (unsound). Everything
else (non-chain-unique, role/eq/non-central disjunctions) falls back.

Validation: 66+16 tests; **14/14 byte-identical** A/B; 13383 identical. SOUND.
Recovery on the timeout family: still **0**.

**Increment 3 — unit-propagation mode + the measured ceiling of lazy splitting
(`079da53`).** The Hyper resolvent builder, under the split regime, suppresses
resolvents that combine ≥2 derived disjunctions (the fact×fact multiplication),
so a branch's per-context clause population stays tame and exhaustive splitting
recovers the suppressed derivations. Sound (14/14 A/B; 13383 identical, full
split / 0 fallback). But it still recovers **0** of the timeout family, and the
node-rate + fixpoint instrumentation shows WHY — two failure modes, both fatal
to *lazy* splitting (saturate to fixpoint, THEN read + split disjunctions):
- 5303/5107/12698/10702: the per-query closure (saturate + inter-context
  message fixpoint) does not complete (<100 split nodes, no progress markers in
  40 s) — the blow-up is in computing the closure ITSELF, before any disjunction
  is available to split. Splitting on top of a closure that never finishes can't
  help.
- 2313: the split loop completes but all 1688 queries fall back (disjunctions in
  non-chain-unique contexts, which the soundness guard refuses to share-split) →
  the complete default engine then times out.

Conclusion: recovery requires splitting **interleaved** with saturation (decide
before the closure explodes) — an incremental decision trail with backtracking —
which fights the monotone append-only arena (retraction). That architecture is a
hypertableau, and the measurement **tilts the Direction C verdict toward a
dedicated/standalone tableau** rather than retrofitting interleaved retraction
into the CB engine. Increments 1–3 land the sound splitting machinery + the
unit-prop component a future interleaved version reuses; all gated `KM_SPLIT`
OFF, no benchmark change.

### Parallel-speed work: dynamic query scheduler (landed) + the parallelism ceiling

Speed push aimed at the timeout tail, learning from Konclude (whose two main
speed sources are aggressive parallelism + lazy tableau-with-caching for
nondeterminism). Findings, with a thread-scaling probe (job 6227, node005,
KM_THREADS ∈ {1,8,16}, 480 s / 220 GB) partitioning the failures by family:

**Lever 1 — dynamic work-stealing query scheduler (LANDED, `7bc8611`).**
The old parallel path split the named concepts into `threads` static
contiguous chunks, one fixed engine each; when the hard query concepts cluster
in the named ordering they land in one chunk and serialise the whole run
(measured on ore_ont_12141). Replaced with `threads` long-lived engines
draining a shared atomic cursor in guided-size grabs (large early for low
contention + intra-engine cross-query context sharing, shrinking to 1 at the
tail), so a finished worker steals the next. Pure scheduling change — each
engine is independent and a query's subsumers don't depend on co-classified
queries (run_for contract), so the partition-independent union is confluent:
no Lean re-cert. `KM_STATIC_SCHED` restores the old path for A/B. Validated:
66+16 cargo tests; subsumptions byte-identical across KM_THREADS=1 / dynamic-8
/ static-8 on 8 onts (16461, 16076, 7270, 7482, 10019, 8169, 13018, 9635).
Also split `apply_pred` into `pred_payload` (reads only the immutable sender)
+ `apply_pred_payload` (mutates only the target) — output-neutral, isolates
the one sender/target aliasing read as a precondition for a future parallel
message-apply phase.

**Lever 2 — intra-saturation parallelism: scoped, then shelved as low-ROI.**
Konclude parallelises the saturation itself; KM only parallelises *across
queries*. The missing piece (concurrent context saturation) is the only lever
for "one giant saturation" onts that query-parallelism can't split. But two
facts make it a poor investment under the real benchmark limits (240 s, 20 GB):

- *Cost:* the saturation core touches the shared arena + intern tables
  directly across ~70 sites (only 6 are the `&[ContextClause]` slice
  signatures; the rest are `saturate`/`add_clause`/`hyper`/`intern_cc`/
  `cc_find` reaching `self.cc_arena` directly). True parallel saturation means
  parameterising that whole core over an arena+intern abstraction (each worker
  sees committed-global ++ its-own-new clauses) or a locked concurrent context
  graph — a multi-session, Lean-adjacent refactor needing iterative validation.
- *Payoff (probe 6227 + memory facts):* the speed-recoverable set is ~1 ont.
  - 12141 + the disjunction family: timeout at 1/8/16 threads, and 8/16
    threads **explode to ~204 GB** — parallelism-resistant *and*
    memory-explosive; needs the algorithmic lever (ordered resolution /
    tableau / BCP), not threads.
  - 16444 (59 GB) and 9724/GALEN (27 GB): both **over the 20 GB memcap**, so
    they are memouts regardless of speed.
  - 16303: th=1 and th=16 both timeout at an **identical 4.93 GB peak** — the
    textbook family-B signature (query-parallelism completely inert; one giant
    saturation). The lone genuine intra-saturation target: fits the memcap but
    needs ~8–10× scaling to clear 240 s.

  Conclusion: bank Lever 1; **shelve Lever 2** (multi-session core refactor,
  memory-neutral, reaches ~1 ont); the productive next lever is the
  disjunction family's algorithmic fix (the largest timeout group, provably
  out of parallelism's reach).

### Sweep 6016: the first fully clean correctness table (datatypes included)

Full sweep with the datatype layer + chain-domain default + Phase-2 engine
(binaries `ofn-dt` / `kobayashi-marust-p2`): **545 ok / 45 timeout /
1 memout; vs Konclude gold 545 agree / 0 incomplete / 0 unsound /
0 both-disagree** — every completed ontology byte-equal to gold, with no
exclusions (ore_ont_6999's datatype gap closed). Zero status regressions vs
sweep 5976 and two recoveries (ore_ont_2397, ore_ont_8737 timeout → ok), so
the new clauses cost nothing net. The 3524 giant's stdout-runaway recurred
mid-sweep and is now fixed at the root (`KM_EMIT_CLAUSES` gating below).

### Nominal-mode r-Pred announcement guard (10594 livelock fix)

The Phase-2 per-source r-Pred path let body-empty ground clauses pass the
body-discharge check vacuously, spraying every ground fact to every context
with a root edge (ore_ont_10594, ~1900 individuals: 3.5M+ Pred messages,
ok → timeout under `KM_NOMINALS`). Restored the announcement guard (an edge
per mentioned individual) with additional nominals (id ≥ `nom_base`) exempt —
they are exactly what Nom conclusions carry and what no context can have
announced. 10594: timeout → 192 s, now faster than the Phase-1 engine on the
same host with identical published output.

### Datatypes: data-property axioms + a concrete-domain oracle

Closes the datatype gap (the last incomplete-vs-gold ontology): ore_ont_6999
is now byte-equal to gold — `Distortion_Type_Affine ⊑ =2 affc2` with
`Functional(affc2)` is correctly unsatisfiable. Two layers, both frontend
(no calculus change, no Lean re-cert needed):

1. **Axiom translation** (`parse.rs`; previously every `Data*` axiom was
   dropped): functionality → role functionality, sub/equivalent/disjoint
   data properties → the role counterparts, ranges → `∀p.__dt__D`,
   `DatatypeDefinition` → concept equivalence. Unqualified data cardinalities
   now count ALL successors (`⊤` filler — the old `__dt__val` filler made
   `≤ n` blind to `DataHasValue` successors). Complex ranges are keyed by
   canonical text (one shared `__dt__opaque` could invent subsumptions
   between different facet restrictions) and typed literals are re-glued
   with their `^^datatype` / `@lang` suffix (the tokeniser splits them off,
   which collapsed same-lexical different-type values).
2. **Pairwise oracle** (`frontend/datatypes.rs`): for the `__dt__` concepts
   occurring in the clause set, decide — per the OWL 2 datatype map — value
   membership, value (in)equality (exact rationals across the decimal tower
   and dyadic float/double, strings, booleans), range subsumption and
   disjointness (integer-tower bounds, string-family tower, partition
   disjointness, interval separation), and finite covers (boolean, DataOneOf,
   small integer intervals): `__dt__D(x) → ⋁ __dt__val__vᵢ(x)`, which with
   value disjointness gives finite-range counting through the engine's
   ordinary equality reasoning. Every relation is emitted as a plain concept
   clause; unknown decisions emit nothing (the old sound abstraction).
   `KM_NO_DATATYPES` disables the oracle pass for A/B.

82 cargo tests pass (5 new oracle tests). Full-corpus validation sweep
pending; built and validated on unimatrix while ws was unreachable.

### Nominals Phase 2+3: Join, r-Succ (*), the Nom rule, and Lean certification

Completes the ALCHOIQ calculus implementation behind `KM_NOMINALS` (Table 3 of
arXiv:1805.01396; design + status in `docs/NOMINALS-CB.md`):

- **Nom** (additional nominals): in the ground context, a hyper-match with
  `σ(x) = o` whose head a-equalities instantiate to `y ≈ y` / `y ≈ f(o')` no
  longer drops them as tautologies (the exact O+I+Q incompleteness) but
  replaces them with `⋁_{k} y ≈ o'_k` over fresh interned additional nominals.
  The disjunction width is `K + K''` (`K + 1` = max neighbour-variable index,
  `K''` = distinct pinned `f(o')` terms): the certified covering bound is the
  sum, and the paper's bare-`K` statement is too narrow whenever `K'' > K`.
  Budgeted (`KM_NOM_BUDGET`, default 4096) with an explicit incompleteness
  warning on exhaustion. Two enabling fixes: the ground context's Hyper now
  considers the side clause at non-side body positions (given-clause
  semantics — provably redundant elsewhere, the Nom trigger here), and the
  symmetric-group strict pruning admits the equal-`y` assignment there.
- **Join**: in-context resolution on ground atoms (cases 1+2 via new
  ground-body/bridge indexes and a `pred_local` refire on ground maximal
  heads; case 3 = provider over `x` + an `x ≈ o` bridge, fired from all three
  arrival orders).
- **r-Succ condition (*)**: pushes are blocked when a subsuming-modulo-merge
  clause shows the element may itself be a nominal (defer to equality
  reasoning).
- **r-Pred pipeline**: per-atom multi-edge discharge (different `A_i` over
  different individual-labelled edges of one source), verbatim `C_i` copies,
  and no edge requirement for head individuals — the old head filter made
  every Nom conclusion undeliverable.
- **Lean (Phase 3)**: `lean/ContextCalculus/Nominals.lean` (sorry-free)
  certifies soundness of all four rules and the grounded substitutions;
  `nom_cover`/`nom_sound` prove the covering bound and the
  conservative-extension soundness of Nom (the interpretation of the fresh
  constants is constructed).
- `owl_classify._run_engine`: the stdin writer thread raced
  `communicate()`'s flush on fast engine exits (`ValueError: I/O operation on
  closed file`); `communicate(input=…)` now owns the write.

Validation: 61 + 16 cargo tests (4 new engine-level tests incl. the paper's
Example 3 and a no-counting negative control); all six pipeline probes match
HermiT (`nom1`, `nom2`, `nom_dl8`, `nom_neg1`, `nom_unsat`,
`nom_oiq_funct` — the last is Example 3 as OWL, the first KM result that
*requires* additional nominals). Inert without individuals: every new code
path is gated on the ground context / ground atoms, and without `KM_NOMINALS`
the reasoner drops individual clauses, so SRIQ-fragment output is unchanged.
60-ontology corpus A/B with this binary pending.

### Chain-domain recognition validated corpus-wide; now DEFAULT ON

Full sweep 5976 (`KM_CHAIN_DOMAIN=1`, all 591 gold-comparable ontologies):
**543 ok / 46 timeout / 2 memout; vs Konclude gold 542 agree / 0 unsound /
1 incomplete / 0 both-disagree.** The single incomplete is `ore_ont_6999`,
whose one missing subsumption (`Distortion_Type_Affine`) is the known
*datatype* gap (identical in the old config) — within SROIQ-minus-datatypes
the corpus is now **0 unsound, 0 incomplete vs gold**, the first fully clean
correctness table. `ore_ont_11745` confirmed fixed at full scale (ok,
unsat=1592, gold-equal).

Landing: the pass is now default-on (`KM_NO_CHAIN_DOMAIN` opts out for A/B
debugging), per the completeness mandate and the disjunction-ordering
precedent. Cost vs the 5941 baseline: `ore_ont_2313` and `ore_ont_8737`
(chain-heavy; 8737 ran ~206 s before) go ok → timeout — honest resource
limits, not silent approximation.

### Frontend: role-chain recognition for pure-domain consumers (`KM_CHAIN_DOMAIN`)

Recovers `ore_ont_11745`, the last unsound-vs-gold ontology: with the flag,
full 11745 is byte-identical to Konclude gold (438277 subsumptions, 1592
unsatisfiable classes, `GO_0008046` correctly unsatisfiable). It was a genuine
unsat under-detection (HermiT-confirmed; an 18-axiom witness reduced from a
STAR module), not the parallel-pipeline artifact earlier assumed.

Root cause: `chain_clauses` / `transitivity_clauses` run inside `augment`
(frontend pass 1) and recognise a chain `R∘S⊑T` only when a TBox consumer
carries a concept on the chain target. A *pure-domain* consumer
`T(x,y) → D(x)` (from `ObjectPropertyDomain(T, D)`) has no such concept and is
added only in pass 2, so the chain feeding a domain restriction was never
recognised. In 11745, `GO_0008046` is a molecular_function (a `SubClassOf`
chain) and, via a transitive `part_of` chain plus `part_of∘ricdo⊑ridpo` with
`domain(ridpo) = biological_process`, also a biological_process; the two are
disjoint, so the class is unsatisfiable. KM reached the chain filler
(`__trans__part_of__GO_0048856`) but never composed it with the domain
restriction, so it missed the clash and emitted the class's ordinary
superclasses (scored as unsound, though KM never derived anything false).

Fix (gated by `KM_CHAIN_DOMAIN` while validated corpus-wide; reordering the
passes is blocked by the `reg.short` name-assignment byte-identity invariant):
`augment` now also returns the detected `ChainInfo`, and after
`domain_range_clauses` are built, `domain_consumer_chain_clauses` emits the
missing recognitions for pure-domain consumers of chain targets — the
`__chain__S__` recognition (any `S`-edge) plus the `R`-composition, and when
`R` is transitive the full `__trans__` up-propagation so the chain composes
across `part_of` hops. Additive and sound (only fresh recognition clauses;
standard chain unfolding, no calculus change, no Lean re-cert): off-flag output
is byte-identical. Reproducers:
`oracle/ontologies/{11745_unsat_core,chain_domain_propagation}.ofn`. Tests:
`domain_consumer_chain_recognition`, `domain_consumer_transitive_chain_recognition`.

### Nominals: grounded CB reasoning (`KM_NOMINALS`, default off) — Phases 0+1

KM's prior nominal handling replaced `{o}` with a fresh concept proxy
`__nom__o` and lifted unconditional ABox facts; sound but incomplete whenever
the singleton property matters. Minimal witness (HermiT-confirmed,
`oracle/ontologies/nom_merge_sub.ofn`): `A ⊑ ∃r.({o}⊓B)`, `A ⊑ ∃r.({o}⊓C)`,
`B⊓C ⊑ E`, `∃r.E ⊑ G` entails `A ⊑ G`, which the proxy misses (the two
successors stay distinct). 60 of the 592 benchmarked ORE ontologies use
`ObjectOneOf`/`ObjectHasValue`.

Implements the ALCHOIQ consequence-based calculus (Tena Cucala, Cuenca Grau,
Horrocks, IJCAI 2018; arXiv:1805.01396) behind `KM_NOMINALS`, mapped in
`docs/NOMINALS-CB.md`. Phase 0 (frontend): under the flag, `augment` emits the
DL7/DL8 defining clauses `⊤ → __nom__o(o)` and `__nom__o(x) → x ≈ o` plus the
ground ABox clauses, and fences ontologies with individuals off the elc path;
off-flag the output is byte-identical. Phase 1 (engine):

- Term space re-encoded to `z < y < x < o_k < f(x) < f(o)` (individuals below
  the Skolem terms, `f(o)` composites packed positionally), a pure id-space
  relabeling validated byte-identical vs the prior binary on `ore_ont_16461`
  and the cardinality probes. The order satisfies Def 3 of the calculus given
  the existing predecessor-trigger-bottom refinement.
- One ground (nominal root) context `v_r` is the only place Hyper grounds the
  central variable (`σ(x) ∈ Σo`); it is created eagerly when ground facts
  exist and holds all ground inference. Ground ontology facts seed `v_r`
  fully and every other context on demand (first clause mentioning the
  individual).
- The Su^r forms (`B(o)`, `S(x,o)`, `S(o,x)`) push their y-form to `v_r` over
  individual-labelled edges (r-Succ); `v_r`'s ground conclusions flow back
  through the existing Pred machinery (r-Pred), with an edge-coverage
  discipline that kept a naive version from livelocking. `x ≈ o` crosses an
  `f` edge as `f(x) ≈ o`, which the receiver's Eq rule rewrites into ground
  atoms. A `v_r` empty clause is global inconsistency.

All five witness probes pass (HermiT-checked): `nom_merge_sub` and the DL8
merge derive the expected subsumption, the two-distinct-nominals negative
stays underivable, and `{o}⊑B, {o}⊑C, B⊓C⊑⊥` is reported inconsistent.
Off-flag and SRIQ-path output are unchanged (every new branch is unreachable
without individuals in the clause set). Known cost on the flagged path:
ABox-heavy ontologies slow down (`ore_ont_10594` 0.6 s → 85 s) — perf and the
remaining rules (Join, the r-Succ side condition, Nom) plus Lean
re-certification are future phases before the flag can default on.

### Frontend: AtMost recognition (`≤n r.F` on the LHS could never fire)

The mirror of the AtLeast gap below, found by inspection: the AtMost
clausification emitted only the constraint direction, so nothing could ever
derive the reified Q and `≤n r.F ⊑ G` was silently incomplete (not
exercised by ORE gold so far). Fix: excluded-middle recognition — fresh NQ
with `⊤ → Q ∨ NQ`, `Q ⊓ NQ ⊑ ⊥`, and NQ ⊑ ≥(n+1) r.F (n+1 witnesses with
pairwise inequalities); a context that refutes the witnesses derives Q.
Polarity-gated (the `⊤ → Q ∨ NQ` split fires in every context): emitted for
negative or unseen occurrences, skipped only when the pre-pass proves the
occurrence positive-only. Probes: `∀r.⊥ ⊢ ≤1 r.J` (vacuous) and
functionality ⊢ `≤2 r.J` (merge-derived) both derive G; negative probes
stay sound. In-corpus clause changes are confined to current timeouts
(10702, 1194, 14817). Test:
`frontend::normalise::tests::atmost_recognition_polarity_gated`.

### Frontend: ≥n recognition clause for n ≥ 2 (the 16461 min-cardinality gap)

The clausifier (`normalise.rs`, `Concept::AtLeast`) emitted the recognition
direction of a reified `Q ≡ ≥n r.F` only for n == 1 (the plain ∃-recognition
clause). For n ≥ 2 no clause could ever derive Q, so a qualified
min-cardinality on the LHS of a subsumption never fired: ore_ont_16461's
single missing subsumption, reproduced in a 21-clause probe (`P ⊑ ∃r.J1,
P ⊑ ∃r.J2, J1⊑J, J2⊑J, Disjoint(J1,J2), ≥2 r.J ⊑ G ⊬ P⊑G`).

Fix: emit the standard contrapositive clausification `¬Q ⊑ ≤(n-1) r.F`, i.e.
`r(x,y0) ∧ F(y0) ∧ ... ∧ r(x,y_{n-1}) ∧ F(y_{n-1}) → Q(x) ∨ ⋁_{i<j} yi≈yj` —
the same clause shape the AtMost branch already produces and the engine's
Hyper + Eq/Factor machinery already reasons over (multi-neighbour-variable
bodies, equality heads). No calculus change, no Lean re-cert: only the input
clause set is completed; the emitted clause is the definitional-extension
direction of the reified Q and is logically equivalent to `≥n r.F ⊑ Q`.
(n == 0 falls out correctly as `→ Q(x)`, since `≥0 r.F ≡ ⊤`.)

The probe now derives P ⊑ G. Frontend output is byte-identical on
ontologies without min/exact-cardinality ≥ 2 (checked on 10); 27 corpus
ontologies are affected and were re-validated against gold. New tests:
`reasoner::tests::min_cardinality_recognition` (engine-level, the probe) and
`frontend::normalise::tests::atleast_two_recognition_clause`.

**Polarity gating**: the recognition clause is pure cost when the `≥n`
occurs only positively (RHS — intro direction suffices), and on
existential-rich ontologies it feeds the live-disjunction blow-up (a single
unqualified `≥5 setting-for` recognition clause on ore_ont_15672/DOLCE
doubles the pipeline wall time: the resolvent residues create new Hyper
providers, mutually incomparable under subsumption). The pre-pass
(`mark_polarity`) now records each AtLeast's polarities; recognition is
emitted unless the concept is PROVEN positive-only (negative or unseen ⇒
emit, so coverage gaps keep the complete behaviour). Even gated,
ore_ont_15672's genuinely-negative `≥5` (an EquivalentClasses conjunct)
keeps its recognition clause and the ontology joins the live-disjunction
timeout family — recovering it is the ordered-resolution workstream, not a
cardinality issue. Test:
`frontend::normalise::tests::atleast_recognition_polarity_gated`.

### Engine: symmetric-group pruning in the Hyper join

The recognition/at-most clause shape is fully symmetric in its neighbour
variables, so the backtracking join enumerated every permutation (and every
equal-term repeat) of each candidate combination — `k^n` assignments where
`C(k,n)` are distinct, ruinous for n ≥ 4. `OntologyClause` now precomputes
its exchange-invariant variable groups (pairwise swap-invariance,
union-find; transpositions of a connected component generate its full
symmetric group), flagging groups whose head carries an equality for every
pair. The join prunes assignments whose group terms are not sorted (strictly
sorted for flagged groups: an equal-term assignment makes some head equality
`t≈t`, a tautology `build_hyper_resolvent` drops). Side-clause variables are
exempt (the side clause is pinned to its body position and not
interchangeable with worked-off candidates). Output-preserving: every pruned
assignment is a permutation of a kept one and yields the identical canonical
resolvent (heads/bodies are sorted and deduped; `Lit::eq` normalises
orientation), so the derived set is unchanged — no Lean re-cert.

### Engine: central-strategy successor cores must hold facts only

With the recognition clause in place, n = 2 worked but n ≥ 3 still stalled
(probe: P with 3 pairwise-disjoint r-successors, `≥3 r.J ⊑ G` ⊬ P ⊑ G; the
real ore_ont_16461 needs n = 4). Trace: P's context correctly derives
`⊤ → A2(f1) | A3(f1) | Q` by paramodulation, but the central strategy had
pushed the disjunctively derived triggers A2(f1), A3(f1) into the successor
CORE alongside the fact A1(f1). The `[A1,A2,A3]`-core context derives ⊥, and
apply_pred conditions the push-back on the whole core — a clause
`A1(f1) ∧ A2(f1) ∧ A3(f1) → ⊥` that would have to cut TWO literals of the
same disjunction at once, which no resolution step can do. The per-disjunct
refutations (`A1 ∧ A2 → ⊥`, `A1 ∧ A3 → ⊥`) were unavailable because the
hypothesis clauses `p → p` added by apply_succ were subsumed by the
over-large core's `⊤ → p`. The legacy non-central strategy (empty cores,
pure hypotheses) does not have the bug — KM_NO_CENTRAL=1 derives G on every
probe, confirming the diagnosis.

Fix: a successor core now contains only the σ-image of FACT triggers (unit
clauses `⊤ → p(f)` in the predecessor); disjunctively or conditionally
derived triggers still travel as Succ messages (edge bookkeeping +
hypothesis `p → p` at the target) but stay out of the core, so their
consequences return conditioned on `p` alone and each disjunct is cut
individually. Context identity (`central_successor_for_core`) keys on the
fact core; hypothesis-only trigger growth keeps the same target and sends
just the new triggers. No calculus-rule change (Hyper/Pred/Succ/Eq schemata
untouched, no Lean re-cert, same category as the central-strategy landing):
cores shrink, so the context invariant (core ∧ body → head entailed) is
preserved, and every previously derived consequence is still derived — the
fact-trigger cores reproduce the old behaviour exactly on ontologies where
all succ triggers are facts (the common case: existential successors).
New test: `reasoner::tests::min_cardinality_recognition_three_witnesses`.
With both fixes the full ore_ont_16461 derives the gold-only subsumption
`Patient1 ⊑ Systemic_JIA_Patient` (≥4 hasAffectedJoint.Joint over 5
pairwise-disjoint joint successors).

### Engine: clause interning (Pred pipeline + global arena) — peak RSS −77%

KM_MEMSTATS accounting (new, diagnostics-only) on ore_ont_9944 at fixpoint
showed each derived clause stored 5+ times across the engine: per-context
`neighbor_pred` copies of back-substituted pred clauses (11.4M instances,
2.06 GB — only 388k distinct, 29x duplication), a full clause copy per
(edge, clause) in `pushed_pred`, full copies in `pred_pool`/`succ_pool` and
`clause_keys`, the `max_head` duplicate, and `Msg::Pred` carrying a cloned
neighbour core + clause per queued message (13.8M messages). On top of that,
the seeded shared closure was cloned into every context (8009 root contexts).

Two interning stages, both representation/sharing only (the derived clause
set is unchanged, so no Lean re-certification — skipping a duplicate Pred
arrival only skips re-deriving clauses `add_clause` would dedup anyway):

1. **Pred pipeline** (`228067f`): engine-level `pred_interned` table;
   contexts hold u32 ids and `neighbor_pred_seen` dedups duplicate arrivals
   (real, from a successor's pre-/post-growth contexts under the central
   strategy). `pushed_pred` keys by (edge → `pred_pool` index). `Msg::Pred`
   carries `{to, from, edge_label, pool_idx}` (24 B, no heap); the sender's
   pool entry and core are immutable, so apply-time resolution reads exactly
   the send-time snapshot. 9944: 8.50 → 4.99 GB, wall 2:58 → 2:26.

2. **Global clause arena**: `cc_arena: [Vec<ContextClause>; 2]`, content-
   interned, split by ordering domain (root / non-root — the same
   (body, head) caches a different `max_head` under the two orderings, so
   the domains are never crossed). `worked_off`/`todo`/pools become Vec of
   u32 arena ids; `clause_keys` becomes HashSet of the id (the id IS the
   content key); head indexes store ids; the shared closures seed ids
   instead of cloning clauses per context. 6.08M worked-off instances
   collapse to 193k distinct (31x). 9944: 8.50 → **1.99 GB peak (−77%)**,
   wall 2:58 → **1:56 (−35%)**, output identical (315,940 subsumptions,
   exact set match). 49+16 cargo tests pass.

This is the lever for the 9724 (GALEN) memout, which churns >82 GB
unconverged on the old representation.

### Engine: complete disjunctive case analysis (same-term literals incomparable)

The context literal ordering (`calc.rs pred_lteq`) imposed a total order on
same-term concept literals (iri id + internal-definer-low), applying the
mutually-incomparable refinement only in root contexts. That total order is
incomplete for disjunctive consequence finding: once a disjunct stops being
maximal it is never resolved, so a head disjunction never fully case-splits.
Minimal probe (CB engine): `A ⊑ ∃R.(C⊔D), C⊑E, D⊑E, ∃R.E⊑G ⊬ A⊑G` (the engine
derives `C(f)|Q_2(x)` and stalls). This is the root cause of the incomplete
disjunctive ORE ontologies (12698's `∃`-filler disjunction + transitive role).

Fix: concept literals on the same term are mutually incomparable in every
context, so Hyper fires on every disjunct and the case split completes. This
matches the Lean completeness proof, which models Hyper as resolution on an
arbitrary atom (`CompletenessProp.lean`) with no ordering assumption -- the total
order was never part of the certified calculus. Sound by construction (ordered
resolution is sound for any selection). Validated on probes + ORE 2313 / 12698
minimal cores; 65 tests green; Horn (single-head) reasoning is unaffected.

TRADEOFF (sweep 5814): genuinely-disjunctive ontologies now explore all branches,
which is heavy (12698 ~16-19 GB). About 10 ontologies regress ok→timeout/memout.
This is fundamental -- completeness on disjunctive inputs requires full case
analysis -- and is recoverable only by performance work (stronger redundancy on
disjunctive clauses, or decoupling Hyper-maximality from Succ-trigger selection),
not by weakening the ordering. `KM_DUMP_WO=1` dumps every context's worked-off
clauses (debug, env-gated). `KM_NO_PRUNE=1` disables inert inverse/role-bridge
pruning (diagnostic; pruning is sound -- disabling it does not recover the
remaining inverse-role / GALEN incompleteness, which is a separate engine gap).

### Frontend: handle EquivalentObjectProperties (was silently dropped)

`EquivalentObjectProperties(R1 … Rn)` had no parse arm in either the AST path
(`parse.rs`) or the streaming RBox builder (`rbox.rs` `rbox_node`), so role
equivalences were dropped. Every inference that bridges two equivalent roles was
lost. Minimal witness extracted from ORE `ore_ont_2313` (`ddmin`, oracle =
HermiT entails `C ⊑ D`), a 3-axiom core:

```
SubClassOf(TO_0000059, ObjectSomeValuesFrom(BFO_0000050, TO_0000056))
EquivalentObjectProperties(BFO_0000050, PPIO_0000091)
ObjectPropertyDomain(PPIO_0000091, PPIO_0000069)
⟹ TO_0000059 ⊑ PPIO_0000069
```

The existential uses `BFO_0000050`; the domain is stated on the equivalent
`PPIO_0000091`. Without the equivalence the two roles never connect, so the
domain never fires on the existential's Skolem edge. `2313` was missing 88 such
subsumptions.

Fix: expand `R1 ≡ … ≡ Rn` into pairwise both-direction inclusions. `parse.rs`
emits the AST `RoleInclusion`s (so `normalise` produces the subrole clauses that
reach the reasoner); `rbox_node` emits matching `Subrole` records (routing /
relevance / domain-range). Any inverse member fences the axiom to the CB engine.
`2313` now matches gold exactly (88 missing → 0, 0 extra). 57 ORE onts contain
the axiom; the change is sound (role equivalence = mutual inclusion) and can only
recover entailed subsumptions. Tests green.

### Correctness tail: sound datatype-ABox precheck + complex-domain clausification

Resolved the four "unsound vs gold" ontologies and recovered one incomplete one.
The headline result is that KM was never unsound on the four flagged ontologies:
they are all genuinely **inconsistent**, and the gold signatures were wrong.

**Proof the gold was wrong.** Delta-debugging (`ddmin` over the axioms, oracle =
HermiT-reports-inconsistent) reduced each of `8941` / `13912` / `15516` / `2669`
to a 2–8 axiom inconsistent core. Running those cores through HermiT *and*
Konclude directly, both reasoners report inconsistent (Konclude prints
`EquivalentClasses(Thing Nothing ...)`). The recorded gold said "consistent"
because of two benchmark-harness bugs, both fixed:
- `ore_canon.py` canonicalised Konclude's `Thing ≡ Nothing` (its encoding of an
  inconsistent ontology) into "consistent with N unsatisfiable classes". It now
  maps `owl:Thing` in the `owl:Nothing` SCC — and any `consistent=false` — to the
  uniform empty inconsistent signature.
- `ore_runone.py` recorded Konclude's exit-0-with-empty-output on a SWRL
  `DLSafeRule` parse failure (`15516` / `2669`) as a bogus "consistent". It now
  flags Konclude "All parsers failed" as `error` (excluded from comparison).
The gold was regenerated for every affected ontology.

**KM side (`frontend/data_abox.rs`).** The CB engine drops the ABox, so these
asserted-data clashes never reached saturation. A new sound precheck detects:
- range-vs-literal clash: a `DataPropertyAssertion` whose literal value-space is
  disjoint from a (possibly sub-property-inherited) `DataPropertyRange`
  (`8941`: `xsd:string` range carrying a language-tagged literal — an
  `rdf:PlainLiteral`, never in the string value space);
- functional-data clash: `FunctionalDataProperty` with two provably-distinct
  values on one individual;
- an at-most-1-driven ground individual merge (closing role assertions under
  symmetry / inverse / sub-roles and domain/range typing) feeding a
  `DataMax`/functional clash or a `DifferentIndividuals` violation (`13912`:
  symmetric `Owner` + domain `Photo` + `Photo ⊑ =1 Owner` merges two photos,
  then `Photo ⊑ ≤1 url` clashes their distinct urls);
plus an asserted-member-of-unsatisfiable-class rule (`asserted_classes` on the
ofn meta; `owl_classify` makes the ontology inconsistent when a class proved
unsatisfiable has a provable asserted member). Every clash is an OWL 2
entailment; caps degrade to "not detected" (incomplete, never unsound).

**Incompleteness.** `parse.rs` now clausifies a COMPLEX
`ObjectPropertyDomain`/`Range` on a named role as the equivalent class axiom
(`∃R.⊤ ⊑ C` / `⊤ ⊑ ∀R.C`) instead of dropping it as `complex-domain`. The
named-class case stays on the rbox path (byte-identical). Recovers `ore_ont_4827`
exactly (the olia `domain(hasCase) = Adjective ⊔ ...` chain via `∃hasCase.Self`).

**Validation.** 19 new `data_abox` unit tests; full suite green. Whole-corpus
frontend differential: clause + meta output byte-identical on every ontology
except those newly flagged inconsistent; all newly-inconsistent ontologies
confirmed inconsistent by HermiT/Konclude (zero false positives). Remaining
incomplete onts are deeper engine gaps: `16461` (1 nominal subsumption, CB drops
individuals); `2313` / `12698` / `9944` (existential-superclass `∃R.C`
propagation).

### EL completion: clone-free hot loop (recovers giant ore_ont_8737)

The `elcomplete` worklist saturation cloned a state collection on every
Sub/Edge item to satisfy the borrow checker. On the transitive ORE giants this
dominated: transitivity is encoded as NF4, so the existential rules fire on
huge predecessor and superclass sets, and each firing paid a full-set clone.
Three changes remove the per-item allocations:

- `in_edges` is `Vec<Vec<(parent,role)>>` instead of `Vec<HashSet<...>>` — a
  pair is appended only in the `edges[parent].insert` success branch, so
  duplicates were already impossible and the set bought nothing. The Sub-side
  NF4 rule and ⊥-edge back-propagation iterate it by index (new entries pushed
  during the loop are picked up by the growing bound), clone-free.
- The Edge-side NF4 rule collects conclusions into a reused `nf4_buf` during a
  read-only scan of `sub_super[d]`, then applies them (replaces a full-superset
  clone per edge).
- NF4/NF7 rule blocks are skipped outright when their indexes are empty.

Schedule-only change: the same conclusions are derived, possibly in a different
order; the fixpoint is unchanged (saturation is monotone + confluent), so no
Lean re-cert. Validated: 53 unit tests; gold-identical signatures on controls
16744 / 10016 / 1559 / 13482.

Effect: `ore_ont_8737` classify 252 → 221 s standalone; in the benchmark
pipeline it went **timeout → ok at 205.7 s** (9.5 GB peak), signature
byte-identical to the Konclude gold. `ore_ont_16744` pipeline 167 → 151 s.

**Full-sweep confirmation (job 5690): 564 ok / 26 timeout / 1 memout**, vs
gold 554 agree / 6 incomplete / 4 unsound / 0 both-disagree — agree +1 (the
recovered 8737), no regression anywhere. All three 3M-axiom giants (8737,
15059, 16744) now classify within budget via the EL path.

### EL fast path: optional canonical-model completeness certificate (`elc`)

`elcomplete::to_nf` no longer aborts on the first non-EL clause: it collects the
non-EL clauses into a *residual* and still saturates the EL subset. With
`KM_ELC_CERT=1`, `classify` then checks every residual clause against the
saturated **canonical model** (domain = satisfiable concept nodes; `x_C ∈ D^I`
iff `C ⊑ D` derived; `(x_C,x_D) ∈ R^I` iff edge `(C,R,D)` derived). If all hold,
`I ⊨ O` for the full ontology, so the EL classification is exact (sound AND
complete) for subsumption, unsatisfiability, and consistency; any failure (or a
work-budget overrun) returns `None` and the caller falls back to the CB engine.
Never an approximation. 7 unit tests; the certificate logic is a calculus-logic
addition and needs Lean certification of the canonical-model lemma (deferred).

**Default OFF.** On ORE 2015 every non-EL residual is a live covering
disjunction (`⊤ → A ⊔ B`), a non-inert inverse bridge, or multi-successor
functionality — none of which the canonical EL model satisfies — so the
certificate never passes there (verified: fails at residual clause 0 on
4205/6212/15803/7127/7246/11311), and attempting it would saturate the large EL
subset before failing, stealing time from the CB fallback. With the flag off,
routing is byte-identical to before (`to_nf` returns a non-empty residual ⇒
`classify` returns `None` ⇒ same exit-3 fallback). The capability is for
near-EL ontologies whose non-EL part IS model-satisfiable.

Also in `elc.rs`: read stdin as raw bytes + `serde_json::from_slice` (skips the
whole-buffer UTF-8 validation and a second allocation; lower peak memory), and
`KM_ELC_TIMING=1` per-stage timing. The timing showed the ORE giant
`ore_ont_8737` is **saturation-bound** (read 0.5 s, parse 8 s, classify 252 s,
serialise 2.8 s) — its 240 s timeout is the EL completion itself, not I/O, so it
needs a faster (parallel, ELK-style) completion, not an I/O fix. `ore_ont_16744`
classify is 83 s.

Goal: close the remaining ORE 2015 coverage gap to Konclude (was 551/590 ok;
40 failures = 21 timeout + 19 memout). Diagnosis, fixes, and benchmark deltas
tracked here.

### Frontend (`ofn`): inverse-role bridge clauses (8+ incomplete → agree)

`InverseObjectProperties(R, S)` was parsed into `hooks.role_inverses` — which no
code consumed — and `ObjectInverseOf(R)` in concepts became a fresh role
`__inv__R` with no clause linking it to `R`. The engine has no inverse machinery
of its own, so inverse-role semantics was silently dropped. Diagnosed on the
SWEET cluster (`14896`/`3795`/`4834`/`6060`/`7025`/`7320`, 24 byte-identical
missing subsumptions each): the gold derivation `Age ⊑ Set` needs
`temporalPartOf ⊑ subsetOf`, `inverse(subsetOf) = supersetOf ⊑ setRelation`,
`range(setRelation) = Set` — i.e. range of a superproperty of the inverse.

`normalise.rs` now emits the two bridge clauses `R(x,y) → S(y,x)` and
`S(x,y) → R(y,x)` per inverse pair (the same swapped-orientation shape as
symmetric roles, which the engine already propagates; verified on `14896` where
the engine derives exactly the 24 gold subsumptions once the bridges exist).

Two hardening fixes rode along: `elc`'s NF6/NF7 recognizers ignored variable
wiring (a bridge clause would parse as a FORWARD role inclusion — unsound; a
chain could bind in listed order, not chain order) and now check the wiring
explicitly, rejecting anything else to the CB engine (exit 3). `el_rbox_safe`
is also forced false whenever an inverse pair was registered, covering bare
`ObjectInverseOf` which produces no rbox record.

Clause output is byte-identical on ontologies without inverse constructs;
inverse-bearing ones gain only the bridge clauses. Harness-validated: the six
SWEET-cluster ontologies plus `3050` and `8999` flip incomplete → AGREE
(8 of the 17 incomplete; the rest have other causes). Sound by construction
(the bridges are the first-order semantics of the axiom; saturation only gains
derivations). No Lean re-cert (frontend/input clauses; calculus untouched).

### Frontend (`ofn`): sound ABox-inconsistency precheck (4 unsound → agree)

Re-diagnosed the 8 "unsound vs gold" ORE ontologies. The dominant cause is NOT
the nominal/number under-detection previously assumed: for `6720`, `15288`,
`443`, `7052` the **ABox** forces an individual into two disjoint named classes,
so the ontology is **inconsistent** (HermiT agrees; Konclude and ELK report all
classes unsatisfiable). KM missed it because the CB engine drops every
individual/ABox clause (`reasoner.rs` maps `Ind`/`Aux` terms to `None`), so the
clash never reaches saturation — KM emitted the full taxonomy of subsumptions,
which the aggregator scored as spurious "extra" subsumptions.

Witness (`6720`): `lemon_slice` is asserted both `fruit` (⊑ `non_alcoholic_-`
`ingredient`) and `sparqling_wine` (⊑ `alcoholic_ingredient`), and those two are
`DisjointClasses`.

New `frontend/abox_consistency.rs`: a sound, conservative precheck over the
parsed ontology. It closes ABox membership under the named subclass/equivalence
hierarchy, object-property domain/range, and `SameIndividual`, then reports
inconsistency iff some individual is provably in both ends of a named
`DisjointClasses`/`DisjointUnion` pair. Only NAMED classes participate (complex
operands and complex assertion concepts are skipped), so every fire is a genuine
OWL entailment — no false positives. The flag rides the `ofn` meta as
`abox_inconsistent`; `owl_classify` short-circuits to an inconsistent result
(empty subsumption set, matching the gold reasoners) without invoking the
engine. Cost is one TBox scan and an early-out (`None`) unless the ontology has
named-class disjointness, so the giants (no disjointness, no ABox) pay nothing.

Clause output is untouched (byte-identical); the only meta change is the added
`abox_inconsistent` field. Corpus-wide the flag fires only on the four family
ontologies plus two non-gold ontologies (`11305`, `11457`, both genuinely
inconsistent), and no ontology Konclude classifies consistently. Soundness vs
gold: **8 unsound → 4 unsound** (remaining: `7901` datatype empty data-range,
`8941` ALC `∀`-driven, `15516`/`2669` complex-boolean over-derivation); agree
530 → 534. No Lean re-cert (frontend, not calculus).

### Frontend (`ofn`): streaming parse + compact clause set (giant ontologies)

The three 3M-axiom giants (ore_ont_8737, 15059, 16744; 450–580 MB OFN) memouted
**in the frontend** at ~20 GB before the reasoner ever started. Three changes,
all output-preserving (byte-identical clause+meta JSON to the old frontend on the
full ORE corpus and on all three giants), cut the frontend peak ~5.5x:

- **Zero-copy tokeniser / parser** (`sexpr.rs`): tokens are now `&str` slices into
  the source produced by a lazy iterator, instead of a `Vec<String>` with a heap
  allocation per token. The parse tree (`Node`) borrows those slices. The
  whole-document token vector and its per-token strings are never materialised.
- **Streaming document walk** (`parse.rs` `for_each_ontology_child` /
  `parse_axioms`): each `Ontology(...)` child is parsed, turned into SROIQ
  axioms, and dropped, so the whole-document AST is never resident. The RBox /
  declared-class side scans re-stream the (cheap, zero-copy) parse instead of
  retaining and **deep-cloning** the AST across `normalise`/`augment` (the old
  `onto_nodes = args.clone()` was itself an O(document) copy). `reg.short` call
  order is preserved, so assigned internal names are identical.
- **Compact `DLClause`** (`clauses.rs`): `body`/`head` are sorted-deduped
  `Vec<Atom>` (canonicalised in the constructors) instead of `BTreeSet<Atom>`.
  A `BTreeSet` node over-allocates even for a 1–2 atom clause; on 3M clauses that
  dominated memory. `Ontology` also stores axioms behind `Rc` so the dedup set
  shares the allocation instead of cloning every axiom.

Measured on ore_ont_8737 (472 MB): frontend peak **19.2 GB → 3.6 GB**, wall
45 s → 20 s (per-stage `VmHWM` via `KM_OFN_TIMING`: normalise 9.4→2.6 GB,
augment 18.6→3.5 GB). Result: **ore_ont_15059 recovered** (was memout; now ok in
70 s / 5 GB, signature identical to the Konclude gold — consistent, empty
#UNSAT). 8737 and 16744 now reach the reasoner (frontend no longer the wall) but
are **not** EL-safe (inverse roles), so they route to the context engine and
remain time-bound there — the engine-scaling residual, not the frontend.

### Result (ORE 2015, 240 s / 20 GB, gold = Konclude 587 ok)

| build | ok | timeout | memout | vs baseline |
|---|---|---|---|---|
| baseline (16-thread, pre-fixes) | 551 | 21 | 19 | — |
| + Hyper join + adaptive retry | 553 | 33 | 5 | +2, 0 regressions |
| + message batching | 554 | 31 | 6 | +3, 0 regressions |
| **+ streaming frontend (final)** | **555** | 32 | 4 | **+4, 0 regressions** |

Recovered: 2397 (fully correct), 9944, 9724 (sound but CB-incomplete on
number/inverse), and 15059 (the giant — see the frontend section; agrees with the
Konclude gold). Soundness preserved: vs gold the correctness profile is unchanged
(530 agree, 17 incomplete, 8 unsound — the pre-existing CB nominal/number
under-detected-unsat cases — both-disagree = 0); the one newly-classified
ontology (15059) agrees with gold, and no previously-agreeing ontology regressed.
All landed changes (Hyper join, batching, streaming frontend) are
output-preserving, so they change *whether* an ontology finishes in budget, never
*what* it derives. km has the lowest median peak memory of the five reasoners
(45.9 MB; Konclude 65, Sequoia 536).

Residual is genuinely hard for the CB engine: live-`∀+⊔` disjunction
(message-traffic explosion — Sequoia, the same calculus, solves these via more
mature redundancy/ordering), the two remaining giants (8737, 16744 — frontend now
fits, but they are not EL-safe so they route to the context engine and time out
there), four CB-engine ~20 GB memouts (10781, 15491, 16444, 6682), and role-chain
propagation volume. The hypertableau (`tableau_cli`) is NOT a fallback: it errors
or hangs on real ORE ontologies (validated only on small synthetic + kinship).

### Hyper rule: backtracking join instead of full cartesian product
- `engine/src/engine.rs` `hyper()` / new `hyper_join()`: the Hyper rule used to
  build a candidate list per body position and iterate the **full cartesian
  product**, attempting unification per combination and discarding the ones that
  fail cross-position variable consistency. On number restrictions
  (`R(x,y1) ∧ C(y1) ∧ R(x,y2) ∧ C(y2) → …`) that is `(#successors)^k`
  combinations, almost all immediately discarded.
  Measured on ore_ont_13912: **738171 enumerated, only 2462 unifiable (99.7 %
  waste)**.
  Replaced with a backtracking join that extends the central substitution one
  body position at a time and only descends into candidates consistent with the
  bindings already made (shared neighbour variables bound earliest). Yields the
  **identical resolvent set** — the skipped combinations were exactly the ones
  that fail `unify` — at a fraction of the enumeration. Same ont: 738171 → 59410
  combinations (12×). All `cargo test` pass (incl. `factor_number_restriction_clash`,
  `existential_subsumption`). No change to soundness/completeness; pure
  enumeration optimisation.
- Added env-gated `KM_PROF` diagnostics (per-query seeding + message-loop
  progress, per-rule saturate counters). Off by default, no hot-path cost.

### Message loop: batched propagation
- `engine.rs` `run_for`: the inter-context message fixpoint used to `saturate`
  *and* `propagate` the target after **every** message. On disjunction/role-chain
  ontologies that re-scans each context's predecessor-edge and Succ/Pred pools
  thousands of times (ore_ont_5303: ~86 k propagate calls). Applying a message
  never enqueues new messages (only `propagate` does), so the loop now **drains
  the whole pending batch**, saturates each target, records the touched contexts,
  and propagates each **once** per round. `apply_succ`/`apply_pred` return the
  touched context instead of propagating inline. Fixpoint unchanged (saturation
  is monotone and confluent — the schedule does not affect the derived set);
  ~1.5× faster message throughput. Recovers ore_ont_9724; all `cargo test` pass;
  vs gold no new unsound/incomplete.

### Threading: adaptive parallel-then-single-threaded-retry (memory-aware)
- Root cause: `reasoner.rs` `saturate()` splits the named queries into
  `available_parallelism` chunks, each a full `Engine` that **re-derives the
  shared successor contexts**. On existential-heavy ontologies this multiplies
  the dominant cost by the thread count. Measured on ore_ont_2397 (ALCH): 1
  thread = 9 GB / 138 s **SUCCESS**, 8 = 40 GB, 16 = 84 GB, 64 = 20 GB **MEMOUT
  @ 9 s**.
- A *blanket* `KM_THREADS=1` is **net-negative**: it recovers the memory-bound
  onts but regresses the speed-bound ones (measured: −12 onts that needed
  parallelism for speed now time out, vs +1..4 memout recoveries). Parallelism
  is genuinely valuable for throughput; it is only harmful (memory) on the
  existential-blow-up onts.
- Fix (`owl_classify.py` `_run_engine_adaptive`): run the **default parallel**
  attempt under an RSS watchdog (`KM_PAR_MEM_GB`, default 18 GiB, just under the
  20 GiB benchmark memcap) that kills *only the engine child*; on overflow,
  **retry single-threaded** (one engine, successor contexts shared, far lower
  memory). Keeps parallel speed for the speed-bound onts (no regression) and
  recovers the memory-bound onts via the fallback. RSS (not virtual address
  space) is monitored so legitimate large parallel runs are not falsely tripped.
  An explicit `KM_THREADS` bypasses the adaptive logic.
