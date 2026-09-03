# EL completion hot loop: v1.4 wall-tail review and patch (2026-09-02)

Worktree: `agent/v14-elc-wall`. Nothing here was built, run, or benchmarked;
the patch was syntax-checked with `rustfmt` only. Every number below comes from
retained artifacts of earlier IBEX runs, cited by path under
`.work/worktrees/v1.4/.work/artifacts/`.

## 1. Verdict

The elc-routed strict residuals (1579, 13224, 6722, 7868, 2828, 2469, 11207,
11315, 2803, 5549, 5566, 7728, 10248, 12387, ...) are wall-only misses with
2.5x or more peak headroom. Inside the EL block the saturation itself is now
the largest phase (13224: 1.4-1.9 s of a 2.2-2.6 s block; 7868: 2.2-2.8 s of
2.8-3.6 s), and it runs at roughly 90 ns per rule step, which is hash-probe
and allocator bound rather than rule bound. The patch removes fixed per-item
probe work from the Sub arm, bounds the one rule whose scan count is
super-linear on this family (R⊓ over conjunction hubs), removes the
allocation churn of `to_nf`, and speeds string interning. Every change is a
scheduling or indexing change under the same rule set; the least fixpoint is
unchanged (section 3 gives the argument per change, section 5 the tests).

## 2. Evidence

Phase laps of the in-process EL block (`KM_ELC_TIMING`, three replicates,
`v14-elc-hard-classify-job51200104/*.timing`):

| ontology | to_nf | index+init | saturate | output(compact) | frontend parse+clausify |
|---|---:|---:|---:|---:|---:|
| 13224 (440k clauses, 1.06M pairs) | 0.25-0.41 | 0.31-0.51 | 1.39-1.95 | 0.23-0.36 | 1.64-2.32 |
| 7868 (246k clauses, 1.29M pairs) | 0.17-0.26 | 0.22-0.31 | 2.20-2.82 | 0.19-0.27 | 1.70-2.18 |

Rule profiles (`KM_ELC_PROFILE`, `v14-elc-callgrind-job51200494/*/rule-profile.txt`
and `v14-elc-rule-profile/2828.*.stderr`):

| ontology | sub_items | edge_items | nf1_scan | nf2_scan | nf3_scan | nf4_sub_scan | nf4_edge_scan | nf7 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 13224 | 3.12M | 1.28M | 2.99M | 3.21M | 1.27M | 0.88M | 5.54M | 0 |
| 7868 (one-sided NF2 on) | 3.48M | 0.81M | 4.16M | 111.5M | 0.61M | 1.00M | 3.19M | 0 |
| 2828 symmetric NF2 | 1.22M | 0.15M | 1.29M | 812.7M | 0.15M | 0.03M | 0.16M | 0 |
| 2828 one-sided NF2 | 1.22M | 0.15M | 1.29M | 0.85M | 0.15M | 0.03M | 0.16M | 0 |

Callgrind of the elc worker (`v14-elc-callgrind-job51200494/{13224,7868}/self.txt`):
`_int_malloc` alone is 16.5% of all instructions on 13224; `elcomplete::run` is
50% on 7868.

Source profiles of the fourteen representatives
(`v14-event-race-sweep-job51191347/profiles`): `domain_axioms = 0`,
`range_axioms = 0`, `role_chain_clauses = 0`, `transitivity_clauses = 0` for
every one of them (11207 has four domain and four range axioms). So on this
family NF7 is never live, and the `∃R.⊤` filler never occurs; levers on those
rules (section 4) are inert here and were left out.

What the 0.31-0.51 s `index+init` lap actually contains: the drop of the
parsed clause set (`lean_cert_requested.then_some(clauses)` drops the
`Vec<JClause>` when no certificate is requested, freeing roughly 3.4M small
strings and vectors on 13224), then `build_idx` and `init_state`. Freeing, not
indexing, dominates that lap; the optional background release in section 3.6
targets it.

## 3. The patch, with the fixpoint-preservation argument per change

All changes are in `engine/src/elcomplete.rs` unless stated. The completion is
a monotone rule system (NF1-NF7, ⊥ propagation, role lift, reflexive seeding)
driven by a FIFO worklist; its result is the least fixpoint, which is
independent of the order in which rule instances fire as long as every
applicable instance eventually fires. Every change below preserves the set of
rule instances that fire; some change the order in which conclusions are
queued.

### 3.1 Dense per-trigger rule records (`ConceptRules`, `Idx::rules_of`)

Before: a `Sub(c, d)` item probed four hash maps keyed on `d` (`sub_rules`,
`nf5_subs`, `nf3_by_sub`, `nf4_by_filler`) plus, in the dirty tree, an
`nf2_pending.remove` probe on every item even when the one-sided index was
off. After: one dense `rule_slot[d]` read (4 bytes per interned symbol) and
one record read. The record holds exactly the same axiom lists the four maps
held for `d`, so the same rule instances fire in the same NF1, NF2, NF5, NF3,
⊥-back-propagation, NF4 order. Memory: `rule_slot` costs 4 bytes per symbol;
the records replace three map entries per rule-bearing concept, so the index
is no larger than before.

### 3.2 Min-side R⊓ join (`fire_nf2`), replacing the one-sided waiter

The dirty tree indexed each NF2 axiom under its lower-degree operand and
parked the conclusion in `State::nf2_pending` when the partner was absent,
enabled by `KM_ELC_ONE_SIDED_NF2`, which the orchestrator set only for a
fingerprint gate (`routing::one_sided_nf2_candidate`, matching the 2828 and
7868 shapes). That measured 2828's NF2 scan from 812.7M to 0.85M candidates,
but left 7868 at 111.5M, kept the symmetric rescan for every other member,
and added a pending map whose size is bounded only by the scan count.

The patch keeps the symmetric registration (each axiom under both operands,
each record sorted by partner) and evaluates the join by enumerating the
smaller side, as ELK's `ObjectIntersectionFromConjunctRule` does: if the
candidate list of `d` is at most eight times the label of `c`, scan the list
and probe the label (the established scan); otherwise iterate the label and
binary-search the sorted list for each member, buffering conclusions until the
label borrow ends. Both branches fire exactly the conclusions `E` with
`(X, E)` in the list and `X` in the label, so the fired instances are
identical; the direct scan is unchanged for the sparse case, and a hub with
`L` candidates arriving in a context with an `S`-element label costs
`S log L` instead of `L`. No pending map, no environment flag, no gate, valid
in certificate and incremental modes because nothing outlives the item.

Cost model on the retained profiles: 2828's hub (about 10k candidates,
50k contexts, labels of tens) drops from 812.7M probes to well under 5M
label-side lookups; 7868's 111.5M residual scans are, by the 20 ns per scan
implied by its 2.2 s saturate lap, mostly real joins on large labels and stay
on the direct branch, so 7868 is neither helped nor hurt by the join itself
(the pending-map inserts the one-sided scheme paid on absent partners
disappear). Members that never met the fingerprint (13224 and the rest) keep
their sparse scans and gain the hub bound for free.

Removed with it: `State::nf2_pending`, `Idx::one_sided_nf2`, the
`KM_ELC_ONE_SIDED_NF2` variable, `routing::one_sided_nf2_candidate` and its
test, the `ROUTE_KEYS` entry, and the orchestrator `set_var` block
(`engine/src/routing.rs`, `engine/src/orchestrate/mod.rs`).

### 3.3 Sub-side NF4 join skipped for contexts without backward links

When `d` is an NF4 filler, the Sub arm registers the propagations in
`prop[(c, R)]` (unchanged) and then joins them against the backward links of
`c` by exact role. The join now runs only if `in_roles[c]` is non-empty. A
context with no backward links has no `(parent, axiom)` pair to fire, so the
skipped probes were all misses; edges arriving later still fire the stored
propagations edge-side, exactly as before.

### 3.4 `to_nf` partition scratch vectors

The four per-clause `Vec<&JAtom>` partitions are declared once and cleared per
clause. This removes about four allocations and four frees per clause
(1.8M on 13224) from the `to_nf` lap. Pure allocation reuse; the borrowed
atoms and every decision taken on them are unchanged.

### 3.5 Word-at-a-time `FxHasher::write`

The module's FxHash processed one byte per multiply-rotate step, so interning a
60-100 byte IRI cost 60-100 steps. It now folds eight bytes, then four, then
the tail, as rustc-hash does. The hash is still a deterministic function of the
byte sequence; every string-keyed table in the module is used for membership
only (the interner map is never iterated; the inverse-bridge helper sorts its
output; the Lean variable map only numbers variables), so no result depends on
the hash values.

### 3.6 Optional background release (`KM_ELC_BG_DROP`, default off)

`release(value, background)` drops a dead value inline by default. With the
variable set, the parsed clause set (after `to_nf`) and the dead saturation
structures (indexes, normal forms, edges, backward links, propagations,
worklist) are dropped on a detached thread instead, so the millions of small
frees leave the critical path. Scheduling only: the values are unreachable
either way. Peak RSS is unaffected in principle (the peak sits at the end of
saturation, long after the clause set has been freed, and the post-fixpoint
release overlaps only the compact rows), but glibc arena contention between
the freeing thread and the saturating thread is unmeasured, which is why the
flag is opt-in and the A/B below has a dedicated arm.

## 4. Considered and not done

* `∃R.⊤` (domain) filler special-casing: registers `n x k` propagations and
  allocates one `prop` vector per (concept, role) on domain-rich ontologies.
  Exact and worthwhile in general, but every representative here has zero
  domain axioms, so it would not move this family; left for a domain-heavy
  panel.
* NF7 pre-filtering and the per-edge `edges[d]` snapshot: no live chains on
  the family (`role_chain_clauses = 0`).
* Single-allocation interner (each name is stored twice today): about
  130k-260k allocations and a few MB; small next to 3.4M clause frees.
* Restructuring `in_by_role` / `prop` as per-node arrays: touches the
  certificate repair and incremental paths; not justified without a build.
* Worklist discipline (LIFO would shrink the queue) interacts with the
  frontier batch (`fire_edge_nf4_batch` reads consecutive Edge items at the
  queue front); deliberately untouched.
* Dictionary-coded frontend handoff (the frontend still hands one owned
  `String` per atom): the largest remaining lever for the whole route, but an
  interface change across frontend and completion, outside this patch.

## 5. Expected effect

Estimates from the profiles, not measurements. Per Sub item the patch removes
four hash probes on cold index maps (about 100-150 ns at 3-3.5M items, so
0.3-0.5 s of the 13224 and 7868 saturate laps); `to_nf` loses 1.8M
allocations (0.1-0.15 s on 13224); interning loses about 80% of its hashing
work (0.05-0.1 s on 13224). On 2828-like hubs the NF2 join stays at the
one-sided level without the pending map. With `KM_ELC_BG_DROP=1` the
`index+init` lap should lose most of its 0.2-0.3 s of frees on 13224 if arena
contention is benign. Peak memory is flat or lower: no pending map, one dense
slot array instead of three maps, no per-clause scratch churn.

## 6. Tests to run (Codex)

Use an isolated target directory (the shared one races with sibling jobs):

```
cd engine
export CARGO_TARGET_DIR=$PWD/../.work/target-elc-wall
cargo build --release
cargo test --release --lib elcomplete::tests::saturation_matches_the_naive_fixpoint_on_random_terminologies
cargo test --release --lib elcomplete::tests::nf2_join_fires_in_both_arrival_orders_from_either_side
cargo test --release --lib elcomplete::tests::interner_distinguishes_long_names_at_every_chunk_boundary
cargo test --release --lib elcomplete::tests::shared_nf1_nf2_bucket_preserves_the_serial_horn_closure
cargo test --release --lib elcomplete::
cargo test --release --lib routing::
cargo test --release --lib orchestrate::
cargo test --release
```

The differential test compares `build_idx` + `run` fact for fact against a
naive rule-by-rule fixpoint on 32 random terminologies (all normal forms, a
64-axiom conjunction hub, `∃R.⊤` fillers, role inclusions, a chain, ⊥, a
reflexive role) and asserts that the label-side join was exercised.

Corpus check (IBEX, three replicates each, same harness as
`.work/agents/fable-v14-elc-tail/ibex_v14_elc_tail_paired.sbatch`):

1. Arms: baseline (commit before this patch), candidate, candidate with
   `KM_ELC_BG_DROP=1`.
2. Ontologies: 13224, 7868, 2828, 2469, 11315, 2803, 5549, 5566, 7728, 10248,
   12387, 1579, 6722, 11207, plus the sweep's elc-routed controls.
3. Verify the signature of every candidate run against the retained gold
   (`verdict == match`, `subsumptions` and `unsatisfiable` counts unchanged);
   any mismatch is a stop.
4. Record `KM_ELC_TIMING=1 KM_ELC_PROFILE=1` laps on 13224, 7868 and 2828:
   expect identical `sub_items`/`edge_items`/`nf1_scan`/`nf3_scan`/
   `nf4_*` counters between arms, a non-zero `nf2_label_side` on 2828 and
   7868, `nf2_scan` on 2828 within a small factor of the one-sided 0.85M, and
   lower `saturate`, `to_nf` and (flagged arm) `index+init` laps.
5. Report wall and peak per arm; the peak of the flagged arm must stay within
   the sweep's headroom on every member.

## 7. Measured result

The 2026-09-02 IBEX gate classified all 253 ontologies selected by the ELC
automatic route with the candidate binary. Every signature matched gold and
every run retained the `elc` route. Against the frozen per-ontology thresholds,
14 previous failures became joint wall-and-memory wins, including 5462, which
also crossed its memory threshold. The number of strict ELC wins increased
from 215 to 228 in the one-shot sweep.

The only apparent regression, 5927, did not reproduce in a five-repetition
same-node paired run. Candidate median wall was 1.9166 seconds, baseline median
was 1.9007 seconds, and both remain below the 2.1075-second threshold. All ten
paired classifications matched gold. The optional background-drop arm was
slower and used more memory on the three-ontology diagnostic panel, so
`KM_ELC_BG_DROP` remains disabled by default.

## 8. Context-local worklist scheduling (agent/v14-elc-residual2, 2026-09-02)

Second patch on the same family, written without building or running
anything (rustfmt-checked only). It targets the cost section 1 left in
place: the saturation lap still runs at memory latency, and section 4 had
deliberately left the worklist discipline alone because of the frontier
batch.

### 8.1 Diagnosis

The 18 elc-routed strict residuals after section 7 (1579, 13224, 6722,
15976, 7868, 16596, 2469, 795, 4802, 15929, 12087, 5566, 12387, 5612, 2828,
10248, 2803, 11293) are wall-only misses; peak passes with 2-3x headroom on
every one (`v14-combined-full-sweep/strict-audit.json`). Eight of them are
within 20% of the ELK wall target and four within 5% (11293 1.007x, 2803
1.012x, 10248 1.05x, 2828 1.07x).

Retained laps of the in-process route (`v14-close-elc-profile/*.timing`,
`v14-elc-hard-classify-job51200104/*.timing`) split the wall of the
near-threshold members into roughly 40% frontend parse+clausify, 40% EL
block, 15-20% public-output mapping and serialisation; inside the EL block
the saturation is the largest lap (13224: 1.7 s of 3.1 s before section 3;
7868: 2.2 s of 2.8 s). The rule profiles of section 2 put that lap at 4.4M
items and about 13M label probes for 13224, i.e. 100-130 ns per probe: the
per-context label tables (`sub_super[c]`, one hash table per symbol, 130k
symbols) are visited cold because the single FIFO interleaves the items of
every context. The compact-output sort keys on interned names and is also
miss-bound, but its name order is load-bearing (the first-alias unsat
representative in the orchestrator's mapping), so it is left alone.

### 8.2 The change

`elcomplete::Worklist` replaces the `VecDeque<Item>` of `State`. The default
discipline, `Worklist::Contextual`, is ELK's context activation: items are
chained per context (the subject of a `Sub` item, the source of an edge) in
a slot arena with a dense `head[c]` table; a context enters a FIFO activation
queue when it receives its first pending item and `pop` drains it completely,
including the items its own processing queues for it, before the next
activated context is taken. A context's burst of conclusions is therefore
processed while its label, edge set and backward-link roles are hot, and
those tables are fetched once per activation instead of once per item. The
arena recycles freed slots last-freed first and never holds more than the
peak number of simultaneously pending items, which is far below the FIFO's
layer-sized peak.

`Worklist::Fifo` keeps the historical single queue. It is selected by
`Worklist::from_env` when `KM_ELC_PAR_NF4` is set (the parallel NF4 frontier
batch, armed by the orchestrator for one giant profile, is defined over a
consecutive edge frontier at the front of that queue and now declines on a
contextual worklist) or when `KM_ELC_FIFO` is set for A/B measurement. The
incremental classifier replays its retained facts through the same API
(`grow` widens the context table for appended symbols), the repair fork
copies the discipline, and `KM_ELC_PROFILE` reports `ctx_activations`.

### 8.3 Fixpoint preservation

Every fact enters the state through `add_sub`/`add_edge`, which queue exactly
one item for it, and `run` processes every queued item exactly once with the
same per-item rule code under either discipline. The joins are
order-independent because their partner tables are updated at insertion
time: backward links (`in_by_role`) at `add_edge`, propagations (`prop`) when
the filler `Sub` item is processed and joined against the links that exist
then, labels at `add_sub`; so each (backward link, propagation), (edge, ⊥ in
target) and (edge, edge) chain pair fires from whichever side arrives second.
The completion is a finite monotone closure, hence the derived facts, the
item counts (`sub_items`, `edge_items`) and the per-item scan counters
(`nf1_scan`, `nf3_scan`) are identical; `nf2_scan`, `nf4_sub_scan`,
`nf4_edge_scan` and `botback` may redistribute between the two sides of a
join. The hash sets of the state can iterate in a different order after a
different insertion order; every consumer sorts or treats them as sets
(compact rows are name-sorted, the string map is a BTreeMap, the
certificate indexes are set-based), as section 3.2 already relied on.

### 8.4 Expected effect (estimate, not a measurement)

Under the FIFO, items of one context are contiguous only within the burst
one item produces (one to three conclusions), so roughly every other item
switches context; under activation the switch happens a few times per
context. On 13224 that is about 2.5M fewer cold label visits (two misses
each) in a 4.4M-item lap, an estimated 0.3-0.5 s of the saturate lap; the
edge-set and backward-link accesses of edge items gain the same way. On the
near-threshold members the saturate lap is 0.3-0.4 s of a 2.0-2.1 s wall, so
the expected 5-10% wall cut is what closes 11293, 2803 and 10248 and moves
2828, 5612 and 12387 toward their thresholds. Peak memory should not rise:
the arena is smaller than the FIFO's layer, and the dense tables cost five
bytes per symbol.

### 8.5 Tests added

* `contextual_worklist_drains_one_activated_context_at_a_time`: activation
  order, same-activation processing of a context's own conclusions, release
  and re-activation, slot recycling, `grow`, `clear`, `items`, `new_like`.
* `contextual_scheduling_reaches_the_fifo_closure_on_random_terminologies`:
  the 32 random terminologies of section 5 run under both disciplines via
  `init_state_with`; labels, edges, `sub_items`, `edge_items`, `nf1_scan`,
  `nf3_scan` must agree, only the contextual run activates contexts.
* `frontier_batch_keeps_the_serial_join_on_the_contextual_worklist`: the
  batch declines on a contextual worklist and the serial join reaches the
  closure in one activation; the two existing batch tests pin the FIFO.
* `saturation_matches_the_naive_fixpoint_on_random_terminologies` and every
  other `run`-based test now exercise the contextual discipline by default.

### 8.6 Tests and A/B to run (Codex)

```
cd engine
export CARGO_TARGET_DIR=$PWD/../.work/target-elc-residual2
cargo test --release --lib elcomplete::tests::contextual_worklist_drains_one_activated_context_at_a_time
cargo test --release --lib elcomplete::tests::contextual_scheduling_reaches_the_fifo_closure_on_random_terminologies
cargo test --release --lib elcomplete::tests::frontier_batch_keeps_the_serial_join_on_the_contextual_worklist
cargo test --release --lib elcomplete::
cargo test --release
```

Corpus check as in section 6, with arms baseline (`KM_ELC_FIFO=1`) and
candidate (default), three replicates, on the 18 residuals plus the elc
controls and the 8737 giant (which must keep `KM_ELC_PAR_NF4` and hence the
FIFO; its `nf4_batch_calls` must be unchanged). Every signature must match
gold; `KM_ELC_PROFILE` must show identical `sub_items`, `edge_items`,
`nf1_scan`, `nf3_scan` between arms and a non-zero `ctx_activations` on the
candidate only.

## 9. Context-parallel saturation (agent/v14-elc-context-parallel, 2026-09-03)

Third patch on the same hot loop. Section 8 made the schedule context-local
on one thread; this one runs that decomposition on several threads. It is
opt-in (`KM_ELC_PAR_CTX`), off by default, and it changes no rule and no
route.

### 9.1 The change

`KM_ELC_PAR_CTX=<n>` (or `auto`, capped at 8) saturates on `n` workers.
Context `c` is owned by worker `c % n` and stored at slot `c / n` of that
worker's dense tables. A worker holds the entire mutable state of the
contexts it owns and nothing else: the label `sub_super[c]`, the forward
edges `edges[c]`, the backward links `in_by_role[(c, ·)]` with their role
list `in_roles[c]`, and the propagations `prop[(c, ·)]`. Nothing is shared
and nothing is locked on the rule path; `Idx` is immutable and read by every
worker. Conclusions for a context another worker owns are batched (1024
messages) and handed to that worker's mailbox.

The edge rules are split into the two halves the serial arm fuses, which is
what makes every rule read only the context it fires in:

| item | context | rules |
|---|---|---|
| `Sub(c, d)` | `c` | NF1, NF2, NF5, NF3, ⊥ back-propagation, NF4 registration and the sub-side join |
| `Fwd(c, r, d)` | source `c` | role lift, NF7 with `c` as the middle context |
| `Link(c, r, d)` | target `d` | edge-side NF4 join on `prop[(d, r)]`, the ⊥ check on the label of `d`, NF7 with `d` as the middle context |

The serial Edge arm runs the `Link` half at the source while reading the
target's propagations, label and out-edges; moving it to the target is the
only structural difference between the two engines.

### 9.2 Fixpoint preservation

The completion is a finite monotone closure, so its least fixpoint depends
only on every applicable rule instance firing at least once, not on the
order. Each fact is inserted into its owner's table exactly once (the
`HashSet::insert` and new-edge guards) and queues exactly one item, so every
one-premise instance fires exactly once. Every two-premise join of the
calculus is intra-context, hence totally ordered by its owner's thread, and
both sides register before they scan:

* NF2 at `c`: both premises are members of `sub_super[c]`; an item is queued
  after its member is inserted and then scans the label for the partner.
* NF4 at `d`: the `Sub` item of a filler extends `prop[(d, R)]` and then
  scans `in_by_role[(d, R)]`; the message that queues a `Link` item appends
  to `in_by_role[(d, R)]` first and the item then scans `prop[(d, R)]`.
* ⊥ over an edge at `d`: `Sub(d, ⊥)` scans the backward links; a `Link` item
  scans the label for ⊥.
* NF7 at the middle context `m`: a `Link` item is queued after its link is in
  `in_by_role[(m, ·)]` and scans `edges[m]`; a `Fwd` item is queued after its
  edge is in `edges[m]` and scans `in_by_role[(m, ·)]`.

In each case the side that arrives second cannot miss the side that arrived
first, because the first was in its own table before the second was created
and both sequences run on one thread. So the derived set is the fixpoint the
serial `run` computes; `sub_items`, `edge_items`, `nf1_scan` and `nf3_scan`
are invariant, while `nf2_scan`, `nf4_sub_scan`, `nf4_edge_scan` and
`botback` may redistribute between the sides of a join, exactly as in
section 8.

Termination is a credit count: a worker holds one credit while it has
anything to do and one credit accompanies each published batch, taken before
the batch is visible and released by the receiver after it is applied (the
receiver re-takes its own credit first). `credit == 0` therefore certifies
that no worker is running, no item is queued and no message is in flight, and
zero is stable because new work is only created while holding a credit.

Determinism: the fixpoint is unique but the arrival order of a label's
members is not, and the classification writes each row in the label's
iteration order. Each worker therefore rebuilds the labels of its contexts
from a sorted vector before it exits, so the output is byte-identical for any
worker count and any interleaving.

### 9.3 What stays serial

The parallel engine reaches the same fixpoint but not the same construction
order, so it declines wherever the order is load-bearing rather than the
result: `KM_ELC_PAR_NF4` (whose frontier batch is defined over a consecutive
edge run at the front of one global FIFO), `KM_ELC_FIFO` (the A/B baseline),
and every certificate mode (`KM_ELC_CERT`, the Lean certificate), whose
repair fork picks merge representatives and blame witnesses in construction
order. The incremental classifier and the positive-ABox path build their
states directly and are untouched. A failed thread spawn falls back to the
serial engine.

### 9.4 Tests

* `context_parallel_saturation_matches_the_serial_fixpoint`: the 32 random
  terminologies of section 5 at one, two, three and four workers, compared
  against the serial engine and the naive fixpoint fact for fact, including
  the backward links, the propagations, the edge count and the invariant
  counters.
* `context_parallel_labels_iterate_identically_for_every_worker_count`: a
  256-concept terminology run at eight different worker counts; the label
  ITERATION order (what the output rows are written from) must be identical,
  and the multi-worker runs must actually have exchanged batches.
* `context_parallel_stress_matches_the_serial_fixpoint_over_repeated_runs`:
  four larger terminologies with every normal form live, four repetitions
  each at four workers against the serial engine.
* `context_parallel_classification_is_byte_identical_across_worker_counts`:
  end to end through `classify` (NF1 chains, conjunctions, existentials, an
  NF4 axiom, a role inclusion, a role chain, an unsatisfiable conjunction) at
  one, two and four workers; the serialised result is compared byte for byte
  across worker counts and answer for answer against the serial engine.
* `context_parallel_propagates_bottom_and_chains_across_shards`: a chain
  whose consecutive contexts land on different workers, so ⊥, the NF4 join
  and the role composition all travel as messages.
* `context_parallel_plan_keeps_the_order_sensitive_modes_serial` and
  `shard_queue_drains_one_activated_context_at_a_time`: the policy and the
  shard-local activation queue.

### 9.5 Not measured (superseded by section 10)

At the time this section was written nothing here had been benchmarked. The
A/B below ran as IBEX array `51251013`; section 10 records it and the selector
it justifies. The arms were baseline (default) and
`KM_ELC_PAR_CTX` at 2, 4 and 8 on the 18 residuals of section 8.1 plus the
elc controls, three replicates, every signature checked against gold, with
`KM_ELC_PROFILE` showing identical `sub_items`, `edge_items`, `nf1_scan` and
`nf3_scan` between arms and `link_items == edge_items` on the parallel arm.
The known costs to look for: the per-context tables are split over the
workers, so a shard's dense queue tables cost 5 bytes per owned context and
nothing per foreign one, but the message buffers and the label rebuild at the
end of the run are new work; and the static `c % n` ownership does not
rebalance, so a run whose closure concentrates in a few hub contexts will not
scale.

## 10. Automatic selection of the context-parallel mode (agent/v14-elc-routing-gates, 2026-09-03)

Section 9 left the mode opt-in and unmeasured. This section records the
measurement and arms it from the source profile. No rule, route, or published
answer changes; the selector only chooses a worker count for the completion
that section 9.2 proved fixpoint- and output-identical at every count.

### 10.1 The measurement

IBEX array `51251013`, binary SHA-256 `06215e49...d745661`, Intel Xeon Gold
6248, 16 CPUs, 480 s timeout, 20 GiB memcap: four arms (serial, and
`KM_ELC_PAR_CTX` at 2, 4, 8) times three replicates over the eighteen
elc-routed residuals of section 8.1. All 216 runs returned `status=ok` with a
gold-matching signature, and the twelve runs of each ontology share one
signature SHA-256, which is the determinism claim of section 9.2 confirmed on
real input.

Eight workers cut the median wall of every one of the eighteen, from 0.3%
(5566) to 22% (795); the largest gains land on the members whose saturate lap
dominates (13224 20.8%, 7868 21.1%, 11293 20.1%). Two workers were slower than
the serial engine on five members, so the two-worker arm is never selected.
Peak rises by 0-38% on the terminology-only members and by 1.34x and 1.97x on
the two with an ABox (1579, 6722), and no member on any arm came near its
external peak target.  Confirmation array `51251710` increased the four
prospective recoveries to ten observations per serial/context-eight arm.  All
four remained strict wins; the narrowest wall margin increased to 4.15%.

The medians, and the complete 592-profile projection of the selector below,
are in `results/benchmarks/2026-09-03-v14-elc-context-parallel-routing/`.

### 10.2 The selector

`routing::elc_context_parallel_workers` returns the worker count for a source
profile: eight where the machine has eight or more CPUs, four from four to
seven, and `None` below that (never the measured-regressing two-worker arm).
It admits the family the panel measured, keyed on source features only:
the same EL source certificate the bare route selects on, the EL class
fragment with `max_concept_depth <= 3`, work floors at the smallest measured
member (100k logical axioms, 20k classes, 20k existentials), ceilings at the
widest (400k logical axioms, 64 MiB and 32 role chains), plus a measured-family
object-property interval of 8--12,
and no ABox, whose two measured members hold the two largest peak increases
and recover nothing.

`orchestrate::elc_context_parallel_setting` applies it: an explicit
`KM_ELC_PAR_CTX` always wins (the key is now route-managed, so the request is
captured before route selection clears it and the A/B arms stay reproducible
under `KM_ROUTE=auto`), and without one only `Route::Elc` is armed. The
certificate routes and the giant's NF4 frontier batch keep their construction
order, and `context_parallel_plan` still declines the mode for them
independently. A failed thread spawn still reverts to the serial engine.

Over all 592 retained source profiles the selector changes no route and arms
exactly nine ontologies, all measured in the paired panel and all on the bare
EL route.  It projects four strict recoveries (795, 2828, 5612, 15929) with no
regression and no unmeasured activation.  The confirmation panel establishes
the four wins with wall margins of 4.15--21.28%.

### 10.3 Tests

* `routing::tests::context_parallel_gate_arms_the_measured_el_terminology_family`:
  the panel's smallest member routes to `Route::Elc` and arms eight workers at
  8-16 CPUs, four at 4-7, and nothing below four.
* `routing::tests::context_parallel_gate_declines_outside_the_measured_family`:
  an ABox, every non-EL class constructor, deeper concepts, imports, rules, and
  each floor and ceiling, one at a time.
* `routing::tests::context_parallel_gate_is_deterministic_for_one_profile` and
  `context_parallel_gate_carries_no_ontology_identity`.
* `routing::tests::context_parallel_projection_over_the_retained_profiles`: the
  592-profile ledger, asserting exactly nine activations and that nothing off
  `Route::Elc` is ever armed.
* `orchestrate::tests::context_parallel_schedule_is_armed_only_on_the_bare_el_route`,
  `an_explicit_context_parallel_request_survives_route_selection`, and
  `context_parallel_schedule_follows_the_available_parallelism`.
