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
