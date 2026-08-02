# ore_ont_1194: inverse-role bridges on the certified-EL route (2026-08-02)

Host `leechuck-office`, branch `codex/opus-1194-inverse`. Input is the frontend
clause payload `/tmp/1194.clauses.json` (270 MB, 1,062,240 clauses). Every run
is bounded by `run_1194.sh`: `systemd-run --scope MemoryMax=24G MemorySwapMax=0`
around `/usr/bin/time -v /usr/bin/timeout 240`.

## 1. What the bridge roles are actually used for

`audit_roles.py` classifies every role atom by the syntactic position it holds
(`role-audit.txt`). 1194 carries 14 bridge clauses: six mutual pairs and two
one-way inclusions.

| role | `A ⊑ ∃R.f` | `∃R.C ⊑ D` | reverse-shaped | chain |
| --- | --- | --- | --- | --- |
| BFO_0000050 | 28,826 | 144,130 | 0 | 0 |
| BFO_0000051 | 10,256 | 45,127 | 0 | 0 |
| RO_0002202 | 28,826 | 144,130 | 0 | 0 |
| RO_0002203 | 102 | 107 | 0 | 0 |
| BSPO_0000098 / 0000102 | 4 / 2 | 12 / 6 | 0 | 0 |
| BSPO_0000124 / 0000125 | 1 / 1 | 1 / 1 | 0 | 0 |
| distally_ / proximally_connected_to | 37 / 56 | 37 / 56 | 0 | 0 |
| surrounded_by__uberon / surrounds | 32 / 20 | 32 / 20 | 0 | 0 |
| has_distal_part, has_proximal_part | 0 | 0 | 0 | 0 |

Both sides of every mutual pair carry NF3 and NF4 axioms, and no role appears in
an already reverse-shaped clause or a chain. So for each pair, whichever side is
eliminated, tens of thousands of its axioms become reverse-oriented rules. There
is no free orientation to pick.

The two one-way roles have no uses at all beyond their bridge.

## 2. Why reverse-oriented rules cannot be run here

`elcomplete::tests::reverse_oriented_inverse_nf4_would_be_unsound` is the
countermodel, verified in both directions:

- on the clean tree the test passes;
- applied to the eager-canonicalisation candidate this session started from, it
  fails with `unsound: derived D ⊑ E, which has a countermodel`.

`C ⊑ ∃R.D`, `C ⊑ A`, `S = R⁻`, `∃S.A ⊑ E`. The rewrite makes the last axiom
`R(y,x) ∧ A(y) → E(x)`, which fires along `C —R→ D` and yields `D ⊑ E`. The
interpretation `Δ = {d}`, `D = {d}`, all other names empty, models all four
axioms with `d ∉ E`.

A node in this completion denotes the generic instance of a concept name, so one
successor node `D` is shared by every `X ⊑ ∃R.D`. A reverse-oriented rule
concludes at that shared successor from one of its predecessors. Making it sound
needs the successor to carry `∃R⁻.A` in its identity, which is a concept-set
context and so the CB engine.

The earlier measurement of the same candidate (`/tmp/1194-inverse-v1.log`,
`v2.log`) had it at 14.0-14.2 GB without finishing base saturation in 150 s,
against 96.19 s / 3.29 GB for the ordinary base. The soundness result makes the
performance result moot.

## 3. What the exact rewrites recover

Same binary, `KM_ELC_NO_BRIDGE_PREP=1` switching the preprocessing off, both
runs `KM_ELC_CERT=2` at 240 s / 24 GiB.

| | residual clauses | peak RSS | conflict restarts reached | output |
| --- | --- | --- | --- | --- |
| prep off (`elc-cert2-prep-off.err`) | 217 | 6.73 GiB | 5 | none, timeout |
| prep on (`elc-cert2-prep-on.err`) | 202 | 6.27 GiB | 15 | none, timeout |

The prep removes 52 clauses over 25 head-free roles, 15 of them residual. It
refuses all six mutual pairs by name, and takes both one-way bridges through the
vacuous-role rule. Each residual clause costs a join over a 499,904-node,
44.2M-edge model on every repair round, so the same wall budget carries the
search about three times as far.

## 4. Where 1194 is still blocked

Not on the bridges. The trace ends in covering-disjunction repair and the
conflict restarts it drives (`clause 131 conflict, banning choice (490064, 134,
281002)` at `__chain__BFO_0000051__HP_0001941`). This matches the earlier
per-round histogram finding: an empty-body cover is violated once per domain
element over 499,904 nodes, so one clause spans several rounds at
`REPAIR_VIOL_CAP=100_000`, and the disjunction census exhausts `MAX_ROUNDS`
before a bridge is ever enumerated.

The next lever on this route is the covering-disjunction model search: bulk
repair for clauses whose violation set is the whole domain, and a
non-restarting conflict strategy. Not the bridges.

## Reproduce

```bash
CARGO_TARGET_DIR=.../engine/target cargo build --release --bin elc
BIN=.../release/elc ./run_1194.sh prep-on  KM_ELC_CERT=2 KM_ELC_DEBUG=1 KM_ELC_TIMING=1
BIN=.../release/elc ./run_1194.sh prep-off KM_ELC_CERT=2 KM_ELC_DEBUG=1 KM_ELC_TIMING=1 \
    KM_ELC_NO_BRIDGE_PREP=1
python3 audit_roles.py /tmp/1194.clauses.json
python3 audit_vacuous.py /tmp/1194.clauses.json
```

## 5. Follow-up: virtual inverse execution and bulk cover repair

Two scheduling/representation experiments were tested against the same 240 s /
24 GiB local gate. Neither changes the released 591/592 result. The complete EL
suite later rejected virtual inverse execution on soundness grounds; the bulk
cover batching experiment remains exact.

### Virtual reciprocal roles (rejected: unsound lower bound)

A guarded prototype represented reciprocal inverse edges virtually and fired
their NF4 and role-hierarchy consequences without storing mirror edges. Its
focused tests covered both event arrival orders, hierarchy propagation, and
fail-closed rejection of chain uses. The complete EL module suite then exposed
two existing shared-witness countermodels:

- `reverse_oriented_inverse_nf4_would_be_unsound`;
- `a_reverse_rule_at_a_shared_witness_would_assert_a_named_subsumption`.

A generic filler node is shared by several existential edges. Executing an
inverse NF4 rule at that shared node can assert a named subsumption that has a
countermodel. The prototype therefore corrupts the certificate's sound lower
bound and is rejected, irrespective of performance. Virtual inverse execution
must not be integrated without predecessor-sensitive witness contexts or an
equivalent exact construction.

The measurements below remain useful only as attribution of the invalid
experiment's explosion:

| virtual pairs | diagnostic at the first useful checkpoint | result |
| --- | --- | --- |
| all six | 5.0M processed, 264.1M queued, 265.3M NF4 sub-side joins | timeout, 21.1 GiB |
| all except BFO_0000050/51 | 25.0M processed, 56.1M queued | stopped after attribution |
| four low-volume pairs | base fixpoint after about 121M facts; queue peaked near 18M | reached certificate repair |

The BFO pair causes the catastrophic cross-product; RO_0002202/03 is the
secondary source. The earlier 10,000-use performance fence does not repair the
semantic defect: even a low-volume pair can trigger the same shared-witness
countermodel.

### Complete-batch top-level covers

When the 100,000-violation cap is filled entirely by one clause of the form
`[] -> A(x) | B(x) | ...`, the prototype completes that same clause's join over
the live domain before applying choices. It preserves node order and the
existing per-binding choice/conflict logic; only the batching boundary changes.
All ten certificate-repair regression tests plus a dedicated complete-domain
test pass.

On 1194, the six covers finished in 12 rounds rather than consuming the full
round budget. The next round still hit a high-volume inverse bridge:

| candidate | last progress | wall / peak RSS | output |
| --- | --- | --- | --- |
| bulk covers only | round 13 | 240.60 s / 17,892,576 KiB | none |
| four virtual pairs + bulk covers | round 13 | 240.84 s / 17,710,336 KiB | none |

This establishes the next implementation target: a symbolic or projected
treatment of the two high-volume inverse pairs. Fact-by-fact virtual closure is
not viable under the production contract.

### Cancelled long run

Slurm job `49870738` ran the four-small-pair plus bulk-cover candidate on IBEX.
It reached 102,215,204 KiB RSS while still inside repair round 13 and was
cancelled when the complete EL suite exposed the virtual-inverse soundness
failure. It produced no taxonomy and no completion checkpoint. The archival
`ibex_long_reference.sbatch` harness now refuses to run unless an explicit
diagnostic override acknowledges that its candidate is unsound; its output must
never be used as classification or benchmark evidence.

## 6. Sound upper-model compression and scheduling probes

The sound follow-up keeps every inverse bridge residual. It applies inverse
edges only inside certificate upper-model forks, so they cannot contaminate the
EL lower bound. An adaptive concept-label set keeps ordinary labels as integer
hash sets and converts labels above 4,096 entries to Roaring bitmaps. The full
71-test EL module suite passes, including both shared-witness countermodels.

All runs below used the 240-second, 20-GiB production gate and produced no
taxonomy. Every run reached the first BFO inverse bridge in repair round 13.

| sound candidate | wall | peak RSS KiB | result |
| --- | ---: | ---: | --- |
| bulk cover + adaptive labels, FIFO repair | 240.56 s | 14,256,920 | timeout |
| plus repair-only LIFO | 240.36 s | 7,757,264 | timeout |
| plus 4,096-edge incremental closure | 240.30 s | 7,723,088 | timeout; rejected as slower within round 13 |
| plus base propagation-index dedup | 240.30 s | 7,630,520 | timeout |
| plus active-premise dispatch filter | 240.35 s | 7,638,636 | timeout |
| suppress terminal work-item enqueue | 240.34 s | 7,592,664 | timeout; rejected because it reaches round 13 later |

The propagation-index pass removed 7,901,400 duplicate entries exactly. A
separate 20-GiB diagnostic on the active-premise candidate remained inside the
same round after 6:12 wall time. Compression therefore fixes the memory failure,
but fact-by-fact closure of the BFO bridge still costs minutes. The next exact
design needs predecessor-sensitive witness contexts, symbolic edge-local
labels, or another representation that avoids asserting inverse consequences
on shared generic filler nodes.

## 7. Existing QoSat/KPSet predecessor-sensitive route

The existing hypertableau QO specialist was tested directly on the retained
cardinality-aware TInput (`/tmp/1194-card.tin.json`, 932,183 clauses before the
worker's transitive closure and unfolding). Direct worker invocation was
necessary because the automatic router gives 1194 to the cardinality candidate
before the QO candidate. Every run used the production 240-second, 20-GiB gate
and produced zero output.

| configuration | last progress at timeout | result |
| --- | --- | --- |
| INVCOMPOSE + FPROP + SAT + KPSET | 1,265,838 composed clauses; 10M drain steps, 89,753 nodes | timeout |
| no composition, SAT fillers + KPSET | 26M literal steps after a 22.8M-edge wave; 186,146 nodes | timeout |
| no composition, shared fillers + KPSET | 13M-edge wave nearly drained, then 2.9M literal events and a new 0.75M-edge wave; 80,527 nodes | timeout |

The shared-filler run is the least expensive of these routes, but it still does
not reach the deterministic precompute fixpoint. `EDGEFAST` and `FASTIMPL` save
only a few seconds. Yielding from the edge queue every 100,000 pops is a strict
regression: processing the intervening literal wave regenerates edges faster
than they drain, leaving 3.8M queued edges at the wall. The schedule prototype
was rejected.

An instrumented 90-second run attributed the remaining volume: by 86 seconds it
had attempted about 330M `kp_write`/propagation operations, 280M `add_lit`
operations, and only 10M full body matches. A sound prototype deferred pure
inverse-NF4 containment checks symbolically to the fixpoint and passed eager-vs-
symbolic inert/load-bearing inverse tests, but the 1194 trace remained nearly
identical. The counter is therefore dominated by the broader propagation
cross-product, not duplicate inverse-check insertion alone; that prototype was
also rejected.

These measurements rule out the current compose, separate-filler, queue-yield,
and inverse-check-dedup variants as 1194 closures. The next QO implementation
target must compress the complete propagation payload itself, for example by
sharing role/filler consequence sets rather than issuing one `add_lit` attempt
per edge and conclusion.

## 8. Batched propagation and exact edge membership

The QO precompute now has two result-preserving, opt-in data-path improvements:

- `KM_HT_QO_PROP_BATCH=1` unions ordinary NF4 conclusions by target node during
  one drain wave, then applies each distinct literal once in stable order. KPSet
  inverse-edge containment checks remain eager.
- `KM_HT_QO_EDGESET=1` adds an exact hash membership index for edges. The
  existing adjacency vectors remain authoritative and retain their traversal
  order; the index only replaces the linear duplicate scan in `add_edge`.

The experimental direct role-inclusion shortcut was removed before integration.
It was unnecessary for the speedup and introduced extra risk around KPSet's
inverse-edge checks. `cargo check`, all 90 hypertableau tests, all 24 routing
tests, and all 110 orchestration tests pass. The focused fixpoint test compares
the eager implementation with both improvements active, including a downstream
consequence triggered by a batched conclusion.

IBEX job `49886242` compared control and optimized runs from the same native
binary (`0f18bf3f640c9af7000633686064e56ebabbdf33552288aacddb25b5ad9673ba`)
under the 240-second, 20-GiB production contract. Both tasks emitted exactly two
result rows and a `DONE` marker.

| ontology | control wall / peak | batched + indexed wall / peak | exact result |
| --- | ---: | ---: | --- |
| 7581 | 21.1071 s / 4,321.71 MiB | 20.2926 s / 4,334.55 MiB | 1,246,911 subsumptions, signature identical |
| 15098 | 0.1645 s / 32.72 MiB | 0.1630 s / 32.41 MiB | 951 subsumptions, signature identical |

On the forced 1194 cardinality-aware QO/KPSet input, the same two improvements
let the deterministic precompute reach its fixpoint instead of timing out:

- precompute: 185.627 seconds;
- total wall: 192.56 seconds;
- peak RSS: 4,011,316 KiB;
- 80,557 nodes and about 21,019,012 stored edges;
- 483,811 parked disjunctions remained;
- all 70,231 queried concepts were affected by the unresolved residue.

The route then deferred correctly with zero output. Cardinality checks recorded
23,026,819 KPSet misses, 38,521 insufficient nodes, and 23,944 Eq-head defers.
This is a substantial throughput improvement, but not a closure: automatic
coverage remains 591/592. The next target is an exact bulk treatment of the
cardinality and covering-disjunction residue after this now-bounded precompute.

The existing `KM_HT_QO_CARDMERGE=1` option does not reduce this residue. A
production-bounded replay reached the same fixpoint in 182.067 seconds and
recorded `cardmerge_done=0`: all 23,944 Eq deferrals bind non-filler nodes, which
the content-shared filler merge correctly refuses to conflate. A second replay
combined separate creation-role fillers (`KM_HT_QO_SAT=1`) with `CARDMERGE`,
batching, and the edge index. It still timed out with 186,244 nodes, 1,117,473
parked disjunctions, 2.82 million literal events, and 2.69 million edge events
queued at 233 seconds. Both runs emitted zero output.

The complete source-bound automatic sweep at commit `f39a2fd` is IBEX job
`49886711`. Its audit verifies 592 final/checkpoint pairs, 591 successful rows,
one fail-closed 1194 error, and zero semantic differences from the certified
`02a563f` sweep. Full provenance and the per-ontology table are in
[`../2026-08-02-f39a2fd-auto/`](../2026-08-02-f39a2fd-auto/README.md).
