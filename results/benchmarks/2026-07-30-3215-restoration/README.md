# 2026-07-30 ore_ont_3215 restoration

Current-source evidence that `ore_ont_3215.owl` classifies sound and complete
inside the benchmark contract (240 seconds, 20 GiB), and the audit that found
why it had stopped doing so.

## Audit of the 2026-07-27 evidence

`results/benchmarks/2026-07-27-solving-routes-full-sweep/` reports
`ore_ont_3215.owl` as a timeout on all 44 current-main KM arms, including
`km_solution_kpset_barrier`, which replays the environment recorded in
`docs/SOLVE-3215.md`. Konclude answers the same ontology in 64.5 s at 9,702 MB.

The historical supplement rules out a regression against the 2026-07-13
closure. Exclusive job 49522590 reran the source-bound closure binary identity
alone on a `cpu_intel_gold_6248` node and it also timed out, at 240.03 s and
8,398 MB.

Rebuilding `91db9fb` (the closure) and current main from source and running
both on one host with the documented environment confirms this directly:

| Binary | HT worker | Total | Peak RSS | Signature |
|---|---:|---:|---:|---|
| `91db9fb` | 397.7 s | 411.7 s | 5,353,720 KB | exact, 3,923,171 pairs |
| current main | 385.8 s | 385.8 s | 5,536,200 KB | exact, 3,923,171 pairs |

The historical peak RSS reproduces the recorded 5,351,252 KB to within 0.05%,
so the rebuild performs the same work. Both binaries remain exactly equal to
Konclude gold. The KPSet barrier, the saturation labels, and the zero-pairwise
verification are all intact; the ontology had lost margin, not correctness.

## Phase attribution

`phase-breakdown-before.txt` is the `KM_BRIDGE_PROGRESS` trace of current main
before the fix, with the per-phase timers this change adds:

| Phase | Time |
|---|---:|
| Frontend + clause hand-off | 6.9 s |
| Bridge environment (trigger absorption) | 1.1 s |
| Saturation seeds + loop + extraction | 34.4 s |
| Satisfiability phase (18,323 completion jobs) | 398.4 s |
| KPSet barrier | 0.8 s |
| Verification (0 pairwise subsumption tests) | 12.7 s |

Saturation answers 36,650 subjects directly and hands the completion path the
same 18,323-subject residue the instrumented Konclude trace reports. The whole
cost is the satisfiability phase.

## The defect

`getenv-stack-frames.txt` aggregates 25 stack samples of that phase. Nine of
them, over a third, sit in `std::env::var` inside the completion rule bodies:
`insert_concepts_to_individual_concept_set`,
`add_concept_to_individual{,_skip_and_processing}`,
`create_successor_individual` and `try_expansion_from_saturated_data`, plus
`ProcessContext::ht_check_dangling_satellites` on every `pop_branch_epoch`.
These are CLI-only diagnostic gates read once per concept addition.
`std::env::var` takes the process-wide environment lock and allocates a
`String` on every call.

`docs/SOLVE-3215.md` section 2 removed exactly this cost from the saturation
hot path in 2026-07-13, for this ontology. The completion layer never received
the same treatment.

## The fix

`engine/src/konclude_ht/completion/mod.rs` owns cached accessors for each
setting, from the same `OnceLock` pattern `saturation/mod.rs` uses, and all 50
inline reads route through them. No route bundle, orchestrator path, or test
sets any of these variables, so every accessor returns exactly what the inline
call returned and every diagnostic keeps working. No rule fires differently and
no derived set moves.

## Result

IBEX job 49624875, exclusive `cpu_intel_gold_6248` node, 16 CPUs, 240 s and
20 GiB per arm, signature compared against
`konclude__ore_ont_3215.owl.sig.gz`:

| Route | Wall | Peak RSS | Signature |
|---|---:|---:|---|
| `ht_bridge` | 162.2 s | 5,560,592 KB | exact, 3,923,171 pairs |
| `auto` (production) | 161.9 s | 5,500,480 KB | exact, 3,923,171 pairs |

Three independent builds of the same node type agree: job 49622066 measured
160.4 s and 163.1 s, job 49622766 measured 161.4 s and 161.6 s, and job
49623951 measured 165.2 s and 169.5 s.

Zero missing, zero extra, no unsatisfiable-class difference, same consistency
result. On the workstation the isolated route drops from 385.8 s to 215.4 s at
5,543,772 KB, also exact.

## Regression panel

Job 49625943 reruns the documented bridge-closed terminologies and the
KPSet-barrier correctness cases on the production `auto` route under the same
240 s / 20 GiB contract, against the frozen Konclude gold signatures. The
2026-07-27 `km_route_auto` column is the baseline this change has to hold.

<PANEL>

## Reproduction

- `ibex_3215_cycle9.sbatch` builds this revision on IBEX and measures both
  routes on `ore_ont_3215.owl` against gold.
- `ibex_family_final.sbatch` runs the regression panel.
- `kmsig.py` compares a `km classify` JSON output against a gold `.sig.gz`. It
  canonicalises the KM side through the repository's own `ore_canon.py`
  (`../2026-07-27-solving-routes-full-sweep/ore_canon.py`), which condenses
  equivalence SCCs, closes the hierarchy transitively, and drops owl:Thing,
  owl:Nothing and unsatisfiable-class pairs. Comparing raw pairs instead
  reports spurious differences on ontologies with equivalences or
  unsatisfiable classes.
