# Fresh ORE all-route and all-reasoner panel

This directory contains a fresh, source-bound run over all 592 ORE 2015
ontologies. One IBEX Slurm array task owns one ontology and runs every one of
the 66 procedures sequentially under the same limits. The run therefore
contains 39,072 independently limited reasoner measurements, with no reuse of
an unreproducible historical binary.

The prominent repository table and the table below are generated from
[`headline-summary.tsv`](headline-summary.tsv). The complete 66-procedure
summary is [`full-panel-summary.tsv`](full-panel-summary.tsv), and the full
39,072-row data set is
[`full-panel-results.tsv.gz`](full-panel-results.tsv.gz).

## Headline comparison

| procedure | `sound=yes` | `complete=yes` | both yes | `status=ok` | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| **KM, preselected current routes** | **575** | **575** | **575** | 583 | 5.0168 | 0.2336 | 643.16 | 37.12 |
| KM, oracle-selected current route | 579 | 579 | 579 | 579 | 3.4477 | 0.1893 | 385.43 | 29.72 |
| **KM, `--route auto`** | **562** | **562** | **562** | 571 | 5.3000 | 0.2807 | 789.92 | 44.43 |
| Konclude | 587 | 585 | 585 | 589 | 3.2657 | 0.2813 | 558.09 | 76.53 |
| HermiT | 549 | 550 | 549 | 558 | 13.1261 | 1.8868 | 1,330.56 | 714.01 |
| ELK | 576 | 529 | 529 | 592 | 1.7449 | 0.7466 | 505.86 | 234.11 |
| RustDL, complete mode | 542 | 525 | 525 | 551 | 4.9596 | 0.1928 | 299.49 | 49.80 |
| Sequoia, strict mode | 340 | 339 | 339 | 341 | 7.3405 | 2.5371 | 2,197.31 | 536.15 |

`ok metrics` are calculated only over `status=ok` rows. This historical
benchmark convention is reported beside the number of such rows, so a
reasoner cannot hide failures behind a fast successful subset. The detailed
summary also reports time and memory over every measured attempt, including
timeouts, memory exits, unsupported inputs, and reasoner errors.

The KM documented-selection row is fixed before looking at this panel: it uses
the route previously recorded for each ontology and has no route for an
unclosed ontology. The `km_best_current_route` row in the headline artifact is
an explicitly labelled oracle upper bound. It chooses the fastest empirically
correct current route after seeing all results and is not a deployable router.

The earlier source-bound ledger records 589 accepted answers, but that total
spans the current, historical, and candidate source revisions named in its
rows. This fresh current-revision run does not reproduce 589. Of the
preselected routes, five time out (`7499`, `9540`, `9635`, `10702`, and
`15672`), `10621` is rejected as unsupported, eight successful answers have
unresolved full-IRI correctness, and the three unclosed ontologies have no
selected route. The prior ledger remains in the first 50 columns of
[`ontology-route-performance.tsv`](ontology-route-performance.tsv), while the
fresh `panel_*` columns record what the frozen current binary actually did.

### Does plain `km classify` reproduce the routed coverage?

No. Plain `km classify ONTOLOGY` is `--route auto`; it returns 571 parseable
answers and 562 empirically sound-and-complete answers. Seventeen additional
ontologies have a validated current explicit route in this panel:

| ontology | validated current invocation |
|---|---|
| 1481, 1579, 3377, 3560, 5107, 6477, 6999, 7914, 9654, 10908, 15803, 15846 | `km classify --route production_all ONTOLOGY` |
| 6934, 7499, 9635, 10702, 15672 | the `htforce_race` environment from `full-panel-contract.tsv`, with `km classify --route manual ONTOLOGY` |

Those recipes raise the validated current-revision union to 579. They were
selected after observing the panel, so they are reproducible per-ontology
recipes, not evidence that the automatic router would have chosen them. The
faster validated arm for every ontology is in `panel_best_km_arm`; its exact
command environment and all alternatives are in `panel_all_procedures_json`.
The 13 rows without a validated current answer are `443`, `1194`, `3524`,
`4669`, `6720`, `7052`, `8941`, `9540`, `10621`, `10860`, `13912`, `15288`,
and `15703`. Eight of these returned answers whose full-IRI correctness is
unknown; that is different from a demonstrated wrong answer.

## What ran

[`full-panel-contract.tsv`](full-panel-contract.tsv) is the exact procedure
contract:

| family | procedures | meaning |
|---|---:|---|
| Current KM public routes | 35 | `auto`, `manual`, and every name printed by the frozen `km routes` command |
| Documented KM solution environments | 8 | every exact nonstandard environment selected by at least one row in the prior source-bound 589-route ledger |
| Retained optimization stages | 11 | chronological source snapshots for the active July optimization stack |
| Clean optimization ablations | 5 | frozen current main with exactly one named optimization commit reversed |
| Primary external baselines | 5 | Konclude, HermiT, ELK, RustDL with internal timeouts disabled, and strict Sequoia |
| Supplemental baseline modes | 2 | released-default RustDL and Sequoia with unsupported features ignored |
| **Total** | **66** | **39,072 measurements over 592 ontologies** |

Here, “KM configuration” means a supported named configuration printed by
`km routes`, plus every exact nonstandard environment in the accepted route
ledger. The captured public list is
[`provenance/km-routes.txt`](provenance/km-routes.txt), and the contract
exercises each of those configurations. Internal
`KM_*` reads used for executable paths, resource caps, dump/trace/watch
diagnostics, one-ontology probes, and abandoned experimental gates are not
additional supported reasoner configurations and are not presented as such.
There is no Cartesian product of raw environment variables: most combinations
have no defined semantics, and treating them as reasoner modes would create
misleading soundness claims.

The primary revisions are:

- KM `8c731f43b3c8a277f5fd7a25687e35afb4c4045e`;
- Konclude `0002e80635403960a7df5d93bd0e8f994d4952d0`
  (`v0.7.0-1138`);
- HermiT `1.4.6.519-SNAPSHOT`;
- ELK `0.6.0`;
- [RustDL](https://github.com/MaastrichtU-IDS/rustdl)
  `8c2bb1bf43d936e56d77ae439c04d2feb3f6ebf5` (`0.3.31`); and
- [Sequoia](https://github.com/andrewdbate/Sequoia)
  `c5248ec7be302efc850cf07ab30a0ea651db81b6` (`0.6.1-alpha`).

RustDL's primary command uses `--pair-timeout-ms 0 --global-timeout-ms 0`,
which disables its internal under-approximation budgets. Its released default
is retained as a separate arm. Sequoia's strict mode is primary; the
`--ignoreUnsupportedFeatures` mode is retained separately and is never
silently substituted for strict reasoning.

The repository contains no Bloom-filter implementation or public Bloom flag at
the frozen revision, so the panel does not invent a Bloom result. It does
measure the active exact hash-based changes, including context-clause hash
reuse, content-hash context-core interning, and incremental removal of
back-subsumed clauses, both as chronological stages and as clean current-main
ablations. The large seeded-closure sharing experiment at `feb0cc6` had already
been rejected and reverted after failing its target ontology; it is historical
diagnostic evidence, not a current optimization or configuration option.

## Limits and measurement

Every procedure receives:

- 240 seconds wall time;
- 20 GiB summed process-tree RSS;
- 16 allocated CPU cores; and
- an Intel Xeon Gold 6248 node selected by the Slurm constraint.

The watchdog samples the complete process tree every 20 ms and takes the
maximum of that value and GNU time's direct-child peak. The retained field is
named `peak_mb` for compatibility, but its unit is MiB. Timing includes input
parsing, reasoning, and taxonomy serialization. Correctness fingerprinting
runs after the timed reasoner and is not included in its wall or memory metric.
Procedure order rotates by ontology to distribute order and cache effects.

This is one run per ontology and procedure, not a repeated microbenchmark.
Small timing differences should not be interpreted as statistical evidence.

### Full-IRI-only scoring for 3524 and 15703

Ontologies 3524 and 15703 generate class IRIs that contain another full IRI
after a slash. Distinct classes therefore collapse to the same value under the
legacy ORE local-name projection. On a 239 MB KM taxonomy, constructing that
lossy projected closure exceeded 235 GiB RSS before completing one arm. This
was untimed post-processing, not reasoner memory, but it prevented the
per-ontology task from publishing its complete 66-row result.

Every arm for these two ontologies is rerun by
[`ibex_full_panel_giant_array.sbatch`](ibex_full_panel_giant_array.sbatch) with
[`full_panel_run_one_fulliri_only.py`](full_panel_run_one_fulliri_only.py).
The supplemental runner reuses the hash-pinned primary runner for command
execution, limits, timing, and process-tree RSS measurement. It skips only the
non-injective local-name projection and passes every successful taxonomy to
the exact SCC-and-bitset full-IRI fingerprinter. An isolated probe completed
the 1,604,386-pair taxonomy in 7.4 seconds at 902 MiB peak RSS. The final
aggregator accepts the supplemental runner only for these two ontology names,
requires its base-runner hash on every row, and rejects any successful row
without a complete full-IRI fingerprint.

## Empirical soundness and completeness

The fields concern the named-class taxonomy on this corpus. They are empirical
judgments against the cited reference or adjudication, not a proof about every
OWL input.

- `sound=yes, complete=yes` means the answer exactly matches the applicable
  full-IRI reference, corrected frozen signature, or explicit inconsistency
  adjudication.
- A strict subset is `sound=yes, complete=no`; a strict superset is
  `sound=no, complete=yes`; and differences in both directions are `no/no`.
- `unknown` means an answer exists but available evidence cannot decide the
  property.
- `not_applicable` means there is no parseable classification answer whose
  soundness can be assessed. Such a row has `complete=no`.

The normal oracle set contains 587 frozen Konclude signatures. The scorer also
applies the documented correction for ontology 13503 and independent
inconsistency adjudications for 2669 and 15516. A same-job full-IRI Konclude
fingerprint is used only where the frozen signature establishes a trusted
reference.

Ontology 4669 has no authoritative complete taxonomy. Its overlay checks every
successful arm against 64 independently satisfiable named classes from 67
hash-pinned HermiT query records. Declaring the ontology inconsistent or
declaring any witness unsatisfiable proves that result unsound. An unrefuted
answer remains `sound=unknown, complete=unknown`; absence of a counterexample
does not create a solve claim. See
[`ore-4669-targeted-soundness.tsv`](ore-4669-targeted-soundness.tsv) and
[`4669-targeted-satisfiability/`](4669-targeted-satisfiability/).

## Optimization effects

The clean current-main ablations found no sound-and-complete coverage change.
The deltas below are `current main - ablated main`; negative time or memory is
an improvement from retaining the optimization.

| optimization retained in current main | both-yes delta | paired rows | wall mean delta s | wall median delta s | peak mean delta MiB | peak median delta MiB |
|---|---:|---:|---:|---:|---:|---:|
| result extraction | 0 | 574 | -0.0350 | -0.0001 | -7.39 | -0.31 |
| one-way subsumption | 0 | 574 | -0.0404 | 0.0000 | +2.05 | 0.00 |
| context-clause hash reuse | 0 | 574 | -0.0551 | 0.0000 | +2.39 | 0.00 |
| context-core hash interning | 0 | 574 | -0.0516 | +0.0002 | +1.28 | 0.00 |
| incremental back-subsumption removal | 0 | 574 | -0.0710 | 0.0000 | +2.55 | 0.00 |

[`optimization-effects.tsv`](optimization-effects.tsv) separates two kinds of
comparison. Chronological source stages include all changes between adjacent
revisions and are therefore descriptive, not causal. A clean ablation compares
frozen current main against current main with exactly one optimization commit
reversed. Paired time and memory deltas use only ontologies for which both arms
return an empirically sound-and-complete answer.

## Main artifacts

- [`ontology-route-performance.tsv`](ontology-route-performance.tsv): the
  592-row ontology ledger requested by the project. It retains the prior route
  evidence, adds fresh headline and documented-route columns, and embeds a
  compact 66-procedure JSON record in every ontology row.
- [`full-panel-results.tsv.gz`](full-panel-results.tsv.gz): all 39,072
  normalized measurements, including command, environment, hashes, limits,
  resource metrics, correctness fields, and Slurm identity.
- [`full-panel-raw-results.jsonl.gz`](full-panel-raw-results.jsonl.gz): the
  exact pre-aggregation JSON rows concatenated in ontology-list order.
- [`full-panel-summary.tsv`](full-panel-summary.tsv): all-arm status,
  correctness, successful-run metrics, and all-attempt metrics.
- [`headline-summary.tsv`](headline-summary.tsv): documented KM selection,
  oracle-best current KM route, KM auto, and the primary baselines.
- [`procedure-runtime-identities.tsv`](procedure-runtime-identities.tsv): one
  binary/runtime identity row per procedure.
- [`full-panel-receipt.json`](full-panel-receipt.json): hashes and invariants
  validated by the final IBEX aggregation.
- [`full-panel-generated-files.sha256`](full-panel-generated-files.sha256):
  hashes of every generated aggregate.
- [`result-files.sha256`](result-files.sha256): hashes of the generated
  aggregates, retained pre-panel artifacts, executable verification record,
  and Slurm accounting export.
- [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md): an executable verification
  transcript for hashes, row counts, procedure counts, and receipt invariants.
- [`provenance/`](provenance/): exact build receipt, binary manifest, variant
  build receipts, reverse patches, frozen driver manifest, and Slurm
  accounting.
- [`ontology-route-performance.pre-panel.tsv`](ontology-route-performance.pre-panel.tsv):
  the previous metadata-joined table, retained byte-for-byte instead of being
  overwritten without history.

## Reproduction

The scripts are intentionally specific to the documented IBEX layout. From
this directory on IBEX:

```sh
sbatch ibex_build_full_panel.sbatch

# Freeze these scripts plus ore_canon.py and tree_watchdog.py in one directory.
# The primary driver handles every ontology except the two collision cases.
primary_job=$(sbatch --parsable \
  --array=0-120,122-551,553-591%32 \
  ibex_full_panel_array.sbatch)

# Publish both supplemental tasks into the same run root.
supplemental_job=$(sbatch --parsable \
  --export=PANEL_RUN_ID="$primary_job" \
  ibex_full_panel_giant_array.sbatch)

# After every task completes, aggregate against the pre-panel table and the
# primary and supplemental driver manifests.
sbatch --dependency=afterany:"$primary_job":"$supplemental_job" \
  ibex_aggregate_full_panel.sbatch \
  "$primary_job" \
  /ibex/scratch/hohndor/km/full-panel-20260722/aggregation-input/ontology-route-performance.pre-panel.tsv \
  "/ibex/scratch/hohndor/km/full-panel-20260722/aggregate/$primary_job" \
  /ibex/scratch/hohndor/km/full-panel-20260722/drivers/sha256-44d2ae9644487047f87e0ae68e8246dedf863aceff4140620afdb0d175406b2c/driver-files.sha256 \
  /ibex/scratch/hohndor/km/full-panel-20260722/drivers/giant-sha256-05ceac2dbd0018a0e83467ce9d93d4dd68b60e570343ded5ef7aeb34e45f3e50/driver-files.sha256
```

The aggregator fails closed unless it finds exactly 592 ontologies, exactly 66
arms in contract order, 39,072 rows, one distinct Slurm task job per ontology,
the standard limits, one immutable identity per procedure, matching source and
gold hashes, complete full-IRI fingerprints for every successful answer, and
valid hashes for every frozen driver, binary, build receipt, variant receipt,
and ablation patch.

## Run provenance

| purpose | Slurm job | result |
|---|---:|---|
| Build 20 frozen binaries and variants | 49286975 | completed |
| Build full-IRI HermiT oracle | 49289827 | completed |
| Smoke tests | 49289828, 49289943, 49290162 | completed |
| Primary 592-ontology array | 49290191 | 590 ontology tasks published; the two collision cases were replaced below |
| Legacy collision diagnostics | 49309213, 49309218, 49309386, 49309785, 49309786 | diagnostic only; no published measurements |
| Exact full-IRI giant probe | 49310788 | completed; diagnostic only |
| Collision-safe tasks for 3524 and 15703 | 49311003, 49310988 | completed; 132 published measurements |
| Fail-closed aggregation | 49311162 | completed; 592 ontologies, 66 procedures, 39,072 measurements |

The compressed accounting export is
[`provenance/slurm-accounting.tsv.gz`](provenance/slurm-accounting.tsv.gz).
The final receipt binds the primary driver manifest
`44d2ae9644487047f87e0ae68e8246dedf863aceff4140620afdb0d175406b2c`,
the supplemental driver manifest
`52fe0eefc51fb578deb99fd20996a357421085ff8921a35dd553926d9c2a3cb7`,
and aggregation program
`5c8f3dcea594534d470e929002c5ee43f3aa0244686070f64d4ec3b6139389b1`.

Failed setup or smoke jobs are documented because they did not contribute a
measurement. The published panel uses only the final smoke-validated driver,
the successful build receipt, and the completed full array.
