# Intern repeated full IRIs in grouped JSON output

## Change

The JSON-only classification path now stores each distinct mapped full IRI once
as `Arc<str>` and reuses it across grouped taxonomy rows. Before processing the
taxonomy, it builds an ordered local-name-to-Arc table from the frontend IRI
map. Dense output therefore performs the same ordered local-name lookup as the
previous implementation and clones an Arc per pair, instead of allocating one
superclass `String` per pair or hashing a long full IRI per pair.

The public `Classification` API, `--lines`, explanation, mirror, routing, and
reasoning state are unchanged. The JSON serializer emits the same borrowed
strings in the same order, including duplicate pairs. This is an output
representation change and does not require Lean re-certification.

## Validation

The complete workstation release suite passed with 1,951 library tests, eight
ignored library tests, and every integration and documentation test passing.
Focused tests verify shared interning, grouped-vs-flat byte identity, and the
streaming-vs-allocating JSON contract.

Commit `abe2759` was archived with SHA-256
`48f7e547176ae88d8f309c10cfa8c29ae537ef7700a1f7a7c1016df5028feafa`.
IBEX build job `50036692` produced binary SHA-256
`94077acb317cd5bafbd47d0ddce3ef1d693b52ba8998f1418df5d4247e05155e`.
Paired job `50036693` ran on an exclusive Intel Xeon Gold 6248 node. Each run
wrote and hashed the complete 14,809,043-pair ORE9674 JSON result. The job
rejected binary mismatches, nonzero exits, malformed receipts, or output
differences.

| repetition | `229ad77` wall | candidate wall | `229ad77` peak KiB | candidate peak KiB |
|---:|---:|---:|---:|---:|
| 1 | 42.35 s | 42.27 s | 2,881,972 | 2,231,924 |
| 2 | 42.63 s | 42.23 s | 2,883,000 | 2,231,472 |
| 3 | 42.81 s | 42.04 s | 2,881,796 | 2,229,608 |
| **mean** | **42.597 s** | **42.180 s** | **2,882,256** | **2,231,001** |

Mean wall improved by 0.98%. Mean peak RSS fell by 651,255 KiB, about 636 MiB
or 22.60%. All six outputs had SHA-256
`152cdf0863750e3c94ac3faeb1764fe31a52935db73069bb48a5a8b6d2cd9184`.

An initial implementation at `2dc5e52` performed a full-IRI hash lookup for
every pair. It achieved the same memory reduction but increased mean wall by
1.25%, so it was not pushed. Precomputing the local-name-to-Arc table removed
that regression and produced the accepted result above.

The complete 592-ontology production sweep is queued behind the preceding
source-bound sweeps and remains pending.

## Reproduction

- [`ibex_build_abe2759.sbatch`](ibex_build_abe2759.sbatch) builds the accepted
  pinned source archive.
- [`ibex_9674_cached_pair.sbatch`](ibex_9674_cached_pair.sbatch) runs and checks
  the accepted alternating benchmark.
- [`ibex_build_2dc5e52.sbatch`](ibex_build_2dc5e52.sbatch) and
  [`ibex_9674_pair.sbatch`](ibex_9674_pair.sbatch) reproduce the rejected direct
  full-IRI-hash variant.
- The parameterized
  [`../2026-08-04-grouped-json-output/ibex_sweep_229ad77.sbatch`](../2026-08-04-grouped-json-output/ibex_sweep_229ad77.sbatch)
  is the production runner. The submitted arrays set `KM_SWEEP_ROOT`,
  `KM_SWEEP_ARM`, and `KM_SWEEP_LABEL` explicitly and override the Slurm output
  path, while the script's defaults exactly reproduce the `229ad77` sweep.
