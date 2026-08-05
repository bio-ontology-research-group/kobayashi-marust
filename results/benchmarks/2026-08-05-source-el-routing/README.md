# v0.2.6 source-certified EL routing

Candidate commit `3938b30` routes large, source-certified OWL EL terminologies
directly to the atomic `elc` completion worker.  These ontologies previously
used `production_all`, which ran the absorbed frontend and duplicate plain and
absorbed CB classifications even though normalized EL completion was already
authoritative.

The source predicate excludes ABox assertions and every non-EL constructor. It
allows the EL TBox and RBox constructors handled by `elc`. Worker-level
normalization remains the final acceptance check, so the route fails closed if
the source profile and normalized clauses disagree.

## Source binding

- Candidate commit: `3938b30`
- Candidate binary SHA-256:
  `7ac98a33a26579d9a2e3abaf95dfd8fba44e2dc842db1d12ce65144dd1a5c0f1`
- Baseline release: `v0.2.5` at commit `408dee4`
- Baseline binary SHA-256:
  `4812d656144b4b822523acf97d6500238391aff5912078868535604f1aef22b1`
- CPU: Intel Xeon Gold 6248 at 2.50 GHz
- Per-classification limits: 240 seconds and 20 GiB

## Paired panel

Slurm job `50075107` ran 18 ontology pairs on exclusive, identically
constrained nodes. Even and odd array tasks reversed arm order. The harness
required the baseline route to be `production_all`, the candidate route to be
`elc`, exact binary hashes, terminal checkpoints, `match` verdicts, and equality
of all semantic result fields.

All 18 pairs passed:

| Metric | v0.2.5 | Candidate | Change |
|---|---:|---:|---:|
| Mean wall time | 13.7085 s | 8.8941 s | -35.1% |
| Median wall time | 6.8760 s | 3.9290 s | -42.9% |
| Mean peak RSS | 2,370.18 MiB | 886.28 MiB | -62.6% |
| Median peak RSS | 1,702.38 MiB | 357.85 MiB | -79.0% |

`paired-results.tsv` contains every arm measurement, and
`panel-summary.json` is the strict aggregate.

## Full sweep

The strict 592-ontology sweep uses `ibex_sweep_3938b30.sbatch`. It validates
the CPU model, candidate binary, route profiles, terminal checkpoints, result
set, collision-safe fingerprints, and absence of temporary files. The final
comparison additionally requires all semantic fields to equal v0.2.5 and
exactly 106 intended `production_all -> elc` route changes.

Initial job `50075264` failed closed before classification because the candidate
deployment lacked the benchmark harness modules. Its pending tasks were
cancelled. The byte-identical v0.2.5 harness modules were copied into the
candidate root and import-checked before corrected job `50075668` was
submitted. That batch job and later middle-range job `50076513` remained
pending and were cancelled in favor of the fixed-hardware debug arrays. No
result from the failed deployment is accepted by the aggregator.

The corrected sweep resumed across jobs `50075757`, `50076165`, `50077178`,
and `50078177`. Job `50079043` was submitted to the batch partition while the
debug tail was progressing, remained pending, and was cancelled before it ran
to avoid duplicate writers. The accepted result set contains exactly 592
profiles, results, and terminal checkpoints, no temporary files, one CPU model,
and one candidate binary.

`aggregate_strict.py` and `compare_full_sweeps.py` both pass:

| Metric | v0.2.5 | v0.2.6 candidate | Change |
|---|---:|---:|---:|
| Mean wall time | 5.7632 s | 5.1787 s | -10.14% |
| Median wall time | 0.2489 s | 0.2467 s | -0.88% |
| Mean peak RSS | 780.74 MiB | 720.08 MiB | -7.77% |
| Median peak RSS | 42.76 MiB | 42.02 MiB | -1.73% |

The final corpus result is 591 `status=ok` and one fail-closed error for
ORE1194. All 592 semantic records equal v0.2.5. Exactly 106 ontologies move
from `production_all` to `elc`; no other route changes. The retained evidence
includes `automatic-results.tsv`, `summary.json`, `comparison-v025.json`, the
paired panel, all aggregators, and the source-bound Slurm harnesses.
