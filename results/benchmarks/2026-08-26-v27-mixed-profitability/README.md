# v27 mixed-route profitability

Source capsule SHA-256: `c41ce9ba2658c7f9a12983db15063402ef82bdc5be400143b21663afba1de43b`

Binary SHA-256: `a6a910fc5fc862257b91f5e14bb587758733a2bf7e91b68ef10eec2d65ca88f1`

IBEX root: `/ibex/scratch/hohndor/km/v27-mixed-profitability-20260826`

The mixed union/intersection/nominal extension activates only for sources of
at least 64 MiB. Existing sparse-Horn routes keep their lower thresholds. This
restores ORE4604 to `production_all` at about 10.5 s while retaining ORE15803's
exact `flat_nf1` result at about 1.33 s. Job `50880737` ran three alternating
repetitions per ontology; all 12 outputs were byte-identical to v20.

The 592-ontology release-candidate sweep uses the hash-, CPU-, harness-, and
checkpoint-guarded wrapper in `ibex_full_sweep.sbatch`. Batch array `50880887`
was cancelled before any task started when a matching Gold 6248 node became
available in the debug partition. Replacement array `50881077` runs one
ontology at a time on `gpu510-32`; its first eight terminal result/profile/
checkpoint triples all carried the pinned binary hash and CPU model and had
zero behavioral differences from v20. The single-task throttle prevents
concurrent result writes and the checkpoint contract supports a clean resume.
After index 30, the untouched range was split without overlap: debug array
`50881077` owns indices 0–299 and batch array `50881242` owns indices 300–591.
Both use the same wrapper, binary, CPU constraint, and output contract.

## Completed sweep

Jobs `50881077` and `50881242` completed their disjoint ranges with 592
profiles, 592 terminal ontology records, no temporary files, and no remaining
Slurm tasks. The strict v27-v20 audit found 591 successful classifications and
the same fail-closed ORE1194 error in both arms, with no behavioral difference.
Five route selections changed: 12528, 15803, 5519, 6223, and 6477.

| Metric over 591 correct completions | v20 | v27 | Change |
|---|---:|---:|---:|
| Mean wall (s) | 1.562004 | 1.421802 | -0.140201 |
| Median wall (s) | 0.1348 | 0.1315 | -0.0033 |
| Mean peak RSS (MiB) | 231.032 | 225.454 | -5.578 |
| Median peak RSS (MiB) | 26.65 | 26.80 | +0.15 |

The aggregate release auditor passed all mean and median wall/RSS comparisons
against ELK, HermiT, Konclude, and strict Sequoia. The per-ontology v1.2 audit
does not pass: of 589 ontologies with an admissible external target, v27 wins
both metrics on 438, memory only on 61, wall only on 12, and neither on 78.
Ontologies 10860, 1194, and 4669 remain unadjudicated for that stricter gate.

This v27 binary is the pre-versioning candidate. A v1.1.0 release must use a
separately hash-bound final binary and may not inherit this binary identity by
assertion.
