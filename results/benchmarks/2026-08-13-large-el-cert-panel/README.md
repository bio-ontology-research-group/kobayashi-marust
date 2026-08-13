# Large extended-EL terminology routing panel

This experiment tests whether plain normalization plus KM's canonical-model
certificate can replace absorbed `production_all` on three large terminology
profiles that sit just outside the direct source-EL screen. The automatic route
retains `production_all` as an exact fallback on certificate refusal, worker
failure, or resource failure.

## Membership audit

The source predicate requires at least 400,000 logical and TBox axioms, no
ABox, no Boolean class constructors or cardinalities, no nominals, datatypes,
imports, or rules, and at least one inverse, symmetric, reflexive, or named
disjointness declaration. Applying it to the complete v0.2.8 set of 592
successful profiles admits exactly:

- `ore_ont_7246.owl`
- `ore_ont_8737.owl`
- `ore_ont_16744.owl`

## Same-node route panel

IBEX array job `50428118` ran `production_all`, `elc`, and `elc_cert`
sequentially per ontology on exclusive Intel Xeon Gold 6248 nodes under the
240-second and 20-GiB benchmark contract. Every successful alternative has the
same gold-matching signature as `production_all`.

| ontology | route | wall s | peak MiB | verdict |
|---|---|---:|---:|---|
| ORE7246 | `production_all` | 30.2069 | 10096.86 | match |
| ORE7246 | `elc_cert` | 21.0717 | 2027.22 | match |
| ORE8737 | `production_all` | 114.7924 | 9985.63 | match |
| ORE8737 | `elc_cert` | 94.9340 | 4925.23 | match |
| ORE16744 | `production_all` | 98.4855 | 11606.40 | match |
| ORE16744 | `elc_cert` | 72.7689 | 5687.01 | match |

Across these three inputs, `elc_cert` removes 54.9 seconds and 19,049 MiB of
summed peak RSS. If the automatic verification reproduces these results, the
expected 592-row mean reductions are about 0.093 seconds and 32.2 MiB.

`ibex_panel.sbatch` binds every run to binary
`1abb488945d16df5ba16ee6aa261b1a2aac356b2bfe183b256856c7e28fe9734`,
requires terminal checkpoints and exact route traces, and rejects differing
successful signatures. `panel-results/` contains all nine terminal records and
checkpoints.

## Automatic verification and full sweep

Candidate commit `d607ca7` was built natively on IBEX as binary
`c8e4c51a3535927f6785ea9d3356de6bd11f9ac9ab8a6edb4b3ca58e98b1f145`.
Automatic-route job `50428492` verifies all three inputs select
`certified_el_production`, complete, and match gold.

Strict array job `50428535` produced exactly 592 results, checkpoints, and
profiles with no temporary files. Comparison with v0.2.8 finds exactly the
three intended route transitions and zero semantic or coverage regressions.
The aggregate is 591 `status=ok`, mean wall 4.5733 seconds, median wall 0.2490
seconds, mean RSS 531.38 MiB, and median RSS 41.77 MiB. Compact evidence and
verifiers are stored under `full-sweep/`, `auto-results/`, and beside this file.
