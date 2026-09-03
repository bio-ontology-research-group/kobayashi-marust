# Compact nominal hypertableau scheduling

ORE 5184 already selected the complete `ht_general` probe through the automatic
`certified_nominals` route.  The default hypertableau fan-out, however, spent
more time and memory on worker setup than this compact 825-clause ontology could
amortize.  This change preserves an explicit `KM_HT_PAR` measurement request
across recursive route application and automatically uses four workers for a
tightly bounded source-feature family.

The gate requires a typed object ABox, 300--1,000 logical axioms, 50--500 ABox
axioms, 100--500 classes, 32--100 object properties, concept depth 2--4, and at
most 2,000 clauses.  It also requires inverse roles, transitivity, cardinality,
and nominals, while excluding qualified cardinality, datatypes, complex
subroles, and the universal role.  Projection over all 592 retained profiles
admits exactly ORE 5184.

The first serial experiment was invalid because route normalization cleared the
requested worker count.  After fixing request propagation, a 50-run panel in
IBEX array `51255664` produced ten correct, signature-identical repetitions for
each worker count:

| worker setting | median wall (s) | median peak RSS (MiB) |
|---|---:|---:|
| automatic/default | 0.0661 | 36.41 |
| 1 | 0.1065 | **10.465** |
| 2 | 0.0768 | 11.58 |
| 4 | 0.0483 | 15.46 |
| 8 | **0.0481** | 24.045 |

Four workers retain essentially the eight-worker wall time with substantially
lower memory.  IBEX build job `51255806` then built the production gate from
source archive SHA-256
`428da8e971da488504a48dd604e80a893fcbef846714149e4aa12ce15584b935`.
The resulting binary has SHA-256
`6fa5a55f78b4b7017ca31eb3ddac6ae64e2066604b5f6259dabbf7b56c0e9b53`.

Automatic-only confirmation array `51255851` produced exactly 10 results, 10
checkpoints, 10 scheduler outputs, and 10 completion markers, with no failure
artifacts.  All repetitions returned `status=ok`, selected `ht_general`, matched
the retained gold result, and shared signature SHA-256
`143e732f871ebc460a396f90684b0f500244eb5620173e0cc45115a9d4cc3f98`.

| automatic production gate | median | range |
|---|---:|---:|
| wall time (s) | **0.04955** | 0.0477--0.0798 |
| peak RSS (MiB) | **15.305** | 8.75--15.89 |
| best external target | 0.0711 | 34.68 |

The medians strictly beat both external targets, so ORE 5184 raises the current
evidence-composite score from 514/589 to **515/589** and reduces the residual
set from 75 to 74.  The raw results and scheduler logs are archived under
`.work/artifacts/v14-ht-par-request/ibex-confirm-v3/`; its checked `SHA256SUMS`
manifest covers all 30 archived job files.

This is a scheduling-only change.  The same complete hypertableau jobs run and
the same independently checked taxonomy is published; no calculus rule,
ordering, redundancy condition, or derived fixpoint changes.  Lean
re-certification is therefore not due.
