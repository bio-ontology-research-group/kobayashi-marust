# Compact datatype hypertableau scheduling

ORE 9635 selects the complete `ht_general` probe through the automatic nominal
route. A worker-count panel showed that three workers meet its unusually tight
latency and memory limits: the manual three-worker arm produced ten correct,
signature-identical runs with medians of 0.0801 seconds and 13.005 MiB, versus
external targets of 0.1044 seconds and 14.38 MiB.

The resulting source-profile gate requires a typed object ABox, 100--250
logical axioms, 1--10 ABox axioms, 64--128 classes, 16--32 object properties,
1--10 data properties, concept depth 2--3, at most 600 normalized clauses when
that statistic is available, has-value restrictions, and a role assertion. It
also requires datatypes, inverse roles, transitivity, and cardinality while
excluding nominals and qualified cardinality. Automatic source routing runs
before normalized clause counts are populated, so the clause constraint is an
upper fence rather than a nonzero lower fence.

IBEX build job `51256551` built commits `174b9fc` and `4f039e9` from source
archive SHA-256
`51b58af2f1a7b31dadf6677517c07aab0538f29ebf072116d47ebc3c2bfd387c`.
The deployed binary has SHA-256
`ce32444e97cc5ba70681cfc6f212d033be5ac210bb88596c26da0c3cbfad714d`.

Automatic-only IBEX array `51256644` then ran the production binary ten times
without a `KM_HT_PAR` override. It produced exactly ten results, ten
checkpoints, ten completion markers, and no failure artifacts. Every run
returned `status=ok`, selected `ht_general`, matched the retained Konclude gold
result, and produced signature SHA-256
`05ec2b7af10ca0553fabdf219377baf556044a8a0e3b71215555cfc44d511b13`.

| automatic production gate | median | range | external target |
|---|---:|---:|---:|
| wall time (s) | **0.0795** | 0.0761--0.0826 | 0.1044 |
| peak RSS (MiB) | **12.845** | 12.37--14.06 | 14.38 |

The medians strictly beat both external targets. ORE 9635 therefore raises the
evidence-composite score from 516/589 to **517/589** and reduces the residual
set from 73 to 72.

This is a scheduling-only change. It runs the same complete hypertableau jobs
and publishes the same independently checked taxonomy; no calculus rule,
ordering, redundancy condition, or derived fixpoint changes. Lean
re-certification is therefore not due. The build record, raw results, and logs
are archived under `.work/artifacts/v14-9635-three-worker/`; its verified
`SHA256SUMS` manifest covers all 34 files.
