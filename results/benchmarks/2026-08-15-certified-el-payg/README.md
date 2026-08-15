# Certified EL pay-as-needed fallback evidence

Release candidate `19eb42e` defers production-fallback serialization for
certified EL routes. The candidate binary is
`645e79b99626db2fe125bfbc3df003355593d206117ebdb5d0a225bdc910afeb`.
The v0.2.32 baseline binary is
`e14949a66e6029fc215d22cdf5bee55b0caf73ff572bb0acd9dba0b5412a7d3a`.

## Policy selection

The initial broad subprocess policy was rejected after three isolated pairs on
each giant showed that compact handoff improved ORE16744 but slowed ORE8737.
Job `50547402` measured ORE16744 at 63.6246 versus 60.2873 seconds and
5,669.26 versus 3,572.49 MiB, while ORE8737 measured 73.7915 versus 76.6120
seconds. The released policy therefore keeps the established certified-route
JSON handoff below 512 MiB of source text. This workload threshold selects the
576,729,915-byte ORE16744 source but not the 472,349,807-byte ORE8737 source.

Focused job `50547497` validates the narrowed source on ORE7246, ORE8737,
ORE16744, ORE15803, and ORE6682. All ten records match in status, route,
verdict, answer, and full-IRI signature. Their summed wall falls by 3.3370
seconds. ORE16744 falls from 62.5056 to 59.3677 seconds and from 5,670.49 to
3,574.79 MiB in that gate.

## Full ORE pair

Order-balanced same-node job `50547528` ran both binaries over all 592 ORE
ontologies on exclusive Intel Xeon Gold 6248 nodes. It contains exactly 1,184
terminal JSON records, 1,184 matching checkpoints, 592 pair-completion markers,
and no temporary output. Each arm has 591 successful classifications and the
expected fail-closed ORE1194 result. Comparisons cover status, verdict,
consistency, selected route, solved state, requested route, answer counts,
missing and extra counts, and collision-sensitive full-IRI signatures. Every
comparison count is zero.

| arm | wall mean s | wall median s | peak mean MiB | peak median MiB | wall sum s |
|---|---:|---:|---:|---:|---:|
| v0.2.32 baseline | 3.450999 | 0.1627 | 424.2426 | 35.05 | 2,039.5402 |
| candidate | 3.434868 | 0.1622 | 420.4032 | 34.39 | 2,030.0067 |

The paired wall reduction sums to 9.5335 seconds. Summed process-tree peak RSS
falls by 2,269.09 MiB. The released change accounts for the deterministic
2,098.17-MiB reduction on ORE16744; smaller per-ontology RSS movements are not
claimed individually.

## Release tests

The complete release-mode suite passes 2,005 library tests with eight ignored
tests and every integration test. This includes all routing tests and
`issue_3_soundness`, which confirms that nominal enumeration plus explicit
difference reports the pigeonhole ontology inconsistent.
