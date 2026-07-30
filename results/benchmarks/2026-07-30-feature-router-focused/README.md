# Feature-routed independent ABox focused run

This focused IBEX run tests the source-only candidate gate for large,
independent class-assertion ABoxes. Pure-EL source profiles select `elc`, whose
worker independently verifies the normalized EL shape. Other candidates select
the atomic `ht_bridge` procedure: the native completion bridge must
independently certify the normalized input and return a complete answer, or
decline explicitly. It does not construct the nominal-aware CB fallback, whose
eager root-context materialization defeats ABox elision and can exhaust packed
`f(o)` terms.

The candidate ontologies are `3560`, `6477`, and `7914`. All three timed out
under the prior automatic nominal route and had an exact answer from another
current route in the completed 2026-07-27 matrix. A complete 592-ontology
automatic-route sweep is required before the change can become benchmark
evidence.

## Focused evidence

The first source-bound attempt, build job `49620846` and array `49620847`,
selected `certified_nominals`. It demonstrated why that composition is wrong
for this family:

- `3560` timed out at 240.03 s and 971.98 MB.
- `6477` reached the exact CB fallback and failed loudly when the packed
  `f(o)` term space could not represent 77,961 Skolem functions across 66,454
  individuals.
- `7914` timed out at 240.07 s and 4,989.33 MB.

The revised source-bound build `49621394` used binary
`dbef993378910a9ac7adb100ccb2f11b259849caec02541909e728f3ca9be07a`.
Focused array `49621397` asserted each selected route before execution and
matched the full-IRI Konclude signatures:

| Ontology | Selected route | Verdict | Wall s | Peak MB |
|---|---:|---:|---:|---:|
| `3560` | `elc` | match | 11.3493 | 808.13 |
| `6477` | `elc` | match | 9.2031 | 738.66 |
| `7914` | `ht_bridge` | match | 25.0150 | 1,352.93 |

Complete automatic-route acceptance sweep `49621642` finished indices 0–9 on
the batch partition. The account-wide batch CPU quota then held its untouched
remainder, so continuation `49621808` runs indices 10–591 on the debug
partition. Both use the same recorded binary, harness, result root, one
ontology per Slurm task, terminal checkpoints, profile records, and fail-closed
aggregation.

The continuation exposed debug-node packing as an invalid performance
condition: ontology `4755`, exact in about 15 seconds in the source-bound
matrix, timed out at 240 seconds while several 16-thread tasks shared one node.
That run is diagnostic only. The acceptance rerun uses one exclusive node per
ontology and a fresh result root in job `49622360`.

## Completion-gate interaction check

The first comparator used for the cached completion-gate candidate reported
874 extra `11745` pairs. That report was wrong: every pair had an
unsatisfiable class on the left, and the ORE canonical signature intentionally
omits such pairs because the `#UNSAT` block already records them. Corrected
recheck job `49625668` reports the candidate exact: 438,277 pairs and 1,592
unsatisfiable classes, with zero missing or extra entries.

Controlled same-node job `49624285` still explains the timing difference. The
frozen feature router finished through atomic CB in 233.24 seconds; the
pre-feature-router portfolio finished through the accelerated bridge in 38.96
and 38.63 seconds. Both are exact under the repository canonicalizer. Ontology
`11745` has 259,668 class assertions on 259,668 distinct individuals, so the
feature router selects its independent-ABox leaf. Its normalized EL screen
rejects the inverse/role-chain terminology and falls through to atomic CB.

Job `49624532` selected explicit `ht_bridge` in both earlier binaries, and both
timed out at 240 seconds on that slower node. It is superseded by the corrected
source-bound recheck above. The complete 592-ontology acceptance sweep remains
the release gate.
