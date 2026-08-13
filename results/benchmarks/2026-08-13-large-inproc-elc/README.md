# Exact-EL in-process handoff

The automatic router already identifies an exact `elc` leaf before the
orchestrator starts a classification mechanism. This change runs structured
exact-EL leaves in the parent process, avoiding serialization and reparsing of
worker taxonomies that can exceed 500 MiB. Inputs whose named-class count is
at least 90% of their logical-axiom count retain the subprocess boundary; this
keeps the large flat-taxonomy family from retaining completion allocations
during public-output mapping. Non-EL and certified-EL routes are unchanged.

Stage job `50444397` isolated the opportunity. On ORE13482 the ELC worker took
15.49 seconds, while the complete command took about 61 seconds; worker-output
parsing and public-output mapping accounted for much of the remainder.

The source-bound candidate binary is `2b811f8586ee…`. A representative paired
panel checked structured exact-EL ABoxes and terminologies plus flat-taxonomy
controls. Every completed arm matched its retained full-IRI gold signature.
Across the first ten complete pairs, summed wall fell from 422.34 to 404.40
seconds and summed peak RSS from 42.85 to 29.42 GiB.

Strict sweep `50447018` produced exactly 592 terminal results with binary-hash,
profile, route-trace, checkpoint, and collision-safe full-IRI checks. It reports
591 successful classifications, ORE1194 as the sole fail-closed error, and zero
behavioral regressions against v0.2.14.

| Metric | v0.2.14 | Candidate | Change |
|---|---:|---:|---:|
| Mean wall | 4.5758 s | 4.4699 s | -2.31% |
| Median wall | 0.2469 s | 0.2272 s | -7.98% |
| Mean peak RSS | 499.38 MiB | 451.22 MiB | -9.64% |
| Median peak RSS | 41.64 MiB | 38.98 MiB | -6.39% |

This directory contains the 592-row automatic table, strict audit, release
comparison, representative panel rows, and the IBEX build/panel scripts.
