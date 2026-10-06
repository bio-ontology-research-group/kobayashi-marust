# Completed large-output comparison 53336568

All 12 attempts (three inputs, two repetitions, two output modes) completed and
passed independent full-answer comparison. The summarizer verifies the frozen
input, runner, artifact, flag, and task identities.

| Ontology | Expanded mean seconds | Graph mean seconds | Expanded bytes | Graph bytes |
| --- | ---: | ---: | ---: | ---: |
| 14459 | 33.377 | 28.067 | 1,345,916,975 | 87,519,993 |
| 11085 | 43.139 | 41.757 | 1,604,796,359 | 1,604,796,397 |
| 8486 | 33.705 | 28.510 | 1,420,964,916 | 93,331,073 |

14459 and 8486 show about 16% and 15% reductions in total wall time. Their
peak process memory is essentially unchanged. 11085 retains materialized
output, so its small timing difference does not establish a graph-size benefit.
These are targeted paired results from one pinned production-profile binary;
the full-corpus graph-output job 53338465 remains necessary for acceptance.
See graph-json-large-final-53336568.json for all attempts, costs, and audits.
