# v1.4 EL residual worker panel

IBEX array `51259178` tested the pinned commit
`5629b4e12bf7982d42c863652c1bdca31373b28a` and binary SHA-256
`7161ebb7a8dd9788e58d0ea083c2633570312d23ae2828f39ed9a24ebbf2132c`
on all nine remaining EL-routed strict-performance residuals. Each ontology ran
with serial EL completion and `KM_ELC_PAR_CTX` at 2, 4, and 8 workers, with
three repetitions per arm.

The array produced 108/108 results, 108/108 checkpoints, and 108/108
`TASK_COMPLETE` markers, with no failure artifact. Every result selected `elc`
and matched its retained gold signature.

| ontology | fastest admissible arm | median wall (s) | wall target (s) | median peak (MiB) | peak target (MiB) | strict result |
|---|---|---:|---:|---:|---:|---|
| ORE 12087 | serial | 3.2800 | 2.8360 | 359.26 | 849.45 | fail |
| ORE 12387 | context 8 | 3.5467 | 3.2375 | 405.73 | 729.74 | fail |
| ORE 13224 | context 2 | 3.4890 | 2.0760 | 397.90 | 397.32 | fail |
| ORE 1579 | context 8 | 6.5258 | 2.4938 | 1100.35 | 596.66 | fail |
| ORE 15976 | context 8 | 4.1658 | 2.8331 | 352.52 | 693.33 | fail |
| ORE 16596 | context 2 | 3.9787 | 2.8055 | 361.51 | 877.77 | fail |
| ORE 6722 | context 8 | 2.8269 | 1.8636 | 618.48 | 428.45 | fail |
| ORE 7340 | serial | 2.5353 | 2.5354 | 292.21 | 759.47 | provisional only |
| ORE 7868 | context 8 | 3.2620 | 2.4669 | 302.45 | 934.22 | fail |

The three-run ORE 7340 margin was only 0.0001 seconds and was not accepted.
Confirmation array `51259422` ran the ordinary automatic route ten more times.
All ten results and checkpoints were valid and gold-matching, with ten
completion markers and no failure artifact. Its median was 2.9443 seconds and
291.91 MiB, so ORE 7340 remains a strict residual.

Worker scheduling alone therefore recovers none of this family. The result
rules out another worker-count routing pass and directs the next work toward
fixed frontend/output costs and EL completion hot paths. The evidence archive
contains 358 checksum-manifest entries; its `SHA256SUMS` file hashes to
`d04541d7eedb436a7b108ac444f337963f7c90d9e2a1b405a8794a40d39313f2`.
