# Borrow frontend-only output indexes

The functional-syntax frontend used to clone every concept name into a sorted
set solely to test declaration membership. It then cloned all IRI-registry keys
into a temporary vector and looked each key up again while constructing output
metadata. The candidate uses borrowed hash-set entries for membership and
iterates borrowed registry pairs directly. Declaration tautologies retain their
source order, and serialized clauses and metadata remain unchanged.

IBEX frontend panel `50451358` ran v0.2.16 and candidate binary
`a1348eac7e11…` sequentially on the same Intel Xeon Gold 6248 node. All five
clause files and all five metadata files were byte-identical. Summed frontend
wall fell from 94.16 to 91.88 seconds (2.42%). End-to-end paired panel
`50451248` also produced five identical classifications and reduced summed wall
from 183.23 to 180.16 seconds (1.68%).

Strict automatic sweep `50451542` produced exactly 592 terminal rows with the
expected binary, CPU model, profiles, checkpoints, and route traces. Comparison
with the v0.2.16 sweep found zero status, consistency, signature, or coverage
differences. Both mean and median wall and peak RSS improved in the raw 591
successful rows:

| Metric | v0.2.16 | Candidate | Change |
|---|---:|---:|---:|
| Mean wall | 4.2748 s | 4.2520 s | -0.54% |
| Median wall | 0.2210 s | 0.2208 s | -0.09% |
| Mean peak RSS | 450.81 MiB | 450.74 MiB | -0.02% |
| Median peak RSS | 39.47 MiB | 39.24 MiB | -0.58% |

The release suite passed 1,972 unit tests and all integration tests, including
the issue #3 pigeonhole regression. This directory contains the complete
592-row result table, strict audit, release comparison, paired logs, and every
IBEX script needed to reproduce the gates.
