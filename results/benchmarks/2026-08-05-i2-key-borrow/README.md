# Borrow blocking keys without a temporary vector

Commit `5bd9489` splits the immutable node-concept borrow from the mutable
incremental-blocking posting-list borrows. The registration loop can therefore
iterate concept keys directly instead of allocating and copying one temporary
`Vec<CLit>` for every unblocked node. It inserts the same keys in the same
iteration order and changes neither blocking nor reasoning.

The complete release suite passed: 1,952 library tests passed, eight were
ignored, and all binary, integration, and documentation tests passed. The
focused hypertableau filter passed 90 tests. This allocation optimization does
not change calculus rules or scheduling and requires no Lean re-certification.

The source archive has SHA-256
`91f2e84a36637e65755333412aabdf7b1938677e168a6eac4ac3dc7c97c8a4fc`.
IBEX build job `50050792` is producing the source-bound candidate. Alternating
ORE6934 pair job `50050793` is dependency-queued behind that build and the
`07b8526` corpus sweep. The pair must demonstrate exact output and useful
performance before this change advances to a corpus gate.

[`ibex_build_5bd9489.sbatch`](ibex_build_5bd9489.sbatch) and
[`ibex_6934_pair.sbatch`](ibex_6934_pair.sbatch) reproduce the staged test.
