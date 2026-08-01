# KM v0.2.0 uniform ORE panel

This run measures all 40 public KM routes, the eight documented nonstandard
solution environments, and seven pinned external baseline modes over all 592
ORE 2015 ontologies. Every procedure receives 240 seconds, 20 GiB summed
process-tree RSS, and 16 CPU cores on the IBEX Intel Xeon Gold 6248 nodes.

The KM source is release documentation commit `364b8b2` on tag `v0.2.0`.
External identities are inherited unchanged from the hash-bound 2026-07-22
contract: Konclude `v0.7.0-1138` (`0002e8063540`), HermiT
`1.4.6.519-SNAPSHOT`, ELK `0.6.0`, RustDL `0.3.31` (`8c2bb1bf43d9`), and
Sequoia `0.6.1-alpha` (`c5248ec7be30`).

Optimization-stage snapshots and reverse-ablation experiments are excluded.
They are development-history measurements, not current reasoner routes. The
contract therefore contains 55 procedures and 32,560 independently limited
measurements.

The run is resumable per ontology. A complete ontology result is accepted only
when all 55 ordered rows are present; otherwise that ontology is rerun. Build,
driver, binary, source, result, and aggregation hashes are retained before the
README headline table is replaced.

Build job `49736470` is running. Resumable array `49736471` is dependency-bound
to the successful build and will execute the 592 ontology tasks with at most 32
concurrent tasks. The first attempted build (`49736467`) failed before doing
work because `SLURM_TMPDIR` was absent; its blocked dependent array `49736469`
was cancelled. The submitted scripts now use an explicit persistent scratch
fallback when node-local `SLURM_TMPDIR` is unavailable.
