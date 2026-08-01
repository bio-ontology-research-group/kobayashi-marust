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
driver, binary, source, result, and aggregation hashes are retained.

## Completed panel

Cluster build job `49736470` and resumable array `49737130` produced all
32,560 rows. The original runner reported 85 `harness_error` rows, all on
ontologies 3524 and 15703. Both have non-injective local names, and the legacy
canonicalizer exhausted its supervisor while retaining the full answer. This
was a publication failure, not a reasoner result.

Collision-safe array `49787943` reran all 55 procedures for both ontologies,
fingerprinted each successful answer using full IRIs, and deleted that answer
before starting the next procedure. Both result files contain exactly 55
unique arms and no `harness_error`. Every one of their 81 successful rows has
the established full-IRI digest
`090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a`.
The corrected panel totals are:

| status | rows |
|---|---:|
| `ok` | 26,240 |
| `unsupported` | 4,925 |
| `timeout` | 821 |
| `error` | 514 |
| `memout` | 56 |
| external `output_error` | 4 |
| **total** | **32,560** |

The two corrected source JSONLs are retained under
[`evidence/collision-rerun-49787943/`](evidence/collision-rerun-49787943/).
Task 15703's final Slurm wrapper exited after successful publication because
its validator assumed that the shared results directory contained only one
file and saw the concurrently completed 3524 file. Direct validation proves
both published files complete. The retained sbatch validator now selects the
file for its own array task and also checks arm uniqueness and full-IRI
digests, preventing this concurrency race from recurring.

The first attempted build (`49736467`) failed before doing work because
`SLURM_TMPDIR` was absent; its blocked dependent array `49736469` was
cancelled. The submitted scripts use an explicit persistent scratch fallback
when node-local `SLURM_TMPDIR` is unavailable.
