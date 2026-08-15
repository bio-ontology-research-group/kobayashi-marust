# Compact exact-EL handoff and median overhead

This directory records the v0.2.28 release evidence.

- Tested implementation: `a50671d`
- Native IBEX binary SHA-256:
  `4aa2370c8cebac9b78fcd64cfbfa6d4be0af2bd87bb6b5c0f351c478d88056af`
- Released baseline binary SHA-256:
  `628b11d8e95dcedf2394afac53a35399ba1e9106b0e844aae3dbbad41852875a`
- Compact-handoff binary SHA-256:
  `1cd7dcbeea96e39b4b4b50eec48e42a9005e223a26515661b6329e746578033c`
- Hardware: Intel Xeon Gold 6248
- Contract: 240-second timeout and 20-GiB process-tree memory cap

## Strict release sweep

Slurm job `50528307` produced exactly 592 result rows, profiles, and
checkpoints. It left no temporary files. The result is 591 successful
classifications with ORE1194 as the sole fail-closed error. Comparison with the
v0.2.27 compact-control sweep found zero differences in status, verdict,
consistency, selected route, or full-IRI signature. ORE3524, ORE13503, ORE4669,
and ORE15703 retain their expected collision-sensitive fingerprints.

| metric | published v0.2.27 | v0.2.28 candidate | change |
|---|---:|---:|---:|
| Mean wall, seconds | 3.586135 | 3.555234 | -0.030901 |
| Median wall, seconds | 0.1848 | 0.1635 | -0.0213 |
| Mean peak RSS, MiB | 433.281997 | 423.840254 | -9.441743 |
| Median peak RSS, MiB | 35.04 | 34.60 | -0.44 |

Jobs `50528026` and `50528176` were startup-only deployment failures: the
first lacked the ontology list and the second lacked harness modules. Their
guards exited before classification and produced zero result rows. They are not
part of the measurement. The corrected root was checked for zero rows before
job `50528307` began.

## Controlled pairs

Full order-balanced job `50526676` ran the exact v0.2.27 and compact-handoff
binaries sequentially for all 592 ontologies. Both arms have 591 successes,
ORE1194 as their sole error, no temporary files, and zero semantic or route
differences. Across successful rows, compact handoff reduced mean wall from
3.573392 to 3.543427 seconds and mean peak RSS from 433.346 to 423.764 MiB.

Median-boundary job `50527646` ran three alternating pairs for each of 90
ontologies around the corpus timing median. All 270 pairs have identical
signatures. Candidate mean wall fell from 0.183767 to 0.182740 seconds, median
wall from 0.18705 to 0.18695 seconds, mean peak RSS from 39.896 to 39.683 MiB,
and median peak RSS from 31.52 to 31.47 MiB.

`audit_compact_pair.py` validates the full compact pair. The Slurm files retain
the exact build, panel, and strict-sweep commands. `median90.txt` pins the
boundary panel membership.

No Lean re-certification is required. These changes replace a lossless worker
representation and move or reuse allocations without changing rules,
redundancy, ordering, route selection, or the derived fixpoint.
