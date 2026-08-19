# Compact complete-ELC output evidence

Release candidate `b5aca75` uses a checked dictionary-coded handoff for
complete subprocess EL taxonomies with at least two million relations. Sparse
answers and partial certificate residues remain JSON. The candidate binary is
`e14949a66e6029fc215d22cdf5bee55b0caf73ff572bb0acd9dba0b5412a7d3a`;
the v0.2.31 baseline binary is
`c28ece45471c273c651921ab2752604281a2b83e04db5408abdc56772965b692`.

## Full ORE pair

Order-balanced same-node job `50546048` ran both binaries over all 592 ORE
ontologies. It contains exactly 1,184 terminal JSON rows, 592 complete pairs,
and no temporary files. Each arm has 591 successful classifications and the
expected fail-closed ORE1194 result. Comparisons cover status, verdict,
consistency, selected route, solved state, missing and extra counts,
unsatisfiable counts, and the collision-sensitive full-IRI signature. Every
comparison count is zero.

| arm | wall mean s | wall median s | peak mean MiB | peak median MiB | wall sum s |
|---|---:|---:|---:|---:|---:|
| v0.2.31 baseline | 3.446567 | 0.1620 | 424.0191 | 35.07 | 2036.9209 |
| candidate | 3.415018 | 0.1628 | 424.1815 | 35.31 | 2018.2759 |

Mean wall improves by 0.916% and the paired reduction sums to 18.645 seconds.
The 0.8 ms median-wall movement and 0.16/0.24 MiB memory movements are treated
as measurement noise; no median or memory improvement is claimed.

## Threshold selection

Jobs `50543902`, `50544635`, and `50544636` each contain 1,184 terminal rows
and zero semantic differences. Their pooled 1,773 successful classifications
per arm reduce mean wall from 3.474599 to 3.443336 seconds and mean peak RSS
from 424.0748 to 423.6703 MiB. The pooled medians differ by 0.9 ms and 0.01
MiB. These runs selected the dense-only threshold and showed that median-band
movement was noise. The final candidate additionally skips relation counting
for small subject maps; job `50546048` validates that exact source.

## Release tests

The complete release-mode suite passes 1,997 library tests with eight ignored
tests and every integration test. This includes compact-codec round-trips,
malformed and truncated payload rejection, all routing integration tests, and
`issue_3_soundness`. The issue #3 test confirms that nominal enumeration plus
explicit difference reports the pigeonhole ontology inconsistent.
