# Indexed role-relevance reachability

The frontend's role-relevance analysis used to rescan every normalized clause
for each growing wave of needed concepts and roles. Large clause sets now build
borrowed reverse head indexes and activate each reachable clause once. Inputs
below 10,000 clauses retain the established scan, avoiding fixed index costs on
the corpus-median path. The computed backward slice is unchanged.

Focused IBEX panel `50453255` compared v0.2.17 with the indexed implementation
on five large ontologies. Every clause file and metadata file was byte-identical.
The indexed phase was 5.9% faster in that panel. The final thresholded binary is
`4a972445d57a…`.

Strict automatic sweep `50456241` produced exactly 592 terminal rows on Intel
Xeon Gold 6248 nodes. It reports 591 successful classifications, ORE1194 as the
sole fail-closed error, and zero status, consistency, signature, route, or
coverage differences from v0.2.17.

| Metric | v0.2.17 | Candidate | Change |
|---|---:|---:|---:|
| Mean wall | 4.2520 s | 4.1484 s | -2.44% |
| Median wall | 0.2208 s | 0.2192 s | -0.72% |
| Mean peak RSS | 450.74 MiB | 450.25 MiB | -0.11% |
| Median peak RSS | 39.24 MiB | 39.04 MiB | -0.51% |

This directory contains the complete result table, strict audit, v0.2.17
comparison, focused logs, and reproducible IBEX scripts.
