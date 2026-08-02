# Shared CB clause-facet cache gate on ORE 1194

Claude Opus proposed caching every immutable head-index key and propagation
eligibility flag once per interned context clause. The implementation at
`c24131d` preserved posting order and shipped differential tests against frozen
copies of the old indexing and unindexing paths. The full release suite passed
1,947 library tests with eight ignored, followed by every integration and CLI
suite with zero failures.

The controlled workstation gate used `/tmp/1194.clauses.json`, one CB worker,
no named query roots, and a 245-second wall cap, matching the preceding
`1ef8ee1` gate.

| candidate | wall | peak RSS | result |
|---|---:|---:|---|
| `1ef8ee1` without facet cache | 245.17 s | 2,470,112 KiB | timeout, no output |
| `c24131d` with facet cache | 245.18 s | 2,478,844 KiB | timeout, no output |

The cache produced no measurable progress on the remaining ontology and added
about 8.5 MiB peak RSS. KM therefore reverted it in `7d4c6b5` instead of
carrying a large, unproven optimization into another 592-ontology sweep.
