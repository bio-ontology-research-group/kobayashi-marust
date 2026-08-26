# v1.1 aggregate wall-time budget

This ledger keeps the v1.1 objective tied to the immutable v1.0.0 baseline and
the binding external aggregate boundary. It is a targeting calculation, not a
release benchmark. Candidate measurements below come from exact-signature
functional panels on potentially different IBEX CPU models. Only the pending
complete Gold-6248 sweep can establish release performance.

The immutable baseline has 591 successful classifications, 1,913.8077 summed
wall-seconds, and a 3.238253-second mean. Beating ELK's 1.520774-second mean on
the same 591-answer denominator requires a strict total below 898.7777 seconds,
or more than 1,015.0300 seconds of savings.

## Non-overlapping measured opportunity

| Candidate family | v1 pool, seconds | functional candidate, seconds | projected saving, seconds | Evidence |
|---|---:|---:|---:|---|
| certified route-independent ABox elision, 20 ontologies | 272.2956 | 64.0687 | 208.2269 | paired exact functional panels `50842877`, `50844429` |
| direct pure-leaf / RBox-flat family, 9 ontologies | 192.0348 | 20.6150 | 171.4198 | exact array `50844954` |
| cyclic/large flat NF1 family, 8 ontologies | 165.4888 | 27.3130 | 138.1758 | exact array `50849592`, replacing its ORE3524 fallback with corrected exact gate `50849929` |
| medium existential leaves, 13 ontologies | 7.3650 | 1.0392 | 6.3258 | exact array `50846607` |
| streamed-flat residuals 868, 11395, 3836, 1559 | 90.7027 | 13.3288 | 77.3739 | exact functional records in the streamed-flat ledger |
| **Total** | | | **601.5222** | all sets above are disjoint |

Applying only these measured functional substitutions to v1 projects
1,312.2855 wall-seconds, or a 2.220449-second mean. This remains about 413.51
seconds above the ELK release boundary.

## Decisive pending pools

The standalone disjoint-union consistency precursor is no longer a pending
savings pool. Its v9 panel produced zero wins in 31 paired rows and was
cancelled as performance-negative. The large bridge trio ORE3215, ORE14817, and ORE10621
covers 202.4128 seconds. ORE4669's mirror route covers another 66.4735 seconds.
Those routes remain useful targets, but cannot establish v1.1 alone.

The next broad optimization must save substantial wall time outside these
pools while preserving byte-identical v1 answers. The main remaining sources
are general ELC completion/output and production/bridge orchestration. The
strict full sweep remains authoritative for overlap, fallback overhead,
correctness, and aggregate resource use.

Memory is not currently the binding aggregate metric: v1's 427.878-MiB mean is
already below ELK's 493.327 MiB and every other retained external mean. Every
candidate must still preserve that advantage, reduce rather than merely tie
it at the v1.1 release gate, and eventually beat the per-ontology memory target
for v1.2.
