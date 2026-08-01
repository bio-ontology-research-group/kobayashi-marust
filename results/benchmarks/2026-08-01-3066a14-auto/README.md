# Automatic ORE sweep after exact-role backward-link indexing

This source-bound production sweep measures one command, `km classify`, over
all 592 ORE 2015 ontologies after indexing EL predecessor links by exact role.

## Provenance

- Reasoner commit: `3066a14`
- Tested archive HEAD: `0a4ce78` (documentation only after `3066a14`)
- Archive SHA-256:
  `c7eba5a3a6358c8a7201019a3502b5b4923047824514f4507d398f150c188062`
- Cluster-native build job: `49811241`
- IBEX binary SHA-256:
  `8b14aa5aa026af208fc44d22ba3db372b04f29040cbf7561eb4dbdbdd4ca40d0`
- End-to-end gate: `49811822_401`
- Resumable 592-task array: `49811856`
- Remote evidence root:
  `/ibex/scratch/hohndor/km/release-0a4ce78-auto-20260801`
- Contract: 240 seconds, 20 GiB reasoner process-tree RSS, 16 CPUs, Intel
  Xeon Gold 6248 nodes

## Result

| measure | value |
|---|---:|
| terminal rows | 592 |
| `status=ok` | 591 |
| error | 1: ontology 1194 |
| retained Konclude full-IRI matches | 587 |
| independently adjudicated results | 4: 2669, 4669, 10860, 15516 |
| mean / median wall over OK rows | 6.6750 s / 0.2779 s |
| mean / median peak RSS over OK rows | 842.06 MiB / 44.79 MiB |

The audit verifies exactly one row for every ontology and index 0 through 591,
one binary checksum, equal terminal rows and checkpoints, successful profiles,
and nonempty automatic route traces. The complete source-bound table is
[`automatic-results.tsv`](automatic-results.tsv).

Every status, verdict, signature or full-IRI digest, consistency value,
subsumption count, and unsatisfiable-class count is identical to the preceding
`b442fe7` sweep. Ontology 1194 remains the only non-completing input and fails
closed without publishing a taxonomy.

The separate exact `KM_ELC_CERT=2` gate for ontology 1194 still timed out after
245.29 seconds with zero output. Exact-role backward-link indexing reduced its
peak from 7,078,600 to 6,698,628 KiB while retaining essentially identical
saturation counts. This is a memory improvement, not a closure.
