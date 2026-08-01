# Automatic ORE sweep after in-place Edge-NF4 propagation

This source-bound production sweep measures one command, `km classify`, over
all 592 ORE 2015 ontologies after removing the Edge-NF4 propagation snapshot.

## Provenance

- Reasoner commit: `b442fe7`
- Tested archive HEAD: `1939991` (documentation only after `b442fe7`)
- Archive SHA-256:
  `3cec215d2f8345ef1c81f7cb158b4b8d6d30c71511f3161bbfed4e012b0a5bea`
- Cluster-native build job: `49796295`
- IBEX binary SHA-256:
  `8c2460e2c1238487e4fd2e0d3d1b846520b36cef5fb12189d9a986e6eda7eead`
- End-to-end gate: `49796423_0`
- Resumable 592-task array: `49796520`
- Remote evidence root:
  `/ibex/scratch/hohndor/km/release-1939991-auto-20260801`
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
| mean / median wall over OK rows | 6.7122 s / 0.2760 s |
| mean / median peak RSS over OK rows | 836.03 MiB / 44.91 MiB |

The audit verifies exactly one row for every ontology and index 0 through 591,
one binary checksum, byte-equal terminal checkpoints, successful profiles,
and nonempty automatic route traces. The complete source-bound table is
[`automatic-results.tsv`](automatic-results.tsv).

Compared with the preceding `fde093c` sweep, every ontology retains the same
status and semantic result. Ontology 4669 is now adjudicated in the array with
the streaming full-IRI SCC encoding, rather than published afterward with the
independent pair-stream encoding. Its result is unchanged: 846,306 pairs, zero
unsatisfiable classes, and SCC digest
`a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30`.
It completed in 69.0221 seconds at 5,689.39 MiB; fingerprinting took 9.1927
seconds at 483.56 MiB. This in-array treatment prevents the legacy local-name
postprocessor from growing to about 80 GiB.

Ontology 1194 still selects `nominals` and fails closed without publishing a
taxonomy. The separate exact EL candidate gate shows that in-place Edge-NF4
iteration reduces its peak from 11,101,160 to 7,078,600 KiB but does not move
it below the 240-second contract.
