# v24 native-disjoint full sweep

Source capsule SHA-256: `f76d4b7d3a24ccef9c0ce8ece73ad70ac032643fe24851a040b874b85f82c35d`

Binary SHA-256: `7d8666d86cb7ff3af5990e4caa1ea32e487e1f3baa466dfb02b43d7b70264716`

IBEX root: `/ibex/scratch/hohndor/km/v24-native-disjoint-20260826`

The 592-ontology sweep completed as Slurm job `50877542`. The strict audit
against v20 found 591 successful classifications plus the expected ORE1194
error, no behavioral differences, and five route changes. Mean wall time fell
from 1.562004 s to 1.531883 s and mean peak memory from 231.032 MiB to
227.543 MiB. The release gate still failed only ELK mean wall time
(1.531883 s versus 1.520774 s), so v24 was not released.

Authoritative remote evidence:

- `full-sweep/strict-audit-v24-v20.json`
- `full-sweep/release-gate-v24.txt`
