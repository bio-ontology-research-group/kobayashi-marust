# Automatic ORE sweep for commit 994c7b3

This is the current source-bound production result for one command,
`km classify`, selected from ontology features without expected answers.

## Provenance

- Source commit: `994c7b3`
- IBEX binary SHA-256:
  `44c5c9094ad490702c213ae47e8a97eb113a6c66b145f98281a32606b7d73720`
- Build job: `49778147`
- Main 592-task array: `49778149`
- Independent 4669 full-IRI oracle job: `49779419`
- Remote evidence root:
  `/ibex/scratch/hohndor/km/release-994c7b3-auto-20260801`
- Contract: 240 seconds, 20 GiB reasoner limit, 16 worker CPUs, Intel Xeon
  Gold 6248 nodes

## Result

| measure | value |
|---|---:|
| terminal rows | 592 |
| `status=ok` | 591 |
| error | 1: ontology 1194 |
| retained Konclude full-IRI matches | 587 |
| consistency mismatches with retained gold | 2: 2669, 15516 |
| independently adjudicated no-gold results | 2: 4669, 10860 |
| mean / median wall over OK rows | 6.5941 s / 0.2792 s |
| mean / median peak RSS over OK rows | 833.45 MiB / 44.96 MiB |

Every row carries the same binary checksum, the ontology's array index, a
terminal checkpoint, and a nonempty automatic route trace.

## Ontology 4669

The automatic `mirror_private` route returns 846,306 named-class
subsumptions and zero unsatisfiable classes in 68.95 seconds at 4,823,596 KiB.
The full-IRI oracle digest is
`d02decbafe66d8a9f1afaf7385785b6937fe46c1f288a33113c83c2bbe805b96`.

The generic Python benchmark postprocessor held about 48 GiB while processing
the 104-MiB JSON taxonomy and exceeded its task cgroup. This was a harness
failure, not a reasoner failure. The published 4669 row therefore records the
direct reasoner measurement, retained output SHA-256, exact oracle job, and
both failed generic-harness job IDs. The reasoner itself remained under the
20-GiB benchmark limit.

## Remaining ontology

Ontology 1194 selects `nominals` and fails closed without a taxonomy. In this
sweep it returned `error` after 27.893 seconds at 18,561.77 MiB. Candidate
cardinality-partition repairs remain isolated until they finish within the
same 240-second, 20-GiB contract and pass the full regression gate.
