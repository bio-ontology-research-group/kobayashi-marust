# ORE 1194 stable-slot compaction gate

This experiment tested whether stable O(1) worked-off deletion plus amortized
order-preserving compaction removes the backward-subsumption scan cost measured
in the mutation profile. It does not improve ontology 1194 and is not included
in `main`.

## Candidate and verification

- Stable-slot parent: detached commit `8d9e6f8`
- Compaction candidate: detached commit
  `ad756a53252dd86c5873a9028f7130af25e1a5cc`
- Source archive SHA-256:
  `6b54ebdf4053e2ef5dcc6f7db360a80b37fa9f5767254f710332070d3badfa21`
- Complete local release tests: 1,992 passed, 8 ignored, 0 failed
- IBEX build job: `49858583`, `BUILD_COMPLETE`
- IBEX binary SHA-256:
  `22fcdf3c149dd140bedf1f2957453685a186b964217c1dab4af23a9968c9cb27`
- Exclusive Gold 6248 gate array: `49858813`

Each gate task verified the binary hash and produced a checkpoint, selected
route trace, JSON result, and `TASK_COMPLETE` marker.

## Exclusive gate results

| Ontology | Route | Status | Gold verdict | Wall (s) | Peak (MB) |
|---:|---|---|---|---:|---:|
| 1194 | automatic `nominals` | error | error | 31.0967 | 18,561.95 |
| 1194 | manual CB, 2 threads, 225 s cap | error | error | 234.0491 | 14,098.23 |
| 8480 | automatic `nominals` | ok | match | 21.6481 | 5,703.18 |
| 15846 | automatic `certified_nominals` | ok | match | 195.2698 | 19,015.50 |

The serialized non-exclusive screen array `49858833` independently produced
the same outcomes. Its 1194 manual run ended at 233.8424 seconds and 14,108.12
MB. The two sentinels matched gold.

## Decision

Reject the candidate. The uncompacted stable-slot parent had already ended the
1194 manual run at 234.7442 seconds and 14,109.95 MB. Compaction changes neither
completion nor resource use materially. The measured cost is therefore not
explained by accumulated tombstone traversal, and this representation should
not be retried as an ontology 1194 fix.

