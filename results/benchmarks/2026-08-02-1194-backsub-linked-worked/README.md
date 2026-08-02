# ORE 1194 linked worked-off gate

This experiment replaced worked-off tombstone filtering with an intrusive
insertion-order list. Backward subsumption unlinks a live slot in O(1), and
iteration follows only live links while preserving the exact survivor and
re-addition order. It does not improve ontology 1194 and is not included in
`main`.

## Candidate and verification

- Parent: detached stable-slot commit `8d9e6f8`
- Candidate: detached commit
  `4a34d3cebf005b380dfd6b721ecbdb83fe5366e3`
- Source archive SHA-256:
  `690bda455ec5e169eef9dd754787f36b7927ab7c5fa998e98abcb7b6a9a01b1c`
- Complete local release tests: 1,990 passed, 8 ignored, 0 failed
- IBEX build job: `49860653`, `BUILD_COMPLETE`
- IBEX binary SHA-256:
  `3b83be40b064f7bb5f9cbf4592848ca03384fc5f61dc54c5e89afcccf35b5920`
- Exclusive Gold 6248 gate array: `49860975`

Each gate task verified the binary hash and produced a checkpoint, selected
route trace, JSON result, and `TASK_COMPLETE` marker.

## Exclusive gate results

| Ontology | Route | Status | Gold verdict | Wall (s) | Peak (MB) |
|---:|---|---|---|---:|---:|
| 1194 | automatic `nominals` | error | error | 29.2137 | 18,449.05 |
| 1194 | manual CB, 2 threads, 225 s cap | error | error | 234.4951 | 14,891.39 |
| 8480 | automatic `nominals` | ok | match | 20.3313 | 5,751.17 |
| 15846 | automatic `certified_nominals` | ok | match | 195.9173 | 19,004.53 |

The serialized non-exclusive screen array `49860999` independently reproduced
the 1194 outcome: automatic ended at 28.6408 seconds and 18,445.75 MB, while
manual ended at 233.7743 seconds and 14,904.05 MB. Its 8480 task matched gold.
The redundant 15846 screen task was cancelled only after the exclusive 15846
task had completed with a matching result.

## Decision

Reject the candidate. Live-only iteration does not reduce the 1194 manual wall
time and raises its peak memory by about 0.8 GB relative to stable slots. The
backward-subsumption mutation profile's large worked/todo scan measurements do
not translate into end-to-end savings when those scans are removed through
stable slots, stable-slot compaction, or insertion-order unlinking. Further
1194 work should target a different source of saturation work rather than
another worked-off container representation.

