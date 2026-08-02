# Rejected active body-posting candidate

Candidate `ba48c13` adds an active body-atom posting and chooses the rarest
required posting across a strengthening clause's body and head before the
existing exact backward-subsumption check. Every candidate that the
strengthening clause can remove must contain every selected body atom and head
literal. Randomized linear-oracle, shared-base, and complete release validation
passed (1,946 passed, eight intentionally ignored, zero failed).

## Provenance

- Source archive SHA-256:
  `5bdafb92e93ce9cdb780b602f48698aa6d2b6f773c58f84fd7111e7f4bf07d3c`
- IBEX build job `49853813`, with `BUILD_COMPLETE`
- Binary SHA-256:
  `c4357630fa5d6f2f3a2f512d2ea4d38be1bd3e2c7a6662f347694aac523e6b49`
- Four-task gate array `49853952`; every task emitted a checkpoint and
  `TASK_COMPLETE`
- Immutable root:
  `/ibex/scratch/hohndor/km/candidate-ba48c13-active-body-20260802`

| ontology/configuration | status | verdict | wall s | peak MiB | baseline wall s |
|---|---|---|---:|---:|---:|
| 1194 automatic | error | error | 31.1029 | 18,471.16 | 32.0151 |
| 1194 exact CB, 2 threads, 225-second cap | error | error | 234.3411 | 12,919.79 | 234.5824 |
| 8480 automatic | ok | exact match | 21.9447 | 5,458.52 | 19.9043 |
| 15846 automatic | ok | exact match | 198.7937 | 19,078.18 | 197.8516 |

The new posting neither closes 1194 nor materially advances it and slightly
slows both nominal sentinels. Its extra index also consumes memory. The
candidate is rejected and not integrated. The next diagnostic counts
backward-subsumption call shapes and candidate volumes directly.
