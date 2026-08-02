# ORE 1194 Hyper-batch antichain probe

This probe tested exact redundancy elimination within each Hyper call before
its conclusions enter the context. It is a negative result. The candidate is
not integrated.

## Candidate

Detached commit `ebc61b4e3a392101cdf7a59d0b882b09c6dd264c` added opt-in
`KM_HYPER_BATCH_ANTICHAIN=1`. When a Hyper call emitted more than one context
clause, the candidate passed the batch through the existing Sequoia-style
`PredResultBuffer`. The buffer retains the exact strengthening antichain:
duplicates and conclusions strengthened by another conclusion from the same
batch are removed. This changes neither inference rules nor the context
fixpoint.

The candidate retained the measured two-thread nominal schedule and
225-second central cap used to reach the ORE 1194 saturation tail.

## Validation

- Debug Hyper-focused suite: 9 passed, 0 failed, including randomized generic
  versus narrowed join comparisons.
- Focused release engine suite: 42 passed, 0 failed.
- A new pipeline differential compared complete saturation output with the
  Hyper-batch antichain disabled and enabled.
- Source archive SHA-256:
  `dca086052e66a26ffdb75668b5c61e6e8393f58d8444f968b4fdf841a4488ecc`.
- IBEX build job: `49850857`, with `BUILD_COMPLETE` marker.
- IBEX binary SHA-256:
  `dfbe3d5a0d4055645c4f4eff4be48cdc5962297e578dd3234737cadcf600bf2d`.

## ORE 1194 production gate

IBEX job `49851149`, array index 33, completed on an Intel Xeon Gold 6248
compute node. The resumable runner recorded an exact terminal checkpoint,
selected route `nominals`, explicit environment `KM_ROUTE=auto` and
`KM_HYPER_BATCH_ANTICHAIN=1`, and emitted `TASK_COMPLETE`.

| configuration | status | wall seconds | peak MiB | termination |
|---|---:|---:|---:|---|
| FIFO baseline, `644e57c` | error | 234.5824 | 12909.99 | central time cap |
| Hyper-batch antichain, `ebc61b4` | error | 233.9005 | 12934.11 | central time cap |

The candidate saved 0.6819 wall seconds while adding 24.12 MiB at peak. It
produced no taxonomy and did not materially reduce the tail. The result shows
that redundancy among conclusions emitted by one Hyper call is not the source
of the large cross-iteration antichain on ORE 1194. A useful next candidate
must exploit redundancy across calls or prevent repeated generation from the
dominant ontology-clause/context family.
