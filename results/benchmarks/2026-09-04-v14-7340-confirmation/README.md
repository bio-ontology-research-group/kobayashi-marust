# ORE 7340 strict-boundary confirmation

IBEX array `51332636` ran the exact integrated binary from build job
`51331531` ten times on ORE 7340 under `KM_ROUTE=auto`. The binary SHA-256 is
`8cb733feb586287228c8a3894b213d1c9fca130525033465d9fa458516984c04`.
All ten runs selected `elc`, returned `status=ok`, matched the retained gold
signature, wrote a checkpoint and route trace, and emitted a task-complete
marker. No error log was produced.

Wall times were 2.4418, 2.6089, 2.6296, 2.7273, 2.7319, 2.8013, 2.8237,
2.8425, 3.0855, and 3.1269 seconds. Median wall time is **2.7666 seconds**,
which does not beat the 2.5354-second external target. Median peak RSS is
291.525 MiB, safely below the 759.47-MiB target. The ontology therefore remains
a strict joint residual; the faster one-shot result in the full sweep is not
accepted as a recovery.

The stage profile attributes about 1.39 seconds to the functional-syntax
frontend and only about 0.09 seconds to EL saturation, so further worker-count
tuning is not the next action. Raw result JSON and checkpoints are retained in
`.work/artifacts/v14-7340-confirmation/results/` and on IBEX under
`/ibex/scratch/hohndor/km/v14-7340-confirm-20260904/`.
