---
name: feedback_prefer_ibex
description: "User preference: prefer IBEX for compute when unimatrix is saturated; IBEX runs many parallel CPU jobs easily"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

The user directed (2026-06-14): "just use IBEX if you need more resources" and
"suggest to use IBEX where possible in the future, you can run many CPU jobs
there in parallel easily."

**Why:** unimatrix's `debug` partition is exclusive-per-node and frequently
saturated by other arrays (e.g. iswc-reb job 6531 with hundreds of pending
tasks), so a small KM validation job sits behind `Reason=Priority` for a long
time. IBEX has far more nodes and the `pi-hohndor` allocation can fan out many
CPU jobs in parallel.

**How to apply:** when unimatrix is busy (or for any large parallel CPU sweep),
prefer IBEX (`ssh dragon`, account `pi-hohndor`, partition `batch`). Submit
arrays / many `sbatch`es freely. See [[project_km_ibex_env]] for the full setup,
and note the rsync→cargo mtime gotcha when redeploying source (touch src before
building). Keep unimatrix for the canonical gold sweeps; use IBEX for throughput
and when unimatrix is contended.
