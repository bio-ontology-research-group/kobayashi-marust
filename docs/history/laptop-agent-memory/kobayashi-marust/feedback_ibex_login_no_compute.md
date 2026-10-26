---
name: feedback_ibex_login_no_compute
description: "HARD RULE — never run compute on IBEX login nodes; they get flagged + orphans linger for days. Build on ws, sweep via Slurm/unimatrix."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: f75fe881-cb21-41f6-8110-ddbbedcc36b5
---

HARD RULE (user, 2026-06-26, after an IBEX admin email): NEVER run reasoner/compute
work on IBEX login nodes (`ssh dragon` lands on `login509-XX-l`). IBEX flags high CPU
on login nodes ("Long running processes are discouraged"). Compute MUST go through
**Slurm** (account pi-hohndor, partition batch) or run on **ws** (compile + targeted
evals) or **unimatrix** (sweeps). Login nodes are for editing/submitting only.

**Why:** an orphaned `kobayashi_marust` ran 1day+ at 98.9% CPU on login509-02-l
(stale from a prior session) → admin email to the user. Same orphan hazard as ws
([[feedback_ws_no_orphans]]): `km classify` spawns children that outlive a killed
parent.

**How to apply:** (1) build unit tests on ws, never the IBEX login node
([[feedback_build_before_benchmark]]); (2) for IBEX compute, `sbatch` to batch nodes,
never run the binary on the login shell; (3) kill orphans by PID across login nodes —
reach a specific node via `ssh dragon "ssh -o StrictHostKeyChecking=no <node> 'kill -9 <pid>'"`
(the laptop can't resolve `login509-02-l` directly; jump through dragon). NEVER
`pkill -f` (self-matches). (4) After any IBEX session, `pgrep -u $(whoami) -a -f kobayashi`
on the login node(s) and clean up.
