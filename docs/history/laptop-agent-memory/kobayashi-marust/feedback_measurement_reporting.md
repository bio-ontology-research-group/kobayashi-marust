---
name: feedback_measurement_reporting
description: "How to report benchmark measurements — always avg+median time/mem, passrate, and gold sound/complete breakdown"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

User HARD reporting rule (2026-06-17): for ALL benchmark measurements, never
report just pass/fail. ALWAYS report, per arm/config:
- **passrate** (ok / total)
- **time**: BOTH average and median wall_s
- **memory**: BOTH average and median peak_mb
- **comparison to gold**: split into **correct/sound** (no extra subsumptions) and
  **complete** (no missing subsumptions) — not just MATCH/DIFF. byte-identical sig
  = both sound+complete; for DIFF onts classify directionally (km ⊋ gold = unsound,
  km ⊊ gold = incomplete, both = both-disagree).

**NO single metric defines success/failure.** The whole panel is used together to
weigh the advantages AND disadvantages (trade-offs) of any change — a change can
win passrate while costing time/mem, or gain coverage while risking completeness.
Never declare a change good/bad on one axis; always present the full panel and let
the trade-off be judged. Report regressions on EVERY axis, not just coverage.

**Why:** pass/fail hides the resource cost of a change (e.g. racing HT alongside
CB costs time/mem even on onts CB already solves) and hides soundness vs
completeness regressions.

**How to apply:** benchmark sbatch must save the FULL ore_runone JSON (wall_s,
peak_mb, status), not just status/gold — the first hybrid sweep discarded timing
and had to be re-run (hybrid_t.sbatch fixes this). Compute avg+median over the
matched both-solve set for fair head-to-head; report passrate per arm separately.
Directional gold classification only needs the few DIFF onts (MATCH = clean), so
keep heavy sig-diffing off the login node. [[project_km_hybrid_cb_ht]]
[[feedback_no_benchmark_hardcoding]]
