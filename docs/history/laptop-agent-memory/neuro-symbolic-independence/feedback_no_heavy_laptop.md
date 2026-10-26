---
name: feedback_no_heavy_laptop
description: "Never run KM reasoner or cargo builds on the laptop; use ws for builds, unimatrix for benchmarks"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Do NOT run memory/CPU-heavy work on this laptop (lc-dell): no `cargo build`, no KM
reasoner/engine (`kobayashi-marust`, `owl_classify.py`, `el_route` completion), no
large classification. The user enforced this explicitly (2026-06-09).

**Why:** the laptop is resource-constrained; cargo LTO builds and KM saturation
spike memory and the user needs the machine responsive.

**How to apply:**
- Rust builds → host `ws` (10.73.11.158, cargo 1.85, 56 cores, 125 GB RAM). Work
  dir there: `~/km-frontend/` with `kobayashi-marust/` and `moose/` as siblings
  (so the Python frontend oracle locates moose). A ws-built binary (glibc 2.41)
  runs fine on unimatrix (glibc 2.39) — it avoids new symbols.
- KM benchmarks / classification → `unimatrix01` (Slurm; see [[reference_unimatrix_moose_env]]).
- Laptop is OK for: editing files, `git`, `ssh`/`rsync`, and the PURE Python
  normalisation frontend `dump_clauses.py` (no engine). Validate clause
  equivalence with `dump_clauses.py --canon` (reasoner-free) on the laptop;
  run classification-equality (`compare_classify.py`, runs the engine) on ws.
- Subagents with `cargo`/engine steps must drive ws/unimatrix over ssh, never
  build locally. The Agent tool runs the agent process ON the laptop, so its
  shell commands must ssh out for any heavy step.

Related: [[project_km_sroiq_program]], [[project_rust_frontend]].
