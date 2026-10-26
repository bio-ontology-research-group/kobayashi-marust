---
name: project_km_ibex_env
description: "IBEX parallel compute env for KM ORE sweeps (account pi-hohndor, python/3.11.0, validated end-to-end gold-clean) — second validation cluster when unimatrix is saturated"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-14. Stood up a SECOND ORE-validation cluster on IBEX (alias `ssh dragon`,
key-based) because unimatrix gets saturated by the iswc-rebuttal job array. Built
to validate KM ordering/residual experiments without waiting on unimatrix.

## Connection + account
- `ssh dragon` = ilogin.ibex.kaust.edu.sa, user hohndor, KEY-BASED (no password;
  the exec_ibex.py script wants a password file and fails — use `ssh dragon`).
- Slurm account = **`pi-hohndor`** (NOT c2014 — that combo is rejected). Partition
  `batch` (14d), `debug` (2h). Submit: `sbatch --account=pi-hohndor --partition=batch`.
- Login nodes are ZERO-COMPUTE — all builds/reasoning via srun/sbatch.

## Layout under /ibex/scratch/hohndor/km/
- `engine/` — rsynced engine source (from laptop `rsync -az --exclude target/ engine/ dragon:.../km/engine/`). Rust = rustup 1.96 at ~/.cargo (login-node install OK, download only). Build job: `km_build.sbatch` (16cpu/32G, builds in ~33s, 67+16 tests pass). Binaries in engine/target/release/{ofn,elc,kobayashi-marust,tableau_cli}.
- `moose/` — the SROIQ frontend moose (from unimatrix `~/nesy-genome/moose`, NOT the laptop's `~/Public/software/moose` which is the unrelated neuro-symbolic ML repo with no `sroiq` subpkg). Needed only because owl_classify imports frontend/el_route at module load.
- `harness/` — ore_runone.py (PATCHED: KM_PYBIN/KM_PY_DIR/KM_PYTHONPATH_OVR now env-overridable), owl_classify.py + py deps (frontend, el_route, preprocess, rust_context, ...), ore_canon.py.
- `gold/` — 587 konclude__*.sig.gz (relayed unimatrix->laptop->IBEX).
- `corpus/` — non-giant ORE onts (<100MB; 6.5G). Giants (3x ~450-590MB) not staged.
- `ore_km_ibex.sbatch` — reusable array sweep (module load python/3.11.0, MOOSE_HOME, KM_* env; CONFIG-specific env via --export).

## Key gotchas
- **python/3.11.0 module REQUIRED**: IBEX default python3 is 3.7.7; moose's
  `elpp/axioms.py` uses `type | type` (PEP 604, needs >=3.10). `module load python/3.11.0`.
- Run env for owl_classify: `MOOSE_HOME=.../km/moose`, `KM_PYBIN=$(command -v python3)`,
  `KM_PY_DIR=.../km/harness`, `KM_PYTHONPATH_OVR=.../moose:.../harness`, plus the
  usual KM_ENGINE_BIN/KM_OFN_BIN/KM_ELC_BIN/KM_RUST_FRONTEND=1/KM_RUST_EL=1.
- Transfers: laptop relays both ways (`ssh A 'tar c' | ssh B 'tar x'`); IBEX<->unimatrix not direct. Double-ssh streaming of 587 small gold files is slow (~20 min).

## VALIDATED end-to-end 2026-06-14
srun on cn604-18: classified ore_ont_1340 (absorption portfolio config, KM_ABSORB=1
+ KM_ABSORB_PORTFOLIO=1) in 8.3s, 23030 subs, status ok, sig **BYTE-IDENTICAL to
Konclude gold**. So the full Rust frontend->engine->sig->gold pipeline works on IBEX.

## Purpose
Run the [[project_km_absorption]] residual experiments (gated ordering A/B vs the
absorption baseline; cache-tableau + absorption on 5303) gold-checked here while
unimatrix is busy. See [[project_km_disjunction_blowup]] for the residual.
