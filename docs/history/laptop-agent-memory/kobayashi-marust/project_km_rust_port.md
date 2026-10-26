---
name: project_km_rust_port
description: "Pure-Rust port of the KM classify orchestrator (replacing owl_classify.py + cb_to_ht.py); Phases 1-2 done+validated+committed, Phase 3 (races) next"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-18. User asked to remove ALL Python from the KM reasoner product and make
it pure idiomatic Rust ("Rust spirit"). Scope (user-confirmed): port the classify
path only — `owl_classify.py` (1146 lines) + `cb_to_ht.py` (542) + the frontend
name helpers — INCLUDING the HT path. KEEP the offline benchmark harness
(`oracle/ore/*.py`, drives Konclude/HermiT/ELK) and the ML trainer
(`route_tree.py`, needs sklearn). Plan file: ~/.claude/plans/sharded-wishing-hamming.md.

**Architecture (the key decision):** a typed SUPERVISOR/WORKER model, NOT
in-process. The RSS watchdog (SIGKILL a >18GB parallel attempt, retry
single-threaded) and the reasoner races (kill the loser) REQUIRE process
isolation — impossible safely in one process. So a new multi-call `km` binary:
`km classify` spawns the existing Rust workers (ofn/elc/kobayashi-marust/
tableau_cli) as subprocesses. Already achieves "zero Python in the classify path".
Deps: std only + a hand-rolled error enum + a Python-compatible JSON formatter (no
thiserror/libc yet; Phase 3 races will likely need libc::kill for the loser-kill
registry).

**Module tree** `engine/src/orchestrate/`: config.rs (env->typed Config, parsed
once, no mutated globals), tmpfile.rs (RAII TempPath), frontend_run.rs (ofn --meta
split, zero-copy giants), engine_run.rs (run_engine /proc/<pid>/statm RSS+wall
watchdog + run_engine_adaptive single-thread retry), mod.rs (classify() + output
mapping + residue + PyFmt), cb_to_ht.rs (clause->TInput + KM_HT_EMELIM). Bin:
src/bin/km.rs (classify + hidden cb_to_ht debug subcommand).

**Validation = byte-identity vs the Python, driving the SAME workers** (isolates
the orchestration port from engine drift). Build/test ONLY on the isolated IBEX
clone `/ibex/scratch/hohndor/km-rustport` (rsync laptop engine/ -> there; build via
sbatch `cargo build --release`, ~/.cargo/bin/cargo, account pi-hohndor). NEVER
km-incr (the live bigsweep 47599034 uses its binaries).

**DONE + committed (branch payg-strategy):**
- Phase 1 (1b50947): production path (ofn-split -> rbox_safe?elc:CB-adaptive ->
  output map; elc exit 0/3/4 + KM_QUERIES residue; ABox short-circuit). Validated
  40/40 vs owl_classify.py on a diverse ORE sample (= km-base config).
- Phase 2 (95d6dbd): cb_to_ht.rs. Validated TInput-identical 52/52 (26 onts ×
  {base, KM_HT_EMELIM}). Insertion-order ids + emission order replicated exactly;
  elim_complements iterates pairs in insertion order (chain-free `used` guard).
- Phase 3a (69af7c4): PRODUCTION races. race.rs (race_absorbed_plain SEQUENTIAL
  8s plain probe then absorbed; spawn_tableau + race_cb_vs_tableau concurrent via
  std::thread::scope, lazy 30s-grace nice-19 tableau, cb_to_ht routability guard,
  first valid wins). engine_run.rs: process-global LIVE child registry + CANCEL
  flag (libc::kill) = the _LIVE_ENGINES/_RACE_WON analogue. config.rs: typed
  KM_ABSORB*/KM_TAB_* . frontend_run::run_ofn_plain (KM_ABSORB on/off ofn).
  Added dep: libc. Validated 31/31 byte-identical vs owl_classify.py under the
  km-prod config (KM_ABSORB+KM_ABSORB_PORTFOLIO+KM_TAB_RACE, KM_TAB_BIN set),
  incl. tableau-race-WIN onts 2313/2066/5089 + 6246 plain probe + 9635.
  => km classify now matches the DEPLOYED production (564) config exactly.

**Phase 3b DONE + committed (9570d7c), validated 25/25 (IBEX job 47608771)**:
3 race configs all agree vs owl_classify.py (fallback HT-race byte-EXACT; elc
portfolio + HT-race race-mode race-invariant, IGNORE_DROPPED). ported into race.rs +
mod.rs + config.rs + engine_run.rs. `race_adaptive_vs_elc` (KM_ELC_PORTFOLIO:
spawn_elc_cert KM_ELC_CERT=2, scoped-thread CB adaptive raced vs certified elc,
RSS-watchdog on elc @ KM_ELC_PORT_MEM_GB=8, exit-4 spawns residue racer with
KM_QUERIES; elc/residue win => cancel_and_kill_engines). `spawn_ht`/`ht_routable`
(faithful + no inverse + no nominals; ALCQ ok) / `race_cb_vs_ht` (KM_HT_RACE,
mode fallback|race via a shared Mutex<Option<Result>> = Python's `done` dict;
fallback = CB always preferred, HT fills only when CB errors or > KM_HT_BUDGET_S=225;
core-reservation ht_reserved_threads = KM_THREADS-1 when set & >1). KM_ELC_FORCE
branch (run_engine RSS+wall budget; oom/timeout => fall through like exit 3) +
handle_elc_result helper. Engine threads threaded EXPLICITLY through cb_stack/
run_adaptive/race_absorbed_plain/run_engine_adaptive (Rust can't mutate global env
like Python's os.environ; same effect). resolve_residue now calls reset_cancel().
Validation harness validate_p3b.py (fallback=EXACT, portfolio/race=IGNORE_DROPPED
since winner-dependent dropped is race-variant but subs/unsat/consistent are
race-invariant by soundness+completeness). **TODO Phase 4**: full-corpus km-vs-owl_classify 0-diff across configs
(harness = /ibex/scratch/hohndor/km-rustport/validate_phase1.py; prod env exported).
**Phase 4 DONE**: full 587-corpus km classify vs owl_classify.py, deployed prod
config (absorb-portfolio+tab-race), 40/40 chunks 0 diffs (IBEX array 47609520,
semantic/race-invariant). Soundness net GREEN.

**Phase 5 DONE + committed (3688293), validated (IBEX 47613973): self-dispatch
km classify vs owl_classify.py 21/21 0-diff; km <sub> byte-identical to standalone
bins (ofn/elc/engine; tableau "diffs" were test broken-pipe artifacts, same
cli::run_tableau code).** ALL 5 PHASES COMPLETE — the reasoner is one pure-Rust
binary, zero Python to classify. Repoints landed (ore_runone.py + Classifier.java,
KM_BIN-gated w/ python fallback). CLAUDE.md updated (LOCAL only — it's gitignored).
NOT pushed yet (commits 1b50947/95d6dbd/69af7c4/9570d7c/3688293 local on
payg-strategy). NOT deployed (sweep 47599034 still running). Python NOT deleted
(user choice — owl_classify.py kept as oracle; dump_clauses --canon laptop-check
still works). User decided (2026-06-18): DON'T delete Python yet
(only repoint harness/plugin to `km classify`); DO collapse 4 workers into one
multi-call `km` binary (staged in-repo, NOT deployed while sweep 47599034 runs).
DONE (validating, IBEX 47613973): src/cli.rs with run_ofn/run_elc/run_engine/
run_tableau (logic moved from the 4 bin mains); lib.rs adds `pub mod cli` +
`pub mod tableau` (tableau.rs+hypertableau.rs use only super:: so they move to
lib cleanly); the 4 worker bins are now thin shims over cli::*; km.rs dispatches
ofn|elc|engine|tableau; config.rs worker resolution returns (program, prefix) —
KM_*_BIN override => standalone bin, else self_exe + subcommand (self-dispatch);
run_engine takes (program, prefix); all spawn sites (frontend_run, engine_run,
race) updated. Validation: (A) km <sub> byte-identical to standalone bins, (B)
km classify SELF-DISPATCH (no KM_*_BIN) vs owl_classify.py prod config. TODO once
green: repoint ore_runone.py + Classifier.java to km classify (repo only,
KM_BIN-gated w/ python fallback), update CLAUDE.md, commit. **NOT deleting**:
ofn/elc/kobayashi-marust/tableau_cli into `km <sub>`, delete owl_classify.py/
cb_to_ht.py/frontend.py/preprocess.py/el_route.py/route.py/rust_context.py, update
CLAUDE.md key-file map. Validation harness: validate_phase1.py (km vs owl, same
workers) + validate_cb.py (TInput). All on IBEX km-rustport (cargo at ~/.cargo/bin,
sbatch account pi-hohndor); commits 1b50947/95d6dbd/69af7c4 on payg-strategy.
[[project_km_rust_frontend]] [[feedback_no_heavy_laptop]]
