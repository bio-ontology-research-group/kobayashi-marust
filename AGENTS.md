# AGENTS.md — kobayashi-marust (KM) reasoner

Guidance for Codex working in this repository. These instructions OVERRIDE
default behaviour. Read this fully before building, benchmarking, or editing.

## What this is

**kobayashi-marust (KM)** is a Rust reasoner for **SROIQ / OWL 2 DL**. It is a
hybrid of:
- a **consequence-based (CB) disjunctive context calculus** engine
  (Sequoia / ELK-style saturation, the `engine.rs` core), and
- an **EL++ completion fast path** (`elc`, ELK-style, for EL-safe ontologies), and
- an **ALC(HOQ) hypertableau** (`tableau_cli`, used only on small/validated
  fragments; see "Tableau is NOT a benchmark fallback" below).

The CB calculus is **machine-checked in Lean** (`lean/`). Soundness and
completeness of the core rules are mechanised; changes to the calculus logic
must be re-certified (see "Lean re-certification" below).

Goal of the active work: make KM's **ORE 2015** coverage match Konclude (587 ok)
while staying competitive on time and memory. Never silently approximate — the
target is a fully sound + complete Konclude competitor.

This repo was moved here from `~/Documents/papers/neuro-symbolic-independence/`
on 2026-06-10. It is a **standalone git repo** (remote
`github.com:bio-ontology-research-group/kobayashi-marust`), not a submodule of
the papers tree.

## WORKSTATION EXECUTION OVERRIDE (2026-07-16)

When `hostname` is `leechuck-office` and this checkout is
`/home/leechuck/Public/software/kobayashi-marust`, Codex is already running on
the host historically called `ws`. This section overrides the laptop-era host,
build, deployment, and benchmark directions below.

- Treat `ws` as local. Never run `ssh ws` or use a `ws:` transfer target.
- This checkout is the source of truth. Edit, test, commit, and push here.
- Run KM builds, release tests, and targeted diagnostics directly on this
  workstation. Use
  `CARGO_TARGET_DIR=/home/leechuck/km-frontend/kobayashi-marust/engine/target`
  to reuse the existing build cache.
- Do not edit or synchronize source into
  `~/km-frontend/kobayashi-marust`; it is an old source snapshot and now serves
  only as the Cargo target-cache location.
- Full sweeps and benchmark compute run through Slurm on remote host `ibex`,
  reached with `ssh ibex`. The active routing-matrix root is
  `/ibex/scratch/hohndor/km/routing_20260715`.
- Never run benchmark compute on an IBEX login node.
- The old laptop relay and `unimatrix01` workflow remains historical context,
  not the active workflow for this checkout.
- Use the workstation-adjusted `remote-connect` skill for remote operations.
  Host-alias and credential-isolation rules still apply to genuinely remote
  hosts.

## CRITICAL operational constraints

These are hard rules. Violating them wastes hours or wedges the laptop.

1. **NEVER build or run KM (cargo build / cargo test / the reasoner / benchmarks)
   on this laptop.** The laptop is for editing source and orchestrating remote
   work only.
   - **Builds + cargo tests → `ws`** (workstation, 125 GB / 56 cores).
   - **Benchmarks → `unimatrix01`** (Slurm cluster).
   - The ONLY laptop-safe check is `engine/.../dump_clauses --canon`-style
     reasoner-free canonicalisation (no saturation).
2. **Do not run memory-heavy anything on the laptop** (no large ontology
   parsing, no aggregation over giant outputs).
3. **Remote access uses the `remote-connect` skill and host aliases only.**
   Never read/cat the skill's `resources/` password files. Use `ssh ws`,
   `ssh unimatrix01`, `ssh unimatrix01-admin`.
4. **ws cannot scp to/from unimatrix directly.** Relay through the laptop:
   `scp unimatrix01:path /tmp/ && scp /tmp/file ws:dest` (and vice-versa).
5. **Kill remote processes by PID, not `pkill -f`** — `pkill -f` self-matches the
   ssh command and kills your own session.

## Hosts and where things live

- **laptop**: this repo at `~/Public/software/kobayashi-marust` (source of truth,
  edit here, commit here).
- **ws** (`10.73.11.158`, alias `ws`): build host. Working clone /snapshot at
  `~/km-frontend/kobayashi-marust`. `moose` (the Python sibling) at
  `~/km-frontend/moose`. Build with `cd ~/km-frontend/kobayashi-marust/engine &&
  nice cargo build --release`. Sync source from laptop with
  `rsync -a engine/src/ ws:km-frontend/kobayashi-marust/engine/src/`.
- **unimatrix01** (alias `unimatrix01`): Slurm benchmark cluster. Operates as
  user `hohndor`. Deployed binaries + harness live under `~/bench/`:
  - `~/bench/km/` — deployed binaries: `kobayashi-marust-batch` (the current
    winning engine = `KM_ENGINE_BIN`), `elc`, `ofn` (frontend; now the streaming
    build), plus `.bak` copies. `~/bench/km/py/` has the deployed `owl_classify.py`.
  - `~/bench/ore_harness/` — `ore_runone.py` (per-ont driver), `ore_km_batch.sbatch`
    (array job), `ore_aggregate_kmbatch.py` (aggregator).
  - `~/ore2015/pool_sample/files/` — the 592-ontology ORE 2015 corpus
    (`ore_ont_*.owl`). The 3 giants are 8737 / 15059 / 16744 (450–580 MB).
  - `~/bench/ore_jobs/` — chunk lists `kmchunk_NNN.txt`, results
    `res_kmbatch_NNN.jsonl`, sbatch stdout `kmbatch-<jobid>_NNN.out`.
  - Slurm: partition `debug`, submit with
    `--exclusive --exclude=unimatrix,node001` (use nodes 002–007). `sacct` is
    down — inspect via `squeue` + the sbatch `--output` file.

## Build & test (on ws)

```bash
# from the laptop:
rsync -a engine/src/ ws:km-frontend/kobayashi-marust/engine/src/
ssh ws 'cd ~/km-frontend/kobayashi-marust/engine && nice cargo build --release && nice cargo test --release 2>&1 | grep "^test result"'
```

Binaries land in `engine/target/release/`: `ofn` (frontend), `elc` (EL fast path),
`kobayashi-marust` (CB engine), `tableau_cli`.

To deploy a freshly built binary to the benchmark host, relay through the laptop:
```bash
scp ws:km-frontend/kobayashi-marust/engine/target/release/ofn /tmp/ofn-new
scp /tmp/ofn-new unimatrix01:bench/km/ofn        # (back up the old one first)
```

## Benchmark workflow (ORE 2015)

Config: 240 s timeout, 20 GB memcap, gold = Konclude (587 ok). The `kmbatch`
config in `ore_km_batch.sbatch` sets:
`KM_ENGINE_BIN=~/bench/km/kobayashi-marust-batch`, `KM_RUST_FRONTEND=1`,
`KM_OFN_BIN=~/bench/km/ofn`, `KM_RUST_EL=1`, `KM_ELC_BIN=~/bench/km/elc`,
`KM_PAR_MEM_GB=18`.

Run the full sweep (30 chunks):
```bash
ssh unimatrix01 'cd ~/bench && sbatch --array=0-29 ore_harness/ore_km_batch.sbatch'
```
Aggregate when done:
```bash
ssh unimatrix01 'cat ~/bench/ore_jobs/res_kmbatch_*.jsonl | python3 -c "import json,sys;from collections import Counter;rows=[json.loads(l) for l in sys.stdin if l.strip()];print(Counter(r[\"status\"] for r in rows))"'
```
Correctness vs gold uses the per-ont signature (`.sig.gz`, sorted subsumptions +
`#UNSAT` block); compare KM's `~/bench/ore_out_kmbatch/km__<ont>.sig.gz` to
`~/bench/ore_out/konclude__<ont>.sig.gz`. The aggregate scripts report an
unsound / incomplete / both-disagree table.

## Architecture: the classify pipeline

The classify orchestrator is now **pure Rust**: `km classify <ont.ofn>`
(`engine/src/bin/km.rs` + `engine/src/orchestrate/`), a typed supervisor that
spawns its worker reasoners as subprocesses. `km` is a **single multi-call
binary**: `km ofn|elc|engine|tableau` are the workers, which `km classify`
invokes by re-execing itself (or a `KM_*_BIN` override). The shared worker logic
lives in `engine/src/cli.rs`; the standalone `ofn`/`elc`/`kobayashi-marust`/
`tableau_cli` binaries remain as thin shims over it. Classifying needs **zero
Python**. `engine/py/owl_classify.py` is the now-superseded reference (kept, not
yet deleted; it drives the same workers and was the byte-identity oracle for the
port — full 587-corpus 0-diff). Validate orchestration changes against it.

The pipeline (the Rust `km classify` path; `owl_classify.py` mirrors it):

1. **Frontend** `ofn` (`engine/src/bin/ofn.rs` + `engine/src/frontend/`): parses
   OWL functional syntax → normalised **DL-clause** JSON (`{"clauses":[...]}`)
   plus side data (`iri_map`, `named`, `declared`, `el_rbox_safe`). With `--meta`
   it streams clauses to a file and side data to a meta file (zero-copy hand-off;
   the clause set never enters Python).
2. **Routing**: if `el_rbox_safe` → try `elc` (exits 3 if not actually EL, then
   falls through). Else → the **CB engine** via `_run_engine_adaptive`
   (parallel-first under an RSS watchdog at `KM_PAR_MEM_GB`, single-threaded
   retry on memory blow-up).
3. **Output**: subsumptions keyed by full IRI; the harness canonicalises with
   `ore_canon.localname`.

JSON contract (`engine/src/json_io.rs`): a clause is `{body:[atom], head:[atom]}`;
atoms are `concept` / `role` / `eq`; terms are `var` / `ind` / `aux` / `fun`.
This same `{"clauses":[...]}` shape is the stdin contract for both `elc` and the
CB engine.

## Current state (2026-06-11)

- Branch **`payg-strategy`**, HEAD **`cd60ce3`** (pushed). This is the active
  branch — keep committing here unless told otherwise.
- **ORE coverage: 564 ok / 26 timeout / 1 memout** (confirmed, full sweep job
  5690). Was 551 when this work began. The latest +2 are the recovered giants
  ore_ont_16744 (Skolem-exclusion EL routing, `72acb3a`) and ore_ont_8737
  (clone-free EL completion, `cd60ce3`; 205.7 s wall, 9.5 GB peak, sig
  byte-identical to gold).
- **Soundness vs gold**: 554 agree, 6 incomplete, 4 unsound, both-disagree = 0
  (sweep 5690 aggregate). Do not let this regress. km has the lowest median
  peak memory of the five reasoners.
- The 1 remaining memout is 16444 (CB-engine ~20 GB blow-up). The 26 timeouts
  are dominated by the live-disjunction family (10702, 9540, 1603, 10860,
  5303, ...) plus context-explosion onts (15491, 6682, ...).

### Recent landed work (newest first; see CHANGELOG.md)
- **Clone-free EL completion hot loop** (`cd60ce3`): `in_edges` as flat
  `Vec<Vec<(parent,role)>>`, index-loop NF4 rules, reused conclusion buffer.
  8737 classify 252 → 221 s standalone; in the pipeline 8737 went timeout → ok.
- **EL canonical-model completeness certificate** (`cb508c6`, `KM_ELC_CERT=1`,
  default OFF — inert on ORE, sound opt-in for near-EL onts).
- **Skolem-exclusion in EL-routing relevance** (`72acb3a`): recovered 16744.
- **Frontend streaming parse + compact DLClause** (`ac153ef`): frontend peak
  19.2 → 3.6 GB on ore_ont_8737, byte-identical output; recovered 15059.
- **Batched propagation** (`06d91d0`), **adaptive threading**
  (`6798758`+`b199d3d`), **Hyper backtracking join** (`2c67c61`): see CHANGELOG.

### Residual (the hard part — needs real work, not constant-factor tweaks)
- **Live `∀ + ⊔` disjunction** ontologies: incomparable 2–3-literal disjunctive
  facts that subsumption cannot prune; root cause is the root-context
  mutually-incomparable ordering in `calc.rs` `pred_lteq`. Fix = Sequoia-style
  ordered resolution in root contexts + Lean re-cert (changes what is derived).
- **Role-chain propagation volume.**
- **Correctness tail**: 4 unsound (under-detected unsat incl. 8941 ALC-forall),
  6 incomplete; several involve contested gold (HermiT also differs from
  Konclude on 12 onts).
- **Tableau is NOT a benchmark fallback**: `tableau_cli` errors or hangs on real
  ORE ontologies (validated only on small synthetic + kinship). Do not wire it
  into the benchmark.

## Soundness & Lean re-certification

- **Every full release, including v1.3.0 and all later full releases, requires
  Lean certification from the exact tagged source.** Run every production
  certification gate and reject any `sorryAx` before tagging. Benchmarks,
  Rust tests, Java tests, and prior-release certificates do not replace this
  gate. A newly added publication path must first be added to the Lean boundary
  and its axiom audit.

- **Re-certify in Lean ONLY for changes to the CB-calculus logic** (rule
  derivations, ordering, redundancy, what gets derived). Saturation is monotone
  and confluent, so schedule/enumeration-order changes (batching, join order,
  threading) are fixpoint-preserving and need NO re-cert — but you must argue why
  the derived set is unchanged.
- The **frontend** (`ofn`) is not calculus logic: validate frontend changes by
  **byte-identical clause+meta output** vs the prior binary across the corpus
  (the giants differ only in resource use, never in output).
- After any change that could affect results, run the soundness-vs-gold table and
  confirm unsound/incomplete/both-disagree do not regress.

## Git & conventions

- Work on **`payg-strategy`**; commit here; push to `origin`.
- End commit messages with:
  `Co-Authored-By: Codex Fable 5 <noreply@anthropic.com>`
  (older commits on this branch used `Codex Opus 4.8` — match whichever model is
  actually running, or keep the branch convention if asked).
- **Writing style** (papers/docs): NO em-dashes (en-dashes are fine); avoid
  thus / uniquely / comprehensive / rigorous / robust; active voice; de-emphasise
  "machine-checked".
- `target/` and `target-dhat/` (≈ 320 MB) and `lean/` build artifacts (≈ 8 GB)
  are the bulk of the on-disk size; the `.git` is tiny. Do not commit build
  artifacts.

## Key file map

- `engine/src/frontend/` — OWL functional-syntax frontend (parse → normalise →
  augment → DL-clause JSON). `sexpr.rs` (tokeniser/parser), `parse.rs` (AST),
  `normalise.rs` (clausifier), `preprocess.rs` (augment: transitivity, chains,
  nominals, domain/range), `clauses.rs` (DLClause + JSON), `rbox.rs`, `iri.rs`,
  `syntax.rs`, `mod.rs` (`ofn_to_clauses` orchestration).
- `engine/src/engine.rs` — the CB disjunctive-context saturation engine (Hyper /
  Pred / Succ / Eq / Ineq / Factor / Elim rules, inter-context messaging).
- `engine/src/reasoner.rs` — query orchestration + parallelism.
- `engine/src/elcomplete.rs` — EL++ completion (the `elc` core).
- `engine/src/tableau.rs` — ALC(HOQ) hypertableau.
- `engine/src/{calc,clause,json_io}.rs` — terms/atoms/signature, clause types,
  JSON contract.
- `engine/src/bin/km.rs` — the multi-call entry point (`km classify` orchestrator
  + `km ofn|elc|engine|tableau` workers); the single binary the reasoner ships as.
- `engine/src/cli.rs` — the worker entrypoints (`run_ofn`/`run_elc`/`run_engine`/
  `run_tableau`) shared by `km <sub>` and the standalone shim binaries.
- `engine/src/bin/{ofn,elc,tableau_cli}.rs` — standalone worker shims over `cli`.
- `engine/src/orchestrate/` — the pure-Rust classify orchestrator (config, frontend
  invocation, engine/race runners, cb_to_ht, output mapping). Replaces
  `owl_classify.py` + `cb_to_ht.py`.
- `engine/py/owl_classify.py` — the now-superseded reference orchestrator (kept as
  the byte-identity oracle; not deleted).
- `lean/` — the Lean formalisation of the calculus.
- `CHANGELOG.md` — full result tables and rationale for each change.
- `docs/HYBRID-TABLEAU.md` — the (aspirational) CB-vs-tableau router design.

## Auto-memory pointers (laptop)

Detailed running notes are in the laptop's auto-memory
(`~/.Codex/projects/.../memory/`), notably: `project_km_cb_scaling`,
`project_km_audit`, `project_km_correctness_audit`, `project_km_hybrid_tableau`,
`project_km_nominals_routing`, `project_km_rust_elc`, `project_km_rust_frontend`,
`feedback_no_heavy_laptop`. These hold the deeper diagnosis history.
