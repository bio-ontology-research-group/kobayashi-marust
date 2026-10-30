# Nominal-route coverage for v1.5.5 (2026-10-30)

Agent `nominal-coverage`, branch `fix/v155-nominal-coverage` off
`development/v1.5.5` (87fda54f). Argument and Lean obligation:
docs/NOMINALS-CB.md, "Inert object sorts in the nominal CB input
(2026-10-30)"; ordering-regime remeasurement: docs/PER-CONTEXT-ORDERING.md
section 8.

## Binaries

| name | what | sha256 |
|---|---|---|
| `km.base` | `cargo build --release` of 87fda54f, workstation | eb423992… |
| `km.fix` | first build of the change (copy made before the race) | 3a27f637… |
| `km.fix2` | final build (copy made inside each CB arm) | 3af1ce61… |
| `km-pgo-use` | v1.5.4 release binary, `.work/pgo-v154/km-pgo-use` | ac15b822… |
| IBEX `km.run9` | v1.5.4 design run 9 (0a0d73c8), `/ibex/.../v154-routing-20261026/km.run9` | a42e3816… |
| IBEX `km-87fda54f` | 87fda54f built on an IBEX node (`ibex/build.sbatch`) | see `ibex/` |
| IBEX `km-fix2` | final source built on an IBEX node | f076cb2b… |

The seed runs and the local ORE regression ran on the shared workstation
(56 cores, load 50 to 110 from other agents' jobs; the host also runs with
strict memory overcommit near its commit limit, which aborts workers
occasionally). The IBEX runs follow the protocol: one core
(`--cpus-per-task=1`), 240 s, 24 GiB, and the flags of the v1.5.4 paired
inventory (`KM_HT_DDB`, `KM_HT_NATIVE_FULL`, `KM_CACHE_CONFORMANCE`,
`KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE`, `KM_FAST_IRI_GRAMMAR`; `--lines`
output instead of the JSON graph).

## Files

- `seeds-base-auto.tsv`, `seeds-fix-auto.tsv`: `tools/diff_run.py` (the
  2026-10-29 runner, plus process-group kill on timeout and KM_TIMING
  stderr capture) on the 400 seeds of `gen_nomdata.py --no-inverse`
  2000-2399 (`results/agents/2026-10-29/per-context-order/gen_nomdata.py`),
  automatic route, 60 s, 3 workers, HermiT gold cached by the 2026-10-29
  agents. Columns: file, route, verdict, seconds, missing/extra
  subsumptions, missing/extra unsatisfiable classes, consistency mismatch.
- `seeds-base-timeouts-base-context-regime.tsv`: the 130 baseline timeouts
  rerun with `KM_NO_SEQ_ORDER=1`.
- `seeds-base-timeouts-bridge-defer.tsv`: the native bridge's datatype
  defer reason on each of them (`KM_ROUTE=ht_bridge KM_BRIDGE_PROGRESS=1`).
- `seeds-recheck.tsv`: every file whose verdict changed, rerun twice with
  `km.base` and `km.fix2`.
- `min/`: reductions (`tools/ddmin.py`, classify above 15 s;
  `tools/ddmin2.py`, CB engine above 10 s with every `D` disjunct dropped,
  a diagnostic only).
- `ore-local-v154-vs-fix.tsv`: `tools/ore_one.sh` on the 353 design-half
  inputs with individuals, v1.5.4 release binary against `km.fix`, 240 s,
  two streams side by side; columns name, rc and seconds for each binary,
  route, whether the copy was made, verdict (`tools/ore_cmp.py`).
- `ibex/`: sbatch scripts, `times-*.tsv` of the 9800/10874 runs, and the
  design-half regression on IBEX (`ibex/reg-*.tsv`).
- `tools/`: everything above, plus `inert_mirror.py` and `top_elim.py`
  (Python mirrors of the two passes used for the engine-level experiments),
  `dump_engine.sh` (a `KM_ENGINE` stand-in that keeps the CB engine's input),
  `pmp.sh` (gdb stack sampling; no perf on this host).

## Reproduce

```
km=.../km.fix2; S=<scratch>; export TMPDIR=$S/tmp
DIFF_THREADS=3 DIFF_KM_TIMEOUT=60 python3 -I tools/diff_run.py $km /nonexistent $S/gold out.tsv auto seeds/*.ofn
ORE_KEEP="KM_HT_DDB=1 ..." tools/ore_one.sh $km $S/ore fix 240 ore_ont_9800
sbatch --array=0-7 --export=ALL,KM_BIN=...,KM_TAGRUN=... ibex/run.sbatch
```
