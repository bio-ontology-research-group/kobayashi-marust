# Lean coverage of the nominal CB input (2026-10-31)

Agent `lean-universal-definer`, branch `fix/v155-lean-universal-definer`
off `development/v1.5.5` (bb3fb9a0). Argument and Lean obligation:
docs/NOMINALS-CB.md, "Lean coverage of the nominal CB input (2026-10-31)";
checker inventory: docs/CHECKERS-ON.md section 1.1.

## What was measured

- `lean/run-rules-certification-gate.sh` (extended with part 3, the
  nominal CB input): passed; `rules-gate-summary.txt` lists the axiom
  audit lines, the randomized certificate counts and every test result.
  Lean accepted 2,000 of 2,000 nominal CB input certificates of the random
  clause sets and rejected all 135 eliminations of `Q_2` without a unit
  fact that change an answer (DPLL over consistency, satisfiability and
  subsumption of the source classes).
- `branch-tests.txt`: `cargo test --release --lib` plus the nominal
  integration tests on f83ddf5f. The 21 failing lib tests are the set
  recorded without Lean checkers in
  `results/agents/2026-10-30/checkers-on-suite/tests/lib-all-without-checkers.log`
  (identical names; they need HT/CB checker executables that this run did
  not build). `data_value_singleton_next_to_nominal_successors` fails on
  the base as well (`results/agents/2026-10-31/nominal-exchange/data/tests-targeted.txt`;
  cause analysed in `results/agents/2026-10-30/data-values-3/README.md`).
  No test fails on this branch that passes on the base.
- `ore9800-timing.txt`: ORE 9800 automatic route, `km classify --lines`,
  `KM_THREADS=1`, two runs each, shared workstation (load 7 to 12):
  10.2 s / 178 MB without checkers, 12.2 s / 725 MB under
  `KM_LEAN_CHECKERS` with only `nominal-cb-input-check` in the directory
  (7.0 MB certificate, accepted); outputs byte-identical. Without a
  certificate variable the copy does the same work as before.

## Reproduce

```
source lean/checker-env.sh lean/.lake/build/bin   # optional
bash lean/run-rules-certification-gate.sh
mkdir chk; ln -s $PWD/lean/.lake/build/bin/nominal-cb-input-check chk/
KM_LEAN_CHECKERS=$PWD/chk KM_TIMING=1 km classify --lines ore_ont_9800.owl
KM_ROUTE=nominals KM_NOMINAL_CB_INPUT_CERT=certs/ \
  KM_NOMINAL_CB_INPUT_LEAN_CHECKER=lean/.lake/build/bin/nominal-cb-input-check \
  km classify --lines engine/tests/fixtures/nominal_inert_sorts/m2032_min.ofn
```

## Binaries

`binaries.sha256`: `km` built from f83ddf5f (`cargo build --release`,
workstation) and `nominal-cb-input-check` built from the same commit
(Lean v4.30.0-rc2). Both were deleted after the runs.
