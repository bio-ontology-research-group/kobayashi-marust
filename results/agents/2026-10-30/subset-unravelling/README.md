# Subset blocking: the predecessor fold (2026-10-31, subset-unravelling)

Branch `fix/v155-subset-unravelling` off `development/v1.5.5` (0e1bd99a),
worktree `.work/worktrees/fix-subset-unravelling`. Argument and Lean
statement: docs/HYBRID-CB-HT.md section 9, "Predecessor fold".

Binaries (`cargo build --release --bin km`, kept in
`.work/agent-scratch/subset-unravelling/bin/`, md5 in `binaries.md5`):

| name | source | what |
|---|---|---|
| `km-base` | 0e1bd99a | branch point (conservative `back_need` of 5d80aad7) |
| `km-fix1` | 0e1bd99a + predecessor fold, relaxed `back_need`, merged victims no candidates | used for the ALCI run |
| `km-fix2` | fix1 + victims' successors no candidates either | dropped (seed 548 runs past 120 s); binary deleted |
| `km-fix3` | 8164d5e5 (3e58e0ab differs from it by two blank lines) | fix1 + `Ext::live_pred` in mode-1 indirect blocking and the certificate (final engine) |
| `ht-subset-unravelling-check` | 1998f230 | Lean checker with `predecessorFolds` |

fix1 and fix3 differ only when nodes are merged; the generated ALCI seeds
have no number restrictions or functional roles (`grep` over the 1,500
ontologies), so no merge happens there and the ALCI run of fix1 stands for
fix3.

## Files

- `drive.py`, `gen_alci.py`, `diag2.py`: copied unchanged from
  `../subset-blocking-gap/` (usage there). `JOBS=4`, `CTO=30` (checker
  budget per certificate), `KM_HT_INCRBLOCK2_CHECK=1`, 120 s per km run.
- `alci-fix1.tsv`: generated seeds 1-1,500 (1,478 missing: the driver
  ended without it), `alci-rerun.tsv`: seeds 1478 and 645 rerun with fix3.
- `corpus-fix3.tsv`: the 700-seed ALC corpus (`CORPUS`), fix3.
- `lost.sh`, `plain.sh`, `lost-seeds.txt`: the five seeds the conservative
  rule lost, one core, `ht_general`, with the inline checker (`lost.sh`) and
  without certificates (`plain.sh`).
- `timing/`: `run1.sh`, `timing.sh` (one core, card-arm route,
  alternating base and fix3), `table.tsv`, `md5.txt` (outputs).
- `m2197-timing.txt`: `top_nominal_data/m2197.ofn` on the `nominals` route,
  base and fix3 side by side.
- `lib-tests.log`, `integration-tests.log`,
  `integration-top-nominal-rerun.log`, `ht-gate-summary.log`.

## Results

See docs/HYBRID-CB-HT.md section 9, "Predecessor fold", "Measurements".
