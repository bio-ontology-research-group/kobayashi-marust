# v1.6.0 certification on Ibex

ws could not certify v1.6.0-rc1 on 2026-11-11: the host was 92 percent busy
and its disk and commit memory were nearly exhausted by other jobs (see
`docs/V1.6.0-STATUS.md`). These files run the same steps on Ibex batch nodes
from a clone of the tag (git bundle of `v1.6.0-rc1`, commit 45543658).

| file | step | equivalent on ws |
|---|---|---|
| `pgo_build_ibex.py`, `pgo.sbatch` | PGO build | `tools/release/v155/pgo_build.py` with every ws path replaced by a staged copy: harness `.work/v152-correctness-1920` (Python files and `cleanup_evidence`), the frozen 22-input training selection, the input manifest with each row's `ibex_path` and `ibex_reference_directory`, the pinned rustc 1.95.0 (59807616e) with `llvm-tools`. Same flags, same 240 s training bound, same verification of every training answer. |
| `cert_ibex.py gates`, `gates.sbatch` | five Lean gates | `capture-gate.py` and `run-five-gates.sh`: the repository's gate scripts, the commit and a manifest of every tracked file checked before and after each gate, exit 0 and no `sorryAx` required. Lean toolchain v4.30.0-rc2 and the package cache (mathlib) copied from ws. |
| `cert_ibex.py rust`, `rust.sbatch` | full Rust suite | `run-full-rust.py`: worker build, `--lib` with the CI checker skips, every integration target but the three the gates run, serially, cleaned environment; refuses unless all five gates passed. |
| `java-step-ibex.sh`, `java-checkers.sbatch` | Java and checker steps | `java-step.sh` with Ibex Maven 3.9.1 and Java 24; `checkers-step.sh` unchanged. |

Receipts land in `<ibex root>/receipts/` and `<ibex root>/ctl/`; the Ibex root
is `/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111`.
