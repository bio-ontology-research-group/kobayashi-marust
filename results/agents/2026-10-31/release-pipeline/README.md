# Release pipeline dry run (2026-10-31)

Agent `release-pipeline`, branch `fix/v155-release-pipeline` (off
`development/v1.5.5` at 895d4baf). The tools are in `tools/release/v155/`;
the procedure is `docs/RELEASE-1.5.5-PROCEDURE.md`. Nothing here is a
release measurement: the held-out, pool and Konclude runs wait for the
tagged candidate.

## What was measured

1. `pgo-dryrun-895d4baf/`: receipts of `tools/release/v155/pgo_build.py` on
   commit 895d4bafbbaae7be33f9b0ef0fa19085e3b05c6d (the head of
   `development/v1.5.5` on 2026-10-31). The binary `km-v1.5.5-rc-pgo` has sha256
   `0951650a834b426f3d7395c9fc53ef7e7bd0b01ad2689a7c55ee0dd0ec8f3289`, needs at
   most GLIBC_2.34, and passed the build-log audit (4,362 trained functions,
   no profile mismatch, no discarded non-zero count). All 22 training inputs
   were verified against the pinned references; 35 raw profiles (v1.5.4: 36).
   Times on a shared ws (CPUs 17-24): instrumented build 551 s, training
   255 s, merge 1 s, profile-use build with the glibc wrapper 703 s, total
   1,531 s. The binary stays at
   `.work/agent-scratch/release-pipeline/pgo-895d4baf/km-v1.5.5-rc-pgo` and on
   Ibex under `v155-release-20261031/binaries/`.
2. `reproduce-v154/`: `aggregate.py --reproduce-v154` on the v1.5.4 run
   records (`.work/v154-release-cert/data/`). It reproduces every number of
   v1.5.4's `build-completion.json` exactly: 556 common inputs, mean ratio
   1.1717, median ratio 1.0771, engine only 1.025 / 1.151, policy only
   1.070 / 1.104, noise floor 0.936 / 1.179, allowed sum 2,405.117 s,
   excess 156.729 s, Konclude 558 against 554 on 534 common inputs (mean
   4.854 s against 2.599 s, median 0.218 s against 0.246 s), and the largest
   deltas. The only difference: `flagged_wrong` is recomputed from the
   comparisons and lists `ore_ont_3794` (excused by `adjudications.json`),
   which the v1.5.4 protocol runner never marked. The S1 verdict on these
   records is NOT_MET (no loss: 558 < 560; mean 1.172), as it was for v1.5.4.
3. `pool-check-on-v153-20261025/`: the pool zero-wrong check run on the
   v1.5.3 run of 2026-10-25 (1,920 rows, 1,708 admitted): 1,662 verified,
   only `ore_ont_3794` flagged. That record carries no answer fingerprint, so
   the check does not excuse it (fail closed); the v1.5.5 runner records the
   fingerprint.
4. Smoke job on Ibex: see "Smoke job" below.

## Reproduce

```bash
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work
python3 worktrees/fix-release-pipeline/tools/release/v155/aggregate.py --reproduce-v154 --out <dir>
python3 worktrees/fix-release-pipeline/tools/release/v155/pgo_build.py --worktree <clean worktree> --root <dir>
```

## Smoke job

Array 54861589 on `/ibex/scratch/projects/c2014/hohndor/km/v155-release-20261031`
(`smoke.sbatch`, six inputs from `inputs/smoke-inputs.txt`: ore_ont_10053,
3529, 1115, 15125, 3696 held-out, 5760 design half). All three tasks
COMPLETED (14 s, 15 s, 46 s; cn512-27-r and cn512-27-l, gold-6248).

| Task | Binary | Measured | Verified | Wrong |
|---|---|---|---|---|
| 0 RC | 0951650a… (dry-run PGO) | 6 | 6 | 0 |
| 1 v1.5.3 | 2470b041… (release asset) | 6 | 6 | 0 |
| 2 Konclude | e8dd5373… (2026-10-04 build) | 6 | 5 against HermiT/Openllet/JFact; 6 of 6 identical to the 2026-10-04 answer | 0 |

The chunk records are in `smoke-54861589/`, with the aggregation output on
them (`aggregate-build-completion.json`; its S1 verdict is meaningless on six
inputs and is there only to show the pipeline runs end to end).
