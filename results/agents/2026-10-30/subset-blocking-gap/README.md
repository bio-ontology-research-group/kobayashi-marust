# Subset blocking: inverse-witnessed existentials (2026-10-30, subset-blocking-gap)

Branch `fix/v155-subset-blocking-gap` off `development/v1.5.5` (bf7ca1a6),
worktree `.work/worktrees/fix-subset-blocking-gap`. Argument:
docs/HYBRID-CB-HT.md section 9, "Inverse witnesses".

Binaries (plain `cargo build --release`, kept in
`.work/agent-scratch/subset-blocking-gap/bin/`):

| name | commit | what |
|---|---|---|
| `km-head` | bf7ca1a6 | branch base |
| `km-fix1` | 41c08265 working tree before the conservative change | exact `back_need` (subtract successor witnesses, rescan from `pred(t)`) |
| `km-fix2` | 41c08265 | conservative `back_need`, every mode 1/5 run |
| `km-fix4` | aeec8578 | plus: merged victims, shared individuals and nominals excluded |
| `km-fix5` | b7a4bdc2 | plus: card arm excluded (final engine) |

`km-fix4` and `km-fix5` behave identically on `ht_general`
(`KM_NO_HT_CARD=1`: no first-class cardinality rules there).
Lean checker: `ht-subset-unravelling-check` copied from
`.work/worktrees/checkers-on/lean/.lake/build/bin` (Lean source unchanged on
this branch).

## Files

- `gen_alci.py SEED OUT`: nominal-free ALCI generator around the pattern
  (existentials and universals over inverse roles, excluded middles).
- `drive.py KM CHECKER GEN|CORPUS OUTDIR lo hi`: per seed, HermiT gold
  (cached; the Oracle of `.work/agent-assets/2026-10-28-scratch/oracle`),
  `km classify --lines` with `KM_ROUTE=ht_general`,
  `KM_HT_SUBSET_MODEL_CERT` (no inline checker, so the answer is the
  default route's) and `KM_HT_INCRBLOCK2_CHECK=1`, then Lean on every
  certificate (relabel, then own-label). Columns: seed, status (ok, WRONG,
  km-error, no-gold, no-input), accepted, rejected, checker timeouts
  (`CTO` s), not emitted, first reason. `CORPUS` reads the 700 seeds and
  gold of the 2026-10-28 scratch, as `lean-v155-coverage/ht_seeds.py`.
- `recheck.py`: re-runs Lean on kept rejected certificates with retries.
- `diag2.py CERT [own]`: Python re-implementation of `materialize` that
  names the failing condition (diagnostics only).
- `timing/`: `run1.sh` (one core, `KM_ROUTE=auto`, `KM_ROUTING_POLICY=v153`,
  from subset-blocking-cost), `timing.sh`, tables per binary,
  `prof/classify-prof.tsv` (`KM_HT_STATS=1`).

## Results

Question 1 (does the gap give wrong published answers?): no wrong answer
found. `alci-head.tsv` (base binary, generated seeds 1-1,500): 1,466 ok,
0 wrong, 25 errors, 9 without gold; 28,616 terminals accepted and 10,993
rejected by Lean on 870 seeds, so the checker route would have refused 870
seeds whose answer was right. 200 sampled rejected certificates re-checked
with retries: 200 rejected (`head-sample-recheck.txt`); `diag2.py` on the
same 200: each fails only by an unwitnessed obligation at a blocked
position (`head-sample-diag.txt`). Why the answers hold: docs section 9,
"Inverse witnesses" (the infinite unravelling copies all of the blocker's
neighbours, its predecessor included).

Fixed binary:

- `alci-fix5.tsv` (generated seeds 1-425, 501-663, 1001-1185; stopped for
  time): 747 ok, 0 wrong, 21 timeouts, 5 without gold; 19,679 accepted,
  0 rejected, 291 checker timeouts (30 s). Base on the same 773 seeds:
  5,539 rejected on 450 seeds.
- `corpus-fix4.tsv` (the 700-seed corpus, `km-fix4`, identical to the
  final engine on `ht_general`, checker timeout 20 s): 326 ok, 0 wrong,
  225 outside the fragment, 137 timeouts (120 s, with
  `KM_HT_INCRBLOCK2_CHECK=1`), 10 failed thread spawns, 2 without gold;
  10,506 accepted, 0 rejected, 880 checker timeouts, 31 not emitted.
  `corpus-timeout-sample.txt`: 10 sampled timeout seeds time out on the
  base binary too. Not emitted: seed 18 has 3 on both binaries; seeds 141
  and 548 have 7 and 5 with the fix and none on the base (a merged victim
  is the only admitted blocker; fail closed under the checker).
- `KM_HT_INCRBLOCK2_CHECK=1` aborted on no seed and not on 205/7499.
- Slower seeds (`alci-fix-slow-seeds.txt`): 9 generated seeds that the base
  answers in 0-16 s take 55-297 s (4) or more than 300 s (5) with the fix.

Cost inputs (`timing/table-final.tsv`, one core, alternating, host load
about 50): 205: base 129.1 / 130.4 s, fix 119.8 / 139.3 s; 7499: base
127.5 / 114.6 s, fix 126.9 / 123.3 s; outputs identical (md5); 205 runs
1,101,827 HT steps on both (`timing/prof/classify-prof.tsv`). The card arm
does not apply the condition; with it (`km-fix4`) 7499 took 1,146,968
steps and 104 s against 1,037,056 and 83 s (run side by side), and the
exact variant (`km-fix1`) took 205 to 165 s against 100 s.

Tests (release, Lean checkers from `run-ht-certification-gate.sh` exported,
`KM_REQUIRE_LEAN_CHECKERS=1`, `CARGO_TARGET_DIR` set):
`final-lib-tests.log` (`--lib tableau::hypertableau::`): 187 passed, 0
failed (without the checker variables 18 fail on missing
`KM_HT_LEAN_*`, as before); `final-integration-tests.log`:
empty_and_universal_data_ranges 10, explain_cli 8, has_key_rules 6,
ht_subset_blocking 4, ht_subset_model_certificate 3, source_axiom_drops 5,
top_nominal_data_successors 16; all passed. An earlier run had one failure
in empty_and_universal_data_ranges from a failed thread spawn (EAGAIN) and
one in top_nominal_data_successors (`probe_v6` on `ht_general` past 120 s),
which aeec8578 fixed.
