# Lean coverage of two v1.5.5 changes (2026-10-30, lean-v155-coverage)

Branch `fix/v155-lean-coverage` off `development/v1.5.5` (87fda54f), worktree
`.work/worktrees/checkers-on`. Binaries: `engine/target/release/km` of that
worktree (plain `cargo build --release`), Lean checkers in
`lean/.lake/build/bin`. Docs: docs/NOMINALS-CB.md section 6 "Lean coverage",
docs/HYBRID-CB-HT.md section 9 "Lean coverage".

## Change 2: inert-sort release (rule checker)

- Lean: `lean/ContextCalculus/RulesInertSortRelease.lean`, checker
  `rules-inert-sort-release-check`, gate `lean/run-rules-certification-gate.sh`.
- ore_ont_7278: `KM_RULES_INERT_CERT=<dir> KM_RULES_INERT_LEAN_CHECKER=<bin> km classify ore_ont_7278.owl`:
  11 definers released (Q_14..Q_28), 8,552 sorted clauses, 8,541 worker
  clauses, 296 reserved concepts; certificate 1.9 MB, Lean accepts in 0.17 s;
  run 12.1 s, output identical to the run without the flags.
- Small fixture `engine/tests/fixtures/rules_inert_sorts/fr373.ofn` (finite-rule
  seed fr373 of results/agents/2026-10-30/rules-worker-cost): 2 released,
  accepted, output unchanged. `lean/testdata/rules-inert-valid.json` (accepted)
  and `rules-inert-forged.json` (a guard sort clause deleted from the worker
  input: rejected).

## Change 1: subset blocking (native hypertableau)

- Lean: `lean/ContextCalculus/HypertableauSubsetUnravelling.lean`, checker
  `ht-subset-unravelling-check`, added to `lean/run-ht-certification-gate.sh`.
- Seeds 507 and 639 (`t507.ofn`, `t639.ofn` = tests/ht_subset_blocking.rs
  cases), route ht_general, `KM_HT_INCRBLOCK2_CHECK=1`: 639 gives 24 terminals,
  all accepted, each with 2 or 3 blocking pairs (also under `KM_HT_BLOCK=5`);
  507 gives 7 accepted terminals. Example: `examples/seed639-accepted.json`.
- ALC seeds 1..700 (`ht_seeds.py`, HermiT gold from
  .work/agent-assets/2026-10-28-scratch): `seed-run/summary-inline-checker.txt`.
  The host was loaded by other builds; 262 seeds failed with EAGAIN when
  spawning workers and 117 are outside the ht_general fragment, so the
  differential part is not usable (183 ok, 0 wrong). Certificate counts:
  3,817 terminals accepted (1,634 with blocking pairs, on 214 seeds),
  552 rejected, 4 not emitted (a blocked node whose only admitted blocker is
  blocked or dropped). A second, offline-checked run (`OFFLINE=1`) kept 196
  rejected relabelled certificates from 26 seeds before it was stopped;
  retrying them with `relabel=false` left `seed-run/own-label-still-rejected.txt`
  (93) rejected; the run was stopped because `checkSat` on terminals of 50 to
  155 nodes with four-variable clauses ran for over an hour.
- Inspected rejection: `examples/seed2-relabel-rejected.json`
  (`diagnose_subset.py` prints the failing condition). The blocker's
  obligation `∃role0.C1` is witnessed by the inverse edge to its predecessor;
  the blocked position gains the trigger but its own predecessor lacks C1.
  Seed 2 is outside the ht_general fragment (one clause dropped), so its
  answer is not published; seeds 4, 78, 138, 154 and 312 also have rejected
  relabelled terminals and answered as HermiT in the first run.

## Reproduce

    lean/run-rules-certification-gate.sh            # KM_RULES_GATE_ORE_7278=<path>
    lean/run-ht-certification-gate.sh
    python3 -I ht_seeds.py KM CHECKER out.tsv 1 700  # JOBS, OFFLINE, OWN, KEEP

## Tests (`tests.log`, release, Lean checkers set, `KM_REQUIRE_LEAN_CHECKERS=1`)

- `--test rules_inert_sort_certificate`: 2 passed (fr373: 2 released; ore_ont_7278: 11 released; both accepted, outputs unchanged).
- `--test ht_subset_model_certificate`: 2 passed (507: 7 terminals, 639: 24, all accepted with blocking pairs).
- `--test ht_subset_blocking`: 4 passed.
- `--lib orchestrate::inert_sorts`: 11 passed (Lean accepted 2,358 releases of 3,000 random sorted sets and rejected all 521 verdict-changing unchecked releases).
