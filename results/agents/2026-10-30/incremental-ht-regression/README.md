# Incremental HT regression, module-reuse expectation, worker-only variables (2026-10-31, incremental-ht-regression)

Branch `fix/v155-incremental-ht-regression` off `development/v1.5.5`
37b78fe3 (after the certificate-defects merge 895d4baf). Worktree
`.work/worktrees/fix-incremental-ht-regression`. Binary measured:
`.work/agent-scratch/incremental-ht-regression/bin/km-fix`
(`cargo build --release` of the sources of 11c71173, sha256
522e906e9d3667d684f1827ee43da430252e3811f5e2028b6e4fba7882da96a6).
All runs `KM_THREADS=1`.

## Item 1: the gate failure was the CB oracle, not the HT session

`before-ht-failure.txt`: `incremental_ht_reasoning` at 37b78fe3. After the
step that adds `⊤ ⊑ ⊥`, the HT session answers A, B, C below owl:Nothing
(right) and `classify_cb_fresh` answers `{A: [owl:Nothing]}` (rows of B and
C missing). Cause: the one-shot stop at a global refutation of b88c6253
(in 0e1bd99a, not in 8a417f98). Fix and argument:
docs/PER-CONTEXT-ORDERING.md section 13. No hypertableau, incremental HT,
subset-blocking, object-guard or r1600 code changed.

## Item 2: module-reuse expectation

`module_timing.py` / `module_timing.txt`: the count=1 negative case of
`common_data_core_prefers_plain_module_before_full_common_path`; module
revisions (`common_module_reuse`) 0.8 to 1.5 ms, a fresh full
classification of the same sources 12 to 27 ms, 5 repetitions.
Argument: docs/INCREMENTAL-REASONING.md, "Module reuse after native data
values".

## Item 3: worker-only variables

`engine/tests/worker_only_environment.rs`. With the v1.5.5 binary
`km-fix5` of subset-blocking-gap, `KM_HT_GLOBAL=1 km classify --route
ht_general` on the test's input prints `CONSISTENT 1`, `DROPPED 0` and no
SUB rows; with `km-fix` it prints the five SUB rows (B ⊑ D included) and a
notice on stderr. docs/HYBRID-CB-HT.md section 12.

## Tests

`suites.txt`: incremental_ht_reasoning 6/6, incremental_cb_reasoning 6/6,
source_incremental_rules 3/3, source_incremental 2/2, source_module_reuse
38/38, ht_subset_blocking 4/4, ht_subset_model_certificate 3/3,
global_refutation_closure 2/2, inconsistent_cb_rows 2/2,
worker_only_environment 1/1; 0 failed, 0 ignored. `lib-tests.txt`: lib
tests filtered on `routing::`, `reasoner::` and `incremental`, 195 passed, 0 failed.

`routing-gate-summary.txt`: `lean/run-routing-certification-gate.sh` end to
end (`KM_WORK_ROOT` in the scratch with its target linked to the worktree's
`engine/target`, `KM_CERT_LEAN_THREADS=3`, `KM_THREADS=1`): Lean
build 3,618 jobs, no `sorryAx`; 35 cargo steps, 277 passed, 0 failed,
1 ignored; "routing certification gate passed", 2,061 s.

## ALCI seeds

`gen_alci.py`, `drive.py` of `../subset-blocking-gap/` on seeds 1-1,500
(HermiT gold cached from subset-blocking-gap's `alci-head` run),
`KM_ROUTE=ht_general`, `KM_HT_SUBSET_MODEL_CERT`, `KM_HT_INCRBLOCK2_CHECK=1`,
Lean `ht-subset-unravelling-check` (copy in
`.work/agent-scratch/subset-blocking-gap/bin/`) on every certificate,
`CTO=60`. Rows: `alci.tsv` (columns as in drive.py). Summary: see below.
