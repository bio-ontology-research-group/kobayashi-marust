# Rule tableau: backjumping on the careful path, one join order for both probes (2026-10-31)

Branch `fix/v155-rules-tableau` off `development/v1.5.5` (5b6988a6).
Commits 3e132c37 (backjumping and certificate resolution), 1105317a (join
order), then the commit carrying the docs and this directory. Design and
exactness argument: docs/DL-SAFE-RULES.md, sections "Backjumping on the
careful path (2026-10-31, v1.5.5)" and "One join order for both rule probes
(2026-10-31, v1.5.5)".

Host `ws` (56 cores) shared with other agents, load average 35 to 50 during
the runs. Every KM run had `KM_THREADS=1`; at most 3 KM runs at once.

## Binaries (`.work/agent-scratch/rules-tableau/`, `cargo build --release --bin km`, default features)

| name | commit | md5 |
|---|---|---|
| km-base | 5b6988a6 (development/v1.5.5) | e71c7ac082603345fcc58bb69fc1ae5e |
| km-bj1 | 3e132c37 code (backjumping only) | 404b7d2d04964cbe289a71250c4ce95c |
| km-bj2 | 1105317a (backjumping and join order) | 346324d52f93f6103fc796e27fc26040 |
| rules-cert-check | `.work/agent-scratch/lean-rules-route/bin/rules-cert-check-f9d32f54` (Lean sources unchanged on this branch) | 1ea9aff460f8ec5baffdcb8d033db743 |

## Item 1: backjumping on the careful path

### fr6 and fr270 (`timing/`)

| seed | km-base | km-bj1 alone, no checker | km-bj2 in the differential, checker on (3 parallel) | output |
|---|---:|---:|---:|---|
| fr6 | > 150 s (killed, rc 124; earlier agent: > 170 s) | 0.64 s | 1.22 s, certificate accepted | ok vs HermiT gold |
| fr270 | 41.78 s | 1.27 s | 3.00 s, certificate accepted | byte-identical to km-base (md5 126fd731...) |

### 400 `gen_finite_rules.py` seeds, 60 s, checker on

`diff_run_cert.py` (copied from `../lean-rules-route`), route auto,
`DIFF_THREADS=3`, `DIFF_KEEP=KM_THREADS=1`, `KM_RULES_LEAN_CERT` and
`KM_RULES_LEAN_CHECKER` on every run. Gold: HermiT with grounded built-ins
(`.work/agent-scratch/fr282-dropped-rules/seeds/gold`).

| binary | ok | WRONG | DROPPED | REFUSED | ERR | TIMEOUT | cert accepted | rejected | nocert (missing) | none | file |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| km-f9d32f54 (`../lean-rules-route`) | 366 | 0 | 0 | 0 | 0 | 34 | 232 | 0 | 0 | 134 | `../lean-rules-route/diff-f9d32f54.tsv` |
| km-bj1 | 380 | 0 | 0 | 0 | 0 | 20 | 246 | 0 | 0 | 134 | `diff-bj1.tsv` |
| km-bj2 | 380 | 0 | 0 | 0 | 0 | 20 | 246 | 0 | 0 | 134 | `diff-bj2.tsv` |

`none` are the `CONSISTENT 0` answers decided before the rule worker (as in
`../lean-rules-route`). km-bj2 wrote 251 certificate files (8.9 MB).

Per seed: no seed lost against km-f9d32f54 or against the fr282 merge run
(`../fr282-dropped-rules/diff-merge-5a3777c6.tsv`, 367 ok). TIMEOUT → ok
against km-f9d32f54: fr6, fr44, fr74, fr141, fr147, fr166, fr171, fr194,
fr225, fr250, fr272, fr304, fr310, fr350. km-bj1 and km-bj2 agree on every
seed. Remaining timeouts: fr57 fr61 fr65 fr97 fr133 fr135 fr140 fr159
fr191 fr243 fr248 fr253 fr276 fr287 fr295 fr300 fr320 fr323 fr346 fr371
(not analysed; fr248 is the CB-route slowdown recorded in
`../fr282-dropped-rules`).

## Item 2: the incremental rule probe join order (`incremental/`)

`../rules-route-followups/scripts/incr7278.py` on ore_ont_7278
(`.work/agent-scratch/subset-blocking-cost/inputs/ore_ont_7278.owl`): a
legacy session (`KM_SOURCE_SESSION=legacy`), then a revision adding
`ObjectPropertyAssertion(isPartOf III_2004 _2005)`, with
`KM_DATA_ASSERTION_AS_CLASS=1` (so the revision reaches the rule adapter,
`ht_delta`).

| binary | init | revision (incremental probe) | verdict |
|---|---:|---:|---|
| km-base | completed (its rule worker 6.98 s) | not finished; the whole run stopped at 600 s | none |
| km-bj2 run 1 | 12.72 s | 6.62 s, `ht_delta` | consistent, 259 subsumptions |
| km-bj2 run 2 | 13.51 s | 5.95 s, `ht_delta` | consistent, 259 subsumptions |

Batch `km classify` on the revised file: km-base 10.4 s / 11.0 s (with
`KM_DATA_ASSERTION_AS_CLASS=1`), km-bj2 9.9 s / 9.1 s, all four outputs
identical (md5 8296adb8..., `CONSISTENT 1`, 259 `SUB` lines), the same
answer as the incremental revision.

The fixture `engine/tests/fixtures/graph_data_rules.ofn` (a 7278 variant)
under the same script: km-bj2 revision 5.51 s; km-base did not finish
within 120 s. The new test
`source_incremental_rules::incremental_rule_probe_matches_the_batch_checker_on_graph_rules`
runs it.

## Tests (release, default features)

- New unit tests (`tests/tests-backjump-unit.txt`, with
  `KM_RULES_TEST_LEAN_CHECKER` set, so the second test also runs the Lean
  checker on the backjumped certificate):
  `careful_backjumping_skips_choices_the_refutation_does_not_use`,
  `backjumped_refutation_resolves_to_a_checkable_proof`: passed.
- `rules_lean_certificate` with `KM_REQUIRE_LEAN_CHECKERS=1`, the checker
  above and `KM_RULES_TEST_ORE_7278`: 7 passed
  (`tests/tests-rules-lean-cert.log`).
- Integration (`tests/tests-integration.log`): finite_data_rule_normalization
  3, finite_rule_taxonomy 4, ground_rule_source 4, rule_independent_abox_clash
  2, rule_taxonomy_nominal 9, rules_inert_sorts_routes 3, rules_route 5,
  source_incremental_rules 4 (with the new test): all passed.
- `--lib` filtered to `tableau::`, `incremental_rules`, `routing::`
  (`tests/tests-lib.txt`): 337 passed, 20 failed, 0 ignored. The 20 failures
  (`tests/lib-failed.txt`) are all in
  `../rules-worker-cost/tests/lib-tableau-frontend-failed.txt` (they need the
  `KM_HT_LEAN_*` checkers); no new failure.
- Rules gate: the gate script was not run end to end (it builds the Lean
  project with mathlib in this worktree). The Lean sources are unchanged on
  this branch. Its steps were run with the prebuilt checker: the 3 valid
  fixtures accepted, the 4 forged fixtures rejected, `rules_lean_certificate`
  7 passed. Part 2 (inert-sort release) was not run: no
  `rules-inert-sort-release-check` binary was available, and this branch
  does not touch the release.

## Reproduce

```
S=.work/agent-scratch/rules-tableau; F=.work/agent-scratch/fr282-dropped-rules
DIFF_KEEP=KM_THREADS=1 DIFF_THREADS=3 DIFF_KM_TIMEOUT=60 \
  DIFF_RULES_CHECKER=.work/agent-scratch/lean-rules-route/bin/rules-cert-check-f9d32f54 \
  DIFF_CERT_ROOT=$S/certs-bj2 TMPDIR=$S/tmp python3 -I diff_run_cert.py $S/km-bj2 \
  .work/agent-assets/2026-10-28-scratch/oracle $F/seeds/gold diff-bj2.tsv auto $(ls $F/seeds/ofn/*.ofn | sort -V)
KM_THREADS=1 python3 -I ../rules-route-followups/scripts/incr7278.py $S/km-bj2 ore_ont_7278.owl out.json \
  KM_DATA_ASSERTION_AS_CLASS=1 KM_THREADS=1
```
