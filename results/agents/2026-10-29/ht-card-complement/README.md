# ht_general complement-definer fold (2026-10-29)

Branch `fix/v155-ht-card-complement` from `5cc0bccf`. Binaries: `km-head`
(5cc0bccf), `km-fix` (fold fix only, bbbc3210), `km-fix-share` (fold fix and
definer sharing on every mechanism, 32de40b7).

## Inputs

- `inputs/repro.ofn`: the reported data-cardinality reproducer.
- `inputs/repro_obj.ofn`: the same with an object property.
- `inputs/prop2.ofn`: no cardinality; `Two ⊑ Has`, `T2 ⊑ Two`,
  `No ≡ ¬Has`, `AtMostOne ≡ ¬Two`.

Expected for all three: `No ⊑ AtMostOne` and `Two ⊑ Has` (plus `T2` edges).

## Route matrix (`routes-matrix.txt`)

Every named route on all three inputs, `km-head` and `km-fix-share`, 90 s
cap. `ok` = `No ⊑ AtMostOne` reported; `MISS` = only `Two ⊑ Has`;
`declined` = structural-gate or fragment refusal.

| binary | ok | MISS | declined |
|---|---:|---:|---:|
| km-head | 99 | 7 | 17 |
| km-fix-share | 106 | 0 | 17 |

Head misses: `ht_general` (all three), `tableau` (all three), `ht_features`
(`prop2`). The automatic route answered all three correctly on both.

## Seed differential (700 ALCHIQ seeds, HermiT gold, `KM_ROUTE=ht_general`)

`rerun.py` is `eval.py` (paths adapted from results/agents/2026-10-28/bridge)
with an explicit seed list and the last stderr line kept for `ERR`. 60 s cap,
8 workers.

| binary | ok | WRONG | declined (`drops 1 clause`) | hermit-error |
|---|---:|---:|---:|---:|
| km-head (rerun 1) | 286 | 38 | 374 | 2 |
| km-fix-share (reruns 1-7) | 325 | 3 | 370 | 2 |

Per seed, head to fix: 35 WRONG to ok, 4 declined to ok, 1 WRONG to WRONG
(639: 5 missed subsumptions to 2), no ok or declined seed became WRONG. The
three remaining WRONG (103, 507 missed inconsistency; 639) are the same in all
seven fix reruns. Head seed 540 alternates between ok and WRONG across runs
(parallel classification order); with the fix it is ok in all seven reruns.

The first `eval.py` runs (`seeds-ht_general-head-eval.txt`: 37 WRONG;
`seeds-ht_general-fold-only-eval.txt`: 3 WRONG;
`seeds-ht_general-fix-eval-anomalous.txt`: 2 WRONG, 465 ERR) ran while the
machine load was about 50. Their extra `ERR`s were not reproducible
(`eval.py` discards stderr). Inferred cause: the reruns show intermittent
`ERR`s on every binary with this signature: the worker
aborts (exit 134) with `spawn HT phase-1/phase-2 worker: Os { code: 11,
WouldBlock }`, a failed thread spawn, so no answer is published.

## Tests

`integration-tests-gate-removed.log`: the four integration suites with the
gate removed (32de40b7). `data_assertions_carried::unproxied_assertions_can_hide_a_clash`
exceeds its 60 s bound on `nominals`; head does too (57 s standalone, over
60 s under load).

`lib-tableau-tests.txt`: `cargo test --release --lib tableau::` at 32de40b7,
236 passed and 20 failed; the 20 are the tests that need the `KM_HT_LEAN_*`
checker variables (pre-existing, untouched). `--lib cb_to_ht::` (52, including
the two new fold tests) and `--lib frontend::normalise::` (25) pass.

## Follow-up: subset blocking (commits 08dcae29, 75dd4d46)

The three seeds still wrong after the fold fix (103, 507, 639) and the
data-range excluded middle that kept `ht_general` out of
`excluded_middle_of_complement_ranges` have one cause: subset blocking in
the native hypertableau (modes 1 and 5) admitted a blocker whose extra
literals a clause reads across the blocked node's edge
(docs/HYBRID-CB-HT.md section 9).

`subset-blocking/`: `ddmin.py` (line-level delta debugging against
`cb_plain1`), `htg.sh` (the `ht_general` bundle under `KM_ROUTE=manual`, so
`KM_HT_BLOCK` and `KM_HT_PAR` survive), the minimal cases `min103.ofn`,
`min507.ofn`, `min639.ofn`, the hand-reduced `t6.ofn` (two axioms), the
excluded-middle cases `case1-9.ofn`, and `c1e.ofn`, the automatic-route
witness.

Verified on the minimal cases:
- `t6`/`min103`: inconsistent (HermiT). Head `ht_general`: consistent.
  `KM_HT_BLOCK=0,2,3,4,6` (whole-label modes): inconsistent; 1 and 5:
  consistent.
- excluded-middle cases 1, 2, 5, 7: head `ht_general` missed `A ⊑ C` /
  `H ⊑ C`; modes 0, 2, 3 gave them; mode 1 did not.
- `c1e.ofn`: inconsistent (HermiT, `nominals`). Head `auto` selects
  `certified_card_proxy_abox`, whose card arm (mode 5) printed
  `CONSISTENT 1`. Fixed binary: `CONSISTENT 0`.
- `reach-head.txt`: head on the automatic and portfolio routes
  (`auto`, `production_all`, `certified_nominals`, `certified_card_nominals`,
  `certified_card_proxy_abox`, `tab_race`, `ht_rules`) for the minimal
  cases: only `c1e` on `auto` and `certified_card_proxy_abox` differs from
  the CB gold.

Seeds (`seeds-ht_general-subset-fix.txt`, 4 workers, 60 s cap, under heavy
machine load): 325 ok, 0 WRONG, 232 declined (`drops 1 clause`), 137
timeouts, 4 aborted thread spawns (`WouldBlock`, a commit-limit failure; seed
76 reruns ok), 2 hermit-error. Against head rerun 1 (286 ok, 38 WRONG,
374 declined): 38 WRONG to ok, 3 declined to ok, 2 ok to no answer (76, the
transient abort; 425, a timeout: it uses `ObjectInverseOf`, and the checked
pairs no longer admit the subset blocks that let head finish). 136 of the 137
timeouts are inputs head declined after running (`drops 1 clause`, all with
inverse roles); the worker runs before that decision because an
inconsistency over the weakened input would still be exact.

Tests at 75dd4d46 (`integration-tests-subset-fix.log`,
`lib-cb_to_ht-tableau-tests-subset-fix.txt`): bridge_generator_soundness 3
passed, data_assertions_carried 9 passed, empty_and_universal_data_ranges 10
passed (with `ht_general` back in `excluded_middle_of_complement_ranges`),
forced_route_fail_closed 5 passed, ht_subset_blocking 4 passed (all four fail
against the head binary), universal_role_and_top_data_range 11 passed and 2
ignored; `--lib cb_to_ht:: tableau::` 288 passed, 20 failed, the same 20
`KM_HT_LEAN_*` checker tests as before.

## Cost on the automatic route over ORE (`ore-cost/`)

Binaries: `c604f80d` (before the subset-blocking fix; same code as
32de40b7) and `e8b63ea9` (after). `KM_ROUTE=auto`, 300 s cap, one file at a
time, `taskset -c 0-3` (4 cores; the worker caps its threads to them).

Selection. The run-8 per-input route records are on IBEX only (array
54741000), so the selected route of every design-half input (1,123,
`split.json`) was recomputed with `km profile` at e8b63ea9
(`design-selected-routes.txt`): 409 elc, 409 production_all, 295
certified_nominals, 7 ht_rules, 2 certified_card_nominals, 1
certified_card_proxy_abox; none selects `tab_race`, `card_*` or
`ht_general`. The native hypertableau runs on the automatic route through
the card arm, which `production_all` and the `certified_card_*` bundles
carry next to the native bridge. The set is the three `certified_card_*`
inputs plus every `production_all` input with number restrictions or
functional roles and no datatypes (`design-profiles.txt`: route,
card-family, datatype, inverse, nominal), 57 files, with 5303 added (58;
10019 and 12107 are in it). The run-8 timing order could not be used.

`ore-checked-blocking.tsv`: route, wall time before and after, exit codes,
SUB/UNSAT line count, whether the sorted SUB/UNSAT/CONSISTENT lines are
identical, and which arm answered (`ht-first`: the HT race worker, card arm
or native bridge, answered before CB; `ht+cb-race`: both ran; `-`: no HT
worker). Results: all 58 outputs identical; 9 time out on both binaries
(1066, 1194, 9540, 9791, 11553, 11695, 13229, 14817 and 9540 on
certified_card_nominals). One regression beyond 1.5x and 5 s: 7499
(`certified_card_proxy_abox`), 25.0 s to 97.5 s. Its card arm (mode 5)
ran 26,438 blocking passes before and 179,453 after (`KM_HT_STATS=1`); the
last pass blocked 238 of 276 blockable nodes before and 180 of 202 after,
so the checked pairs cost search (more passes over smaller models), not
model size. 10019 (0.16 to 0.12 s) and 12107 (0.06 to 0.05 s) are
unchanged.

5303 and the transitive-role note. On the automatic route 5303 answers
in 0.21 s on both binaries (HT worker first) with 238 subsumptions.
Forced `ht_general` at 5cc0bccf (plain subset blocking, before the fold
fix) and at c604f80d gives the same 238 SUB lines as the automatic answer,
so the "subset blocking drops 1 subsumption on 5303 with transitive roles"
note does not reproduce on this history; it is not shown to be the
subset-gain mechanism (inferred: it was the EMELIM fold loss that 554fc87
fixed for this ontology). At e8b63ea9 forced `ht_general` on 5303 times
out at 300 s (no answer).
