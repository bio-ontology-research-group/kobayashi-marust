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
