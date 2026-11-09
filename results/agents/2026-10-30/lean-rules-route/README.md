# Lean certificates for the rule route (2026-10-30)

Branch `fix/v155-lean-rules-route` (worktree `.work/worktrees/checkers-on`),
off `development/v1.5.5`, merged with it at 69d2c117, e62a4bce and after the
fr282 merge (rule-aware taxonomy). Design, proved statements and the
frontend assumptions: docs/DL-SAFE-RULES.md, "Lean coverage (2026-10-30,
v1.5.5)"; summary in docs/CERTIFICATION-ROADMAP.md.

## What was measured

1. The gate `lean/run-rules-certification-gate.sh` end to end
   (`gate-run.txt`: theorem axiom audit, fixtures, test results).
2. The 400 `gen_finite_rules.py` seeds of `../rules-worker-cost`
   (`seeds-fr1-400.tar.gz`, gold: HermiT with grounded built-ins), route
   auto, 3 threads, 60 s cap, with `KM_RULES_LEAN_CERT` and
   `KM_RULES_LEAN_CHECKER` on every run (`diff_run_cert.py`, the
   fr282-dropped-rules `diff_run.py` plus a certificate column).
3. Cost of emission and checking on ore_ont_7278.

## Binaries

| name | commit | md5 |
|---|---|---|
| km-1a6643af | 1a6643af (before the fr282 merge) | efc4d474707d47ca8f70b2248f090acc |
| km-f9d32f54 | f9d32f54 (after the fr282 merge) | 8e717f312d007ec6cc5e1ba895cba7e0 |
| rules-cert-check | ab8e7e13 Lean sources (unchanged since) | 1ea9aff460f8ec5baffdcb8d033db743 |

All in `.work/agent-scratch/lean-rules-route/bin/` (`cargo build --release`,
default features). The timing of 7278 used the a3831253 build
(`engine/target/release/km`, faster Rust model pre-check).

## Differential (`diff-f9d32f54.tsv`, `diff-1a6643af.tsv`)

Columns 1 to 10 as in `diff_run.py`; 11 `cert`, 12 number of certificate
files, 13 the worker's certificate message if any. `cert`: `accepted`
(the worker's checker accepted every certificate and a second run of the
checker here accepts each file), `rejected`, `nocert` (an answer without a
certificate), `none` (no rule-worker answer was used), `timeout`.

| binary | ok | WRONG | DROPPED | TIMEOUT | accepted | rejected | nocert | none |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| km-f9d32f54 | 366 | 0 | 0 | 34 | 232 | 0 | 0 | 134 |
| km-1a6643af | 220 | 0 | 117 | 63 | 203 | 0 | 0 | 134 |

km-f9d32f54 wrote 235 certificate files (152 MB) for the 232 accepted
runs. No rejection, so nothing to minimise. Per seed against fr282's own
run of the same seeds without the checker (`diff-final-merged.tsv`, 365
ok, 35 TIMEOUT): fr270 and fr56 TIMEOUT → ok, fr248 ok → TIMEOUT. fr248
times out at 150 s also without certificates on this build (its rule
worker takes 0.01 s; the time goes elsewhere in the pipeline), and so does
fr136, one of the two seeds km-1a6643af lost against v1.5.4 (fr188, the
other, was not rerun): not a certificate cost.

The 134 `none` answers are all `CONSISTENT 0` on route `ht_rules`, decided
before the rule worker by the positive EL ABox check
(`elcomplete::positive_abox_classify_compact`, `orchestrate/mod.rs` just
before the `ht_rules` step). They are outside this certificate.

## ore_ont_7278 (`timing/ore7278-a3831253.txt`)

Three interleaved runs each, load average about 80 on 56 cores, so
absolute times are high. Same output in every pair.

| run | km plain (s) | km certified (s) | worker plain | worker certified | model | write | Lean check |
|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | 15.11 | 21.62 | 8.16 | 15.34 | 0.18 | 0.04 | 5.73 |
| 2 | 14.66 | 19.34 | 8.48 | 13.39 | 0.29 | 0.06 | 4.67 |
| 3 | 17.30 | 21.62 | 10.22 | 14.28 | 0.17 | 0.04 | 4.15 |

The certificate is one model (283 elements, 10,725 clauses, 222
nominals, 6.2 MB). The Lean check took 2.2 s at lower load (10.8 s before
the join-order change, 7.0 s with the extension index only). Recording
the search, building the model and writing the file cost under 1.5 s
together; the rest of the difference is the check and load noise.

## Reproduce

```
S=.work/agent-scratch/lean-rules-route
F=.work/agent-scratch/fr282-dropped-rules
DIFF_THREADS=3 DIFF_KM_TIMEOUT=60 DIFF_RULES_CHECKER=$S/bin/rules-cert-check-f9d32f54 \
  DIFF_CERT_ROOT=$S/diff2/certs python3 -I diff_run_cert.py $S/bin/km-f9d32f54 \
  .work/agent-assets/2026-10-28-scratch/oracle $F/seeds/gold out.tsv auto $(ls $F/seeds/ofn/*.ofn | sort -V)
KM_CERT_KEEP_NATIVE_CHECKERS=1 lean/run-rules-certification-gate.sh
KM_TIMING=1 KM_RULES_LEAN_CERT=dir KM_RULES_LEAN_CHECKER=lean/.lake/build/bin/rules-cert-check \
  km classify --lines ore_ont_7278.owl   # dir/*.timing holds the cost split
```
