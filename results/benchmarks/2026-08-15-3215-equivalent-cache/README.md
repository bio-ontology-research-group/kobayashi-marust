# KPSet per-model reuse experiments

All candidates are based on v0.2.26 (`c1004a9`). They preserve the completion
search, classifier messages, message order, and saturation fixpoint.

## V1: equivalent non-candidate extraction

Commit `1f677f0`, binary SHA-256
`3f7e861859e011a2635129425051ce0ae807d41dada04a809384732cd1d28a94`,
extracts the model-node-dependent equivalent non-candidate set once per model
instead of once per named label. The three focused equivalent-candidate tests
passed.

IBEX job `50514669` ran ORE3215 in ABBA order on one Intel Xeon Gold 6248
allocation. All four arms used `production_all`, matched gold, and had the same
full-IRI signature.

| Metric | v0.2.26 | V1 |
|---|---:|---:|
| Mean wall (s) | 140.5712 | 140.1308 |
| Mean peak RSS (MiB) | 6321.75 | 6323.70 |

The 0.31% wall improvement is too small for a strict corpus sweep. V1 was not
released.

## V2: ordered possible-subsumer template

Commit `3c4ac97`, binary SHA-256
`2eaed700a25830404dcb25e02c1d2b1d41b66414cfa918b28dfba5a54f215423`,
additionally sorts and filters each model's root labels once. Per-message
construction clones that ordered template and applies exactly the original
testing-concept exclusion. The focused order and exclusion regression test
passed.

IBEX job `50515223` produced two exact-gold ORE3215 arms on the same Intel Xeon
Gold 6248 allocation:

| Metric | v0.2.26 | V2 | Change |
|---|---:|---:|---:|
| Wall (s) | 140.9742 | 139.8478 | -0.80% |
| Peak RSS (MiB) | 6328.71 | 6327.17 | -0.02% |

This remains too small relative to corpus scheduling variance and did not earn
a strict 592-ontology sweep. V2 was not released.

These results ruled out equivalent-candidate extraction and repeated root-label
sorting as dominant causes of ORE3215's model-analysis time and motivated finer
profiling of message construction.

## V3: cached root-label membership

Diagnostic job `50515271` measured 1,416,217 possible-subsumer message calls but
only 19,956 message-initialisation calls. The update path rebuilt an identical
root-label `HashSet` for each named label. Commit `ff9c458`, binary SHA-256
`eb2f4335500dd4c6621676f4c87636a30867fe0d5484a3b879841f423adc4c84`,
builds that set once per completed model and passes it read-only to every update
call. This changes representation reuse only; it does not change message
contents, ordering, completion rules, or the saturation fixpoint.

The focused regression test covers initial message ordering, testing-concept
exclusion, and cached update behavior. The complete release test suite passed,
including all 1,998 library tests and the issue #3 pigeonhole regression.

Two opposite-order IBEX pairs matched gold and selected `production_all`:

| Job/order | v0.2.26 wall (s) | V3 wall (s) | Wall change | v0.2.26 RSS (MiB) | V3 RSS (MiB) |
|---|---:|---:|---:|---:|---:|
| `50515347`, baseline then V3 | 140.8609 | 120.6064 | -14.38% | 6325.11 | 6331.21 |
| `50515379`, V3 then baseline | 140.5840 | 120.2536 | -14.46% | 6326.93 | 6331.64 |

The focused result is large and order-independent. Strict 592-ontology sweep
`50515439` ran under the standard 240-second and 20-GB limits on Intel Xeon
Gold 6248 CPUs. It contains 592 unique terminal rows, profiles, and checkpoints,
has no temporary files, and pins every row to the V3 binary hash. Field-by-field
comparison with v0.2.26 found zero differences in status, verdict, consistency,
selected route, or signature. Both sweeps report 591 successful classifications
and the same sole fail-closed error.

| Metric | v0.2.26 | V3 | Change | Improved? |
|---|---:|---:|---:|:---:|
| Mean wall (s) | 3.607746 | 3.589761 | -0.017984 | yes |
| Median wall (s) | 0.1839 | 0.1885 | +0.0046 | no |
| Mean peak RSS (MiB) | 436.3724 | 436.1394 | -0.2329 | yes |
| Median peak RSS (MiB) | 36.16 | 36.17 | +0.01 | no |

ORE3215 itself took 131.7421 seconds and 6,327.19 MiB in the strict sweep,
versus 155.5588 seconds and 6,328.99 MiB in v0.2.26. V3 therefore preserves a
useful tail optimization, but it does not pass the four-metric release gate by
itself. It was not released. The next candidate should retain V3 and improve
the median path before another strict sweep.

`audit_v3_sweep.py` encodes the integrity and comparison checks;
`audit-vs-v0.2.26.json` is its complete report. The focused V3 pair scripts and
the strict-sweep wrapper preserve the exact Slurm protocols used above.
