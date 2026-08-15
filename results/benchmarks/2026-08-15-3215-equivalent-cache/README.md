# KPSet per-model reuse experiments

Both candidates are based on v0.2.26 (`c1004a9`). They preserve the completion
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

The result rules out equivalent-candidate extraction and repeated root-label
sorting as dominant causes of ORE3215's model-analysis time. The next target is
the serial execution of 18,323 independent satisfiability models or a larger
measured subphase inside their message construction.
