# ORE8737 EL completion profile

This capsule targets mean wall time after v0.2.11. ORE8737 is exact on the
automatic `certified_el_production` route in 100.1517 seconds, while frozen
Konclude takes 38.2881 seconds.

IBEX profile job `50435254` used the v0.2.11 binary SHA-256
`d19938110369da96167feddf2a257550bf80aca1793afd40154d18d303663f8e` on
an Intel Gold 6248 node. The streaming frontend took 25.64 seconds and peaked
at 3,864,448 KiB. The isolated EL worker took 56.64 seconds and peaked at
4,996,600 KiB. Its rule-volume counters were:

```text
sub_items=46950912 edge_items=23065620
nf1_scan=25610406 nf2_scan=0 nf3_scan=23065620
nf4_sub_scan=600584305 nf4_edge_scan=4061947248
nf7_scan=0 botback=0
```

The 4.06 billion NF4 edge-side conclusion checks dominate the remaining core
time. Measurement build job `50435346` produced binary
`a02338fa3784047f1ca22fd811d084d85c1e9e8ebfb5ddaebc4e405d251dcd92`.
Profile job `50435442` found 683,067 labels but only 281,969 distinct completed
label fingerprints. However, all 23,065,620 NF4 edges had a distinct exact
`(parent, role, target-label)` key. Cross-target label memoization therefore
cannot remove these joins and was rejected before implementation.

A second candidate used a generation-stamped dense membership cache for the
current edge parent. It preserved the existing worklist schedule and
authoritative hash sets, turning already-known NF4 conclusions into one array
read. IBEX build job `50435498` produced binary
`2ee369dac81dce0235d68f0dcb9c8c59ca3950032188f2a04d9b25b0e8dfe654`.
The same-node exact-gold panel, job `50435561`, measured:

| Arm | Verdict | Wall | Peak RSS |
|---|---:|---:|---:|
| v0.2.11 baseline | exact match | 92.7864 s | 4932.19 MiB |
| dense-marker candidate | exact match | 94.6215 s | 4920.93 MiB |

The candidate saved 11.26 MiB but regressed wall time by 1.8351 seconds
(1.98%). It was rejected and fully removed from production source. Together,
these experiments rule out completed-label memoization and a second dense
membership layer as useful ways to reduce ORE8737's NF4 cost. The next attempt
should reduce the 4.06 billion joins structurally, for example by changing the
propagation representation or batching intersections, rather than adding
another membership cache.
