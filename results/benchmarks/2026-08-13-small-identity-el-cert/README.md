# ORE15803 certified-EL routing

Release v0.2.10 extends the existing `certified_el_production` source gate to a
large near-EL terminology with a tiny identity-only ABox. The certificate is
authoritative and any refusal or resource failure reruns `production_all`.

The complete profile audit admits exactly `ore_ont_15803.owl`. In same-node
panel job 50430173, forced `production_all` took 33.2433 seconds and 2,589.44
MiB while `elc_cert` took 24.3237 seconds and 1,316.07 MiB. Both produced the
same gold-matching signature
`b2a4da940996565b8ddac8c21ce38392192c271087965a80ba09c8826f2ee654`.

The source-bound candidate is commit `fd30da7`; its IBEX-native binary SHA-256
is `6a177d728714e6208148bebb735da9ea261fdc73fe5f54f63ad418b11cbe737f`.
Automatic verification job 50430743 selected `certified_el_production` and
matched gold in 24.8286 seconds at 1,354.35 MiB.

Strict full sweep 50430792 produced 592 results, profiles, and checkpoints and
no temporary files. It records 591 successes and the unchanged ORE1194 error.
Comparison with v0.2.9 finds exactly the intended ORE15803 route change and no
semantic or coverage regression. Aggregate metrics are 4.5884-second mean
wall, 0.2498-second median wall, 528.14-MiB mean peak RSS, and 41.98-MiB median
peak RSS. The wall movement relative to v0.2.9 is independent-scheduling noise;
the same-node panel above is the route-performance acceptance measurement.

Harnesses in this directory retain the source-bound build and automatic
verification contracts. The full sweep and its strict aggregate remain at
`ibex:/ibex/scratch/hohndor/km/candidate-fd30da7-identity-elcert-20260813`.
