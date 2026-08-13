# ORE3215 mean-wall investigation

This capsule records the v0.2.11 investigation of ORE3215, the slowest KM
automatic-route result. All accepted timings below used Intel Gold 6248 nodes,
240 seconds, 20 GiB, the v0.2.11 binary SHA-256
`d19938110369da96167feddf2a257550bf80aca1793afd40154d18d303663f8e`,
and exact comparison with the frozen Konclude full-IRI signature.

The route panel, Slurm job `50434609`, established:

| Route | Result | Wall | Peak RSS |
|---|---:|---:|---:|
| `ht_bridge` | exact match | 157.7465 s | 6424.92 MiB |
| `ht_full` | exact match | 158.9038 s | 6428.42 MiB |
| `elc_cert` | unsupported | 35.9418 s | not retained |

The certified-EL trace, job `50434817`, explains the refusal. EL saturation
processes 23,982,112 subsumption items and 3,989,180 edge items, including
2,281,608,485 NF2 candidate checks. Both repair policies build complete models,
but 18,322 named subjects remain unresolved, above the exact residue cap.

A source-bound candidate moved the existing sound common-disjunct hoist before
the certificate comparison. IBEX build job `50435023` produced binary
`0ee18af6c14403c594d7bb1726e6d3f31bdc953d04acebdb7331d924fabc0aa5`.
Exact test job `50435070` still returned unsupported in 36.0393 seconds. The
trace showed 1,754,178 hoisted pairs, followed by the same 18,322 unresolved
subjects and more repair work. The hypothesis was rejected and the source
change was reverted. No production behavior changed.

The remaining exact path is the Konclude bridge. Its dominant work is 18,323
synchronous satisfiability jobs, so future work should target exact completion
environment reuse or repeated-module classification rather than EL routing.
