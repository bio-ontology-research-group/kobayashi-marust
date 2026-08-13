# Large no-cardinality ABox routing candidate

ORE15846 is a 256,427-axiom ABox with no source cardinality or datatype
constructor. The automatic router selected `certified_nominals`, even though
the existing large-no-cardinality predicate selected the complete production
portfolio only a few match arms later. The broader large-nominal arm therefore
shadowed the intended scheduling rule.

IBEX Gold-6248 pair job `50091851` ran both routes with candidate `2a32741`,
binary SHA-256
`d8fd398d79e044e1daada75dff9812960de72bf2dca94399bf4836a1c0bab7b6`,
under the 240-second and 20-GiB classification limits:

| Route | Status | Gold verdict | Wall time | Peak RSS |
|---|---|---|---:|---:|
| Automatic (`certified_nominals`) | ok | match | 175.6823 s | 19,056.18 MiB |
| Forced `production_all` | ok | match | 10.1760 s | 1,334.98 MiB |

Both routes produced the same collision-sensitive full-IRI signature
`ac1340ed5caad4831da799f8842d2893e8d9f310dce3d084390affed2072a4a6`,
10,640 subsumptions, no unsatisfiable classes, and a consistent ontology.
`auto.json` and `production_all.json` retain the complete source-bound rows.

The candidate routing change moves the existing
`large_no_cardinality_abox_production_candidate` arm before the broader
`large_nominal_portfolio_candidate` arm. It changes scheduling only:
`production_all` retains the same exact nominal-aware fallback and every
specialist arm remains complete-answer-or-defer. Evaluation of all 592 current
profiles shows that this precedence correction changes only ORE15846.

The source change still requires a fresh build, complete release suite, route
profile audit, and strict 592-ontology sweep before release.

The complete locked release suite at `d725ad2` passes with 1,959 tests passed,
eight intentionally ignored, and no failures; the issue #3 pigeonhole
integration test passes explicitly. A workstation-built binary was rejected by
the first profile array before producing any profile because its glibc 2.39
requirement is incompatible with IBEX. Those 40 terminal startup failures are
preserved under the remote candidate root and are excluded from all evidence.
IBEX-native source-archive build job `50093112` produced the accepted binary,
SHA-256
`7e0e28e77a0c86d937f814198a0c85ad35ea086c91d5fefa70b5fd0c3dc775b7`.
Profile job `50093390` produced 592 validated profile/checkpoint pairs with no
accepted temporary files. Comparison with `2a32741` found ORE15846 as the only
route change and no other profile-field difference.

The first completed sweep ending in job `50095117` passed the semantic and
coverage checks, but mixed rows from earlier resumable attempts. Its accepted
result directory is retained remotely as `results-50095117` and is not the
release measurement.

Clean full sweep `50421935` started with an empty result directory and produced
592 result/checkpoint pairs with no temporary files. Strict aggregation reports
591 `ok` rows, ORE1194 as the sole fail-closed error, exactly 99 expected route
changes from v0.2.6, and zero coverage or semantic regressions. The accepted
automatic-result SHA-256 is
`165ee79ed05626936cec4e90b56051ef553d6fb526b5d97630b58eea6a81551a`.

| Metric | v0.2.6 | Candidate |
|---|---:|---:|
| Mean wall time | 5.1787 s | 4.5777 s |
| Median wall time | 0.2467 s | 0.2475 s |
| Mean peak RSS | 720.08 MiB | 567.35 MiB |
| Median peak RSS | 42.02 MiB | 42.20 MiB |

The candidate improves mean wall time by 11.6% and mean peak RSS by 21.2%.
The median movements are below measurement resolution and both candidate
medians remain below the frozen Konclude values. The same-node paired panels
for the 98 ELC route changes improve all four panel metrics. The ORE15846 pair
is exact and improves wall from 175.6823 to 10.1760 seconds and peak RSS from
19,056.18 to 1,334.98 MiB.
