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
