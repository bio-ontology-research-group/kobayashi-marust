# Compact exact-nominal worker scheduling

Seven small nominal/ABox residuals had historical bare-CB routes that beat
their external targets. A 70-run reproduction panel and a 140-run common-route
matrix confirmed those measurements, but bare `cb_plain1` does not enable KM's
singleton-aware nominal encoding. Gold agreement on these inputs cannot turn
that proxy route into a complete nominal procedure, so automatic routing does
not use those results.

The sound alternative is to retain the exact `nominals` route and vary only its
worker count. A 35-run one-worker panel found four strict wins: ORE 13035,
13132, 2678, and 2744. ORE 2860, 5564, and 9557 did not meet their wall targets
under the exact route; a further 45-run 2/4/8-worker panel did not recover them,
so they remain residuals.

The automatic scheduling gate uses only source-profile bounds: 50,000--170,000
bytes, 300--900 logical axioms, 100--320 ABox axioms, concept depth 2--3, and
35--300 classes, with no imports or rules. It applies only after semantic
routing has selected the exact `nominals` route. A release test projected the
gate over all 592 retained source profiles and admitted exactly the four
measured inputs. The gate contains no ontology identity.

Commit `b8123bc` retains `KM_NOMINALS=1` and changes only `KM_THREADS` from 16
to 1 for this envelope. Focused release tests passed, including the 592-profile
projection. IBEX build job `51257488` built source archive SHA-256
`112fcec92ef0041e1c870f36deed285fde789686bf2dd019e9fdccb943c4d0e7`.
The deployed binary has SHA-256
`baf1c645e02708692f2c0ada71ea62500cf4e0119d3bb5caedfe4f44233f4f3a`.

Automatic-only array `51257573` produced exactly 40 results, 40 checkpoints,
40 completion markers, and no failure artifacts. All ten repetitions per
ontology returned `status=ok`, selected `nominals`, and matched the retained
Konclude gold result.

| ontology | median wall (s) | wall target (s) | median peak RSS (MiB) | RSS target (MiB) | signature SHA-256 |
|---:|---:|---:|---:|---:|---|
| 13035 | **0.0782** | 0.1500 | **19.22** | 32.23 | `26f70e0e...55b1c` |
| 13132 | **0.0772** | 0.1055 | **9.69** | 30.20 | `e13d65db...c0f72` |
| 2678 | **0.0771** | 0.0855 | **18.44** | 31.14 | `4d94e1f7...c788` |
| 2744 | **0.0776** | 0.1382 | **19.38** | 32.29 | `cc1a1bfc...b44bd` |

These four recoveries raise the evidence-composite strict score from 517/589
to **521/589** and reduce the residual set from 72 to 68.

This is a scheduling-only change. The exact nominal clauses and calculus, rule
ordering, and derived fixpoint are unchanged, so Lean re-certification is not
due. The production source, build record, results, and logs are archived under
`.work/artifacts/v14-compact-nominal1-production/`; its verified `SHA256SUMS`
manifest covers 125 files. The exploratory route matrices are under
`.work/artifacts/v14-small-nominal-cb-panel/`, with a verified 905-file
manifest.
