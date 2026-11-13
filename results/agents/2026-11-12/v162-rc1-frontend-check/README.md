# v1.6.2-rc1: KM_FRONTEND_CHECK on the checkers-on suite (Ibex)

Ibex jobs 55535767 (build of km and `km-owl-reference` from `v1.6.2-rc1`,
f3af7658) and 55535768 (150 shards), same runner, shards and budgets as
`../v162-frontend-check-suite/` (km 300 s plus the check's 300 s,
`KM_THREADS=1`). Binaries: km d842ea24, km-owl-reference 250e3781.
Rows: `results.tsv`.

| outcome | inputs |
|---|---:|
| agreed (EL reference) | 389 |
| agreed (ALC reference) | 2 |
| disagreed | **0** |
| declined: parse rejects a construct outside `F` | 1,270 |
| declined: in `F`, neither OWL EL nor OWL ALC | 84 |
| declined: ALC signature budget (16 concept names) | 25 |
| no check: km itself timed out or failed | 11 |

The 84 in-`F` declines name their first non-EL, non-ALC axiom:
SymmetricObjectProperty 26, EquivalentClasses 20, SubClassOf 19,
InverseObjectProperties 9, ObjectPropertyRange 8, DisjointClasses 2
(the last three kinds carry inverses or role axioms with ALC
constructors). They are the fragment of `docs/V1.6.3-HT-PLAN.md`.

Against the run at c2fcc10d (before the Rust IRI-identity change), every
input has the same km status and check outcome except ore_ont_8864, whose
check finished in 154 s (earlier over the 300 s budget) and agrees. So
the parser change moved no suite answer and no check outcome.
