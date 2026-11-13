# v1.6.2 KM_FRONTEND_CHECK on the checkers-on suite (Ibex)

Ibex jobs 55512525 (build of km and `km-owl-reference` from
`development/v1.6.2` at c2fcc10d) and 55512526 (150 shards). Every input of
the 1,781-input checkers-on suite ran `km classify --lines` with
`KM_FRONTEND_CHECK=1` (`tools/run_frontend_check_suite.py` of
`results/agents/2026-11-12/v162-owl-binary/`), km budget 660 s (km 300 s plus
the check's 300 s), `KM_THREADS=1`. Rows: `results.tsv`.

| outcome | inputs |
|---|---:|
| agreed (EL reference) | 388 |
| agreed (ALC reference) | 2 |
| disagreed | **0** |
| declined: parse rejects a construct outside `F` | 1,270 |
| declined: in `F`, neither OWL EL nor OWL ALC (inverses, symmetry, role axioms with ALC constructors, ranges with EL) | 84 |
| declined: ALC signature budget (16 concept names) | 25 |
| declined: check budget | 1 |
| no check: km itself timed out or failed (all 11 fail the same way in the v1.6.1 Q2 run) | 11 |

So 390 suite answers of km are exact under the OWL 2 direct semantics of
their input text by `owlReference_sound` and the agreement check; no km
answer disagrees with the OWL reference. Checker wall time on the agreed
inputs: median 0.3 s, 95th percentile 68 s, maximum 223 s.

The 84 declines inside `F` are the fragment of `docs/V1.6.3-HT-PLAN.md`
(ALCHI, SHI, regular chains); the 25 budget declines are ALC ontologies
whose translation exceeds 16 concept names, the bound the v1.6.0 ALC stage
uses for type elimination.
