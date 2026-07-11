# Remaining-five Konclude diagnosis (2026-07-10)

Target ontologies: `3215`, `7914`, `9663`, `9724`, `14817`.

No KM implementation was changed. Full-ontology experiments ran as Slurm jobs
on IBEX with 40 GB allocations. Small checks ran on `ws`.

## Konclude ablations

Official Konclude v0.7.0-1138, one worker. Times include parse, preprocess,
precompute, classification, and output. RSS is the process maximum.

| ontology | default wall / RSS | no saturation-subsumer extraction | no saturation successor extension |
|---|---:|---:|---:|
| 3215 | 111.6 s / 11.8 GB | 188.3 s / 12.9 GB | 86.8 s / 10.5 GB |
| 7914 | 3.0 s / 1.36 GB | 6.0 s / 1.96 GB | 10.2 s / 1.51 GB |
| 9663 | 10.0 s / 4.25 GB | 19.1 s / 5.94 GB | 36.2 s / 4.28 GB |
| 9724 | 5.8 s / 3.03 GB | 12.2 s / 3.75 GB | 90.9 s / 12.0 GB |
| 14817 | 22.0 s / 3.29 GB | 23.1 s / 4.75 GB | 21.4 s / 2.12 GB |

Konclude's default precompute/classification split was:

| ontology | precompute | classification |
|---|---:|---:|
| 3215 | 26.5 s | 81.9 s |
| 7914 | 1.30 s | 0.35 s |
| 9663 | 5.96 s | 1.82 s |
| 9724 | 4.80 s | 0.15 s |
| 14817 | 2.41 s | 17.63 s |

Disabling satisfiable-test subsumption extraction was neutral on the two
classification-heavy cases: `3215` took 103.4 s total and `14817` took 20.4 s.
The important mechanism is therefore the shared precomputed model, KPSet
candidate initialization/pruning, fast satisfiability prechecks, and the
completion caches, not that one extraction toggle.

## KM observations

The new `KM_TRIGGER_ABSORB=1` route timed out on all five after 300 s:

| ontology | observed stage at timeout | peak RSS |
|---|---|---:|
| 3215 | saturation did not finish | 12.6 GB |
| 7914 | saturation answered 10,910/17,680; 6,770 residue subjects, five hard deferrals | 37.8 GB |
| 9663 | saturation did not finish | 37.9 GB |
| 9724 | saturation budget overrun; first residue subject then expanded millions of labels | 18.3 GB |
| 14817 | saturation answered 46,930/58,364; only 1,537/11,434 residue subjects processed | 1.43 GB |

The source terminology itself is not the remaining `3215`/`14817` problem.
The trigger route absorbed all 36,646 eligible equivalence definitions in
`3215`; for `14817` it encoded 155,575 direct axioms plus 4,295 absorbed GCIs
with zero unsupported source axioms.

Turning on KM's successor extension, with or without saturation-cache coupling,
did not complete saturation on any of the five in 300 s. `7914` and `9663`
reached about 38 GB. Konclude's opposite result on the same ablation shows that
KM has the extension substrate but not the production algorithm.

Small checks:

- Konclude classifies `tests/completeness-gaps/mini7914_unsat.ofn` correctly in
  0.05 s (`X` equivalent to bottom). Current KM and trigger KM both return an
  empty unsatisfiable set. This is a correctness gap in inverse/transitive
  propagation, not only a timeout.
- KM's isolated `e2e_part_of_shape_14817` role-automaton test passes.
- KM's isolated `satcache_expansion_and_blocking_fire_in_probe` test passes.

The last two checks locate the gap at production construction/coupling: the
role-automaton preprocessor is only called by tests, the KPSet classifier port
is not the production classifier, and completion's
`get_saturation_resolved_individual_node_extension` remains a pending body.

## Required work

1. Wire Konclude's real precompute-to-KPSet classification pipeline: initialize
   testing order and possible-subsumption maps from saturation, run fast
   satisfiability/pseudo-model prechecks, dispatch only unresolved tests, and
   consume classification messages for pruning and taxonomy construction.
2. Finish successor-extension and saturation-cache coupling, especially
   deterministic restriction collection, resolved-extension lookup, and
   saturation-derived successor blocking. Replace unordered extension work maps
   where Konclude relies on ordered process maps.
3. Run `RoleChainAutomataTransformationPreProcess` in production after building
   the source TBox/RBox arenas, then complete the inverse/transitive edge
   reapplication path. This is mandatory for `7914` correctness and the known
   `14817` transitive `part_of` tail.
4. Port saturation disjunct common-concept extraction and its update queue.
   This is the main missing disjunction-specific saturation operation for
   `3215`, where successor extension is empirically not load-bearing.

Per ontology: `3215` needs items 1 and 4; `7914` needs items 1-3; `9663` and
`9724` need items 1-2; `14817` needs items 1 and 3.
