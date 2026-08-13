# ORE6682 plain certified-EL production route

This experiment tests a composed automatic route for large near-EL
terminologies with a positive ABox and a small residual union set. The route
normalizes without polarity absorption and asks the EL canonical-model repair
certificate for a complete answer. If the certificate refuses or its worker
fails, KM reruns the established absorbed `production_all` route. The source
predicate is only a scheduling hint; the normalized certificate and exact
production fallback retain the semantic contract.

No consequence-based calculus rule changes. The implementation changes route
selection and orchestration only, so it does not require Lean re-certification.

## Candidate identity

- Starting release: `v0.2.7`, source `d725ad2`, binary
  `7e0e28e77a0c86d937f814198a0c85ad35ea086c91d5fefa70b5fd0c3dc775b7`.
- Candidate source archive:
  `8528081662d3dd2cc34df8d865b228c8c265c0ce8258ea9ca6aac6c0179bc9c6`.
- Candidate implementation commit: `087ae98`.
- IBEX-built candidate binary:
  `1abb488945d16df5ba16ee6aa261b1a2aac356b2bfe183b256856c7e28fe9734`.

## Same-node pair

IBEX job `50424991` ran both arms sequentially on the same exclusive Intel
Xeon Gold 6248 node under the 240-second and 20-GiB benchmark contract.

| arm | selected route | wall s | peak MiB | verdict |
|---|---|---:|---:|---|
| v0.2.7 baseline | `production_all` | 29.1361 | 7778.68 | match |
| candidate automatic | `certified_el_production` | 24.8344 | 5082.77 | match |

The candidate reduces wall time by 14.8% and peak memory by 34.7%. Both arms
produce signature
`0a7e90878ba8715efca484296498d433cf7ab87612dc369aacb545029d3e93e3`.
The harness requires terminal checkpoints, gold matches, an exact candidate
route trace, and equality across all semantic result fields before printing
`PAIR_COMPLETE`.

## Complete gate-membership audit

Candidate-profile array job `50425027` produced 30 result files and 30
checkpoints containing exactly 592 unique successful profiles. Exactly one
ontology selects the new route: `ore_ont_6682.owl`. The other 591 automatic
route selections remain outside this gate. See `profile-summary.json` and the
source-bound rows under `profile-all/`.

The structural-feature audit also contains exactly 592 unique successful rows
under `features-all/`. The final audit harness binds to the accepted v0.2.7
592-name list by SHA-256, validates each per-ontology JSON object, compacts it
to NDJSON, and publishes a chunk only after its expected row count is present.

## Complete automatic sweep

IBEX array job `50425474` produced exactly 592 result files, 592 terminal
checkpoints, and 592 profiles, with no temporary files left behind. The strict
aggregate binds every row to candidate binary
`1abb488945d16df5ba16ee6aa261b1a2aac356b2bfe183b256856c7e28fe9734`
and Intel Xeon Gold 6248 hardware. It reports 591 successful classifications
and ORE1194 as the sole fail-closed error.

The field-by-field comparison with v0.2.7 finds zero semantic regressions,
zero coverage regressions, and exactly one route transition: ORE6682 from
`production_all` to `certified_el_production`. The sweep reports mean wall
4.6525 seconds, median wall 0.2480 seconds, mean RSS 563.01 MiB, and median RSS
42.36 MiB. Mean RSS improves over v0.2.7; wall mean and both medians contain
small adverse run-to-run movement. The same-node pair above isolates the only
changed execution path and supplies the performance acceptance result.

## Files

- `baseline_production_candidate_pair.json` and `candidate_auto_pair.json`:
  accepted paired records.
- `production_all.json` and `elc_cert.json`: isolated-route diagnostic job
  `50422131` that motivated the composed route.
- `ibex_pair_auto_probe.sbatch`: strict same-node candidate verifier.
- `ibex_profile_all_candidate.sbatch`: complete source-profile membership
  audit.
- `ibex_features_all.sbatch`: complete structural-feature audit.
- `ibex_build_auto_probe.sbatch`: source-bound IBEX build.
- `ibex_sweep_087ae98.sbatch`: resumable strict 592-ontology sweep.
- `aggregate_strict.py` and `compare_v027.py`: integrity and no-regression
  verifiers.
- `full-sweep/`: compact automatic results, aggregate, and v0.2.7 comparison.
