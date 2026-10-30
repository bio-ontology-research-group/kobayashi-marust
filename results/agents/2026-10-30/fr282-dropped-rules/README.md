# DL-safe rules beside a nominal: exact taxonomy instead of DROPPED (2026-10-30)

Branch `fix/v155-fr282-dropped-rules` off `development/v1.5.5` (87fda54f).
Commits b6f9547c, 34297b84, f0f485b1, e94e8e3f, 01bc0bea and the test
update (code, tests, docs), then this directory. Design and exactness argument: docs/DL-SAFE-RULES.md, section
"Rule-aware taxonomy beside a nominal (2026-10-30, v1.5.5)"; the
repeated-assertion count: docs/DATA-ASSERTION-PROFILES.md, "Repeated
assertions".

Binaries (all `km`):

| name | build | md5 |
|---|---|---|
| v1.5.4 | `.work/pgo-v154/km-pgo-use` (release PGO asset) | 0a88bb2a... |
| km-fix | 62e7a33d, `.work/agent-scratch/rules-worker-cost/km-fix` | 9666cafa... |
| km-base | 87fda54f, `cargo build --release` (default features) | ddef8408... |
| km-final | e94e8e3f, `cargo build --release --features mimalloc --bin km` | cd97e67b... |

`km-base` and `km-final` are in `.work/agent-scratch/fr282-dropped-rules/`.

## The defect (fr282)

`km-base` on `seeds/ofn/fr282.ofn` (automatic route): `CONSISTENT 1`,
`DROPPED 2`, no subsumption; HermiT (built-ins grounded by
`../rules-worker-cost/ground_builtins.py`) entails `A ⊑ D`. Route
`ht_rules` (`fr282-base-87fda54f.err.txt`). The message comes from the
`ht_rules` step of `orchestrate::classify_with_evidence_inner`: the rule
worker (`KM_RULES_CONSISTENCY`) only decided consistency; the CB engine
then classified the ontology without its rules, and because the source has
an object nominal (`object_nominal_concepts > 0`) the rules were counted in
`RULES_OUTSIDE_TAXONOMY` and published as dropped. Nothing about the rule
shape, the built-in, the data property or a cap is involved: any
consistent ontology with an executable DL-safe rule and a nominal took this
path.

Minimum (`probes/m3.ofn`, also the integration fixture): `A ⊑ {c, b}`,
`D(c)`, `t(b, b)`, domain of `t` is `∃s.{c}`, `v(c, 4)`, rule
`s(x, y) ∧ v(y, n) ∧ n ≥ 0 → D(x)`. The rule fires on `b` only through the
derived edge `s(b, c)`, so the ground-rule source route does not take it;
`A ⊑ D` needs `D(b)`. With the edge asserted (`m1`) or with an
object-only rule (`m4`, routed to the ground-rule source) v1.5.4 already
answered correctly.

DROPPED on the 400 seeds under v1.5.4 (`dropped-causes-v154.tsv`,
`causes.sh`): 119 answers. 118 carry the "not applied to a nominal
taxonomy" count; in 11 of them the worker input has no executable rule
(the frontend normalized the rules into ordinary clauses), where the count
was spurious. 15 also count one "uncarried" data-property assertion: a
repeated `DataPropertyAssertion` (fr216, fr217, fr290, ...), counted
against the occurrence count of the source; 1 has only that cause.

## Fix

1. The rule worker classifies its own input (`KM_RULES_CLASSIFY`,
   `tableau::rules_classification`, plain `Tableau::classify`) when a rule
   conclusion can reach a class query (object nominal or universal role)
   and the input has an executable rule; its taxonomy is the answer.
2. Schedule: that classification runs alone within 10 s
   (`KM_RULES_TAXONOMY_BUDGET_S`); past it, the CB taxonomy of the
   rule-free stream runs as before and the rule worker completes it with
   the CB entailments taken as given (`KM_RULES_CLASSIFY_KNOWN`). Same
   answer either way (test `cb_first_schedule_gives_the_same_answers`).
3. Refusal instead of DROPPED (exit 3) when the conversion omits a clause
   other than the proxy definitions `__nom__a(x) → x ≈ a`, fences a
   construct, the input is nominal + inverse + number (no NN-rule), or the
   stream is one-sorted.
4. Automatic `ht_rules` with such rules uses nominal clausification, so the
   stream is sorted (the v1.5.4 open item: binary object-atom rules beside a
   TBox nominal and a data property got no verdict).
5. A ground `DifferentIndividuals(a b)` is encoded as
   `__nom__a(x) ∧ __nom__b(x) → ⊥` in the rule worker; it used to be
   recorded and silently not encoded (probe `diff4`: v1.5.4-path answer
   `K ⊑ D`, HermiT `K` unsatisfiable).
6. No executable rule left: no rule count (the CB stream already contains
   the normalized rules).
7. Frontend: every converted `DataPropertyAssertion` occurrence counts as
   carried (repeated assertions are the same axiom).

## Differential: 400 `gen_finite_rules.py` seeds

`run_diff.sh` (this directory's `diff_run.py`, which now reports `DROPPED`
and `REFUSED`), route auto, 60 s cap, 3 threads, then `rerun_err.sh` (ERR
rows rerun with one thread; the machine was at its commit limit, load
85-110 on 56 cores, and the 4 GiB worker stacks made some spawns fail with
ERR in 0.03 s). Gold: `seeds-fr1-400.tar.gz` of `../rules-worker-cost`.

| binary | ok | WRONG | DROPPED | REFUSED | TIMEOUT | file |
|---|---:|---:|---:|---:|---:|---|
| v1.5.4 | 220 | 0 | 119 | 0 | 61 | `diff-v154.tsv` |
| km-final | 365 | 0 | 0 | 0 | 35 | `diff-final.tsv` |

Per seed: 116 DROPPED → ok, 3 DROPPED → TIMEOUT, 220 ok → ok, 29 TIMEOUT →
ok, 32 TIMEOUT → TIMEOUT; no ok answer was lost. The three new timeouts:
fr6 (v1.5.4: 35.9 s with DROPPED; now the completion step explodes in
phase 1 of `Tableau::classify`, finding a model of `{A}`, > 170 s), fr56
(the CB route, no executable rule; 65 s for v1.5.4 and 82 s here when run
alone under the same load), fr270 (v1.5.4 5.3 s with DROPPED; 44.5 s here
alone, 10 s budget + 15 s CB + 29 s completion). The earlier
`../rules-worker-cost` table showed 339 ok and 1 WRONG because its
`diff_run.py` counted DROPPED answers as ok.

## 2026-10-29 rule probes and nominal-data seeds

`run_1029.sh`: `top-nominal-data/rules` (15 probes, HermiT gold), and the
affected `fresh2` (57) and `fresh3` (28) seeds, route auto, 60 s.

| set | v1.5.4 | km-final |
|---|---|---|
| rules | 3 ok, 12 REFUSED | 7 ok, 8 REFUSED |
| fresh2 | 50 ok, 7 TIMEOUT | 50 ok, 7 TIMEOUT |
| fresh3 | 18 ok, 1 DROPPED, 9 TIMEOUT | 18 ok, 1 DROPPED, 9 TIMEOUT |

s7, s8, s9, s10 (binary rule beside `⊤ ⊑ {a}` and `⊤ ⊑ ≥2 u`) change from
refused to exact. The 8 still refused are k1-k5 (`HasKey`) and s3-s5
(rules with a data atom and no data assertion: "parsed 0 and certified 0 of
1"), outside this change. The fresh3 DROPPED (m7170, route
`certified_nominals`, no rule) is the same on both binaries.

## Timing (7278, 3726)

`timing/timing.sh`, one run each, core 44, `run1.sh` environment of
`../rules-worker-cost` (policy v153). Load average about 85 on 56 cores,
so absolute times are about twice those of `../rules-worker-cost/timing`
(load 13).

| input | v1.5.4 PGO | km-fix | km-final | output md5 (all equal) |
|---|---:|---:|---:|---|
| ore_ont_7278 | 56.54 | 19.47 | 17.69 | 1be6b3438106 |
| ore_ont_3726 | 57.25 | 13.90 | 10.75 | 1be6b3438106 |

Neither input takes the new step (no object nominal; route
`certified_el_production`); both still run the second frontend pass, as
with km-fix. No cost reintroduced.

## Tests (release, `--features mimalloc`, e94e8e3f unless noted)

Integration suites (`tests-integration.log`):
cb_route_completeness 8, constant_data_rule_normalization 2,
finite_rule_taxonomy 4, forced_route_fail_closed 5, ground_rule_source 4,
has_key_rules 6, integer_data_rule_normalization 2,
isolated_named_rule_normalization 1, rule_independent_abox_clash 2,
rules_route 5, source_incremental_rules 3, top_nominal_data_successors 16,
transitive_rule_reduction 1, unary_rule_normalization 9,
universal_role_and_top_data_range 13, nominal_ground_body 3, and the new
rule_taxonomy_nominal 8: all passed.

- data_assertions_carried: 8 passed, 1 failed:
  `unproxied_assertions_can_hide_a_clash` exceeds its 60 s bound on the
  forced `nominals` route (the known v1.5.4 open item). Same input alone:
  v1.5.4 65.8 s, km-final 80.0 s, both `CONSISTENT 0`; the other routes
  answer in 0.1 to 4.1 s on both. Not caused by this change.
- empty_and_universal_data_ranges: `excluded_middle_of_complement_ranges`
  failed once in the suite run (its 180 s per-case bound under load 100)
  and passed alone (255.7 s); the other 9 passed.
- finite_data_rule_normalization:
  `finite_rule_nominal_query_uses_inverse_chain_and_transitive_premises`
  failed on e94e8e3f: the input is now refused (inverse role chain and a
  number restriction beside a nominal, SHIQ for the rule worker); v1.5.4
  answered with `DROPPED 1`. The test was changed to accept an exact answer
  or that refusal (01bc0bea). On the final commit the suite passes 3/3:
  `finite_data_rule_entailments_reach_nominal_class_queries` pinned the
  v1.5.4 `dropped == 1` and now expects `dropped == 0` with exactly
  `C ⊑ Bad` (the answer KM now gives).

Final commit (km `88a05ced...`, the refusal message and tests changed
since e94e8e3f, no answer changed): finite_data_rule_normalization 3
passed, rule_taxonomy_nominal 8 passed, data_abox_projection 2,
source_axiom_drops 5, endpoint_transitivity 1 passed.

Library: `orchestrate::` 292 passed, 0 failed, 1 ignored; `frontend::` 398
passed (with the new `repeated_data_assertion_counts_every_source_occurrence`);
`tableau::` 237 passed, 20 failed, the same 20 as
`../rules-worker-cost/tests/lib-tableau-frontend-failed.txt` (they need the
`KM_HT_LEAN_*` checkers). A first suite run had a 21st failure,
`compact_bridge_entry_matches_the_legacy_json_worker` (environment-variable
test), which passed alone three times and in the rerun of `tableau::`.
Lean gates: not run.

## Probes (`probes/`, gold in `probes/gold/`)

`m3` (fr282 minimum), `m1` (asserted edge), `m4` (object-only rule),
`diff4` (distinctness), `z7` (declared class without axioms, from s7),
`u2` (universal role; ground-rule source route), `d3` (a
`DifferentIndividualsAtom` rule: refused).

## Reproduce

```
S=.work/agent-scratch/fr282-dropped-rules
./run_diff.sh $S/km-final diff-final.tsv && ./rerun_err.sh $S/km-final diff-final.tsv diff-final-merged.tsv
./run_1029.sh $S/km-final final
CPU=44 timing/timing.sh timing .work/pgo-v154/km-pgo-use .work/agent-scratch/rules-worker-cost/km-fix $S/km-final
```
