# Rule-checker cost on ore_ont_7278 and ore_ont_3726 (2026-10-30)

Branch `fix/v155-rules-worker-cost` from c89e7c86 (v1.5.4 plus the
incremental subset-blocking fix). Commit 62e7a33d (`orchestrate/inert_sorts.rs`,
`orchestrate/mod.rs`, docs/NOMINALS-CB.md section 6, "Inert object sorts in
the rule checker"). Binaries: `km-v153-pgo`, `km-v154-pgo` (release PGO
assets, unchanged), `km-fix` (plain `cargo build --release --features
mimalloc --bin km` of 62e7a33d, md5 9666cafa...), `km-exp` (the same rule-checker
code before the final test and comment edits, plus two debug hooks removed
before the commit: a dump of both frontend
passes and stage timers inside the frontend; used for the profile and the
seed differential below).

## Cause

The data-property assertions are not the cost. Both v1.5.3 and v1.5.4 carry
the 81 assertions of 7278 into the rule-checker input: the rules compare data
values, and the finite-rule grounding (`data_rules::lower_finite_rules`) adds
every positive data assertion as `a : ∃p.{v}` itself. The two worker inputs
differ only in the sort encoding of docs/NOMINALS-CB.md section 6
(b574d11e and successors, new in v1.5.4), which applies because the
grounding sets `KM_NOMINALS`: `ofn [sorts] 489 clauses added or relativized`
in both frontend passes (`profile/v154-7278-ofn-timing.err.txt`). The
captured worker inputs (`profile/captab.sh`, `profile/cdiff.py`) differ by
340 concept sort clauses `C ∧ D → ⊥`, 56 role sort clauses, 66 range sort
clauses `R → D`, 16 data-role range clauses `p(x,y) → D(y)`, and 11
relativized facts `Q_0(x) → Q_k(x) ∨ D(x)` that replace `Q_0(x) → Q_k(x)`
(`Q_0` is the `⊤` definer, `Q_k` the definer of `∀p.DT` of a
`DataPropertyRange`). Nothing else differs, and the 3726 inputs show the
same pattern.

Mechanism (`KM_TAB_STATS=1`, `profile/tabstats-*.err.txt`): the clausal
`Tableau` branches on each of the 11 disjunctions at each of the 221 ABox
nodes (2,431 `branch` events, `body=1 head=2`), and every branch restarts
`horn_saturate` over the whole graph (2,433 saturations of 223 nodes and
10,736 clauses, against 2 on the v1.5.3 input). There is no backtracking
(`backtracks=0`): the first disjunct always succeeds, so the time is
2,431 full re-saturations of about 9 ms each. The node count (2,214 after
expansion) and the finite-model check (283 domain elements, 60 concrete
values) are the same for both inputs.

Worker alone on captured inputs (`profile/worker-experiments.tsv`, one
core, `km-v154-pgo tableau`):

| input | edit | clauses | s | verdict |
|---|---|---:|---:|---|
| v1.5.3 7278 | none | 10,254 | 4.32 | consistent |
| v1.5.4 7278 | none | 10,732 | 26.39 | consistent |
| v1.5.4 7278 | drop the 11 `D` disjuncts only | 10,732 | 2.06 | inconsistent |
| v1.5.4 7278 | drop every `D` clause | 10,254 | 4.41 | consistent |
| v1.5.4 7278 | drop the 340 concept sort clauses | 10,392 | 27.40 | consistent |
| v1.5.4 7278 | drop the 56 role sort clauses | 10,676 | 26.56 | consistent |
| v1.5.4 7278 | drop the 11 `D` disjuncts and the 11 `Q_k ∧ D → ⊥` | 10,721 | 4.26 | consistent |
| v1.5.4 3726 | none | 10,732 | 24.56 | consistent |
| v1.5.4 3726 | as the previous fix row | 10,721 | 4.04 | consistent |

The third row shows that the disjunct is not removable on its own: with
the sort clause kept, a data value gets `Q_k` and clashes.

## The second frontend pass (question 2)

Yes, the frontend runs twice (`KM_TIMING frontend: 81 data-property
assertion(s) not carried; re-running ...`), about 2.8 s per pass, nearly
all of it in the finite-rule grounding (stage timers: 2.79 s of 2.79 s
between the unary-rule lowering and the end of `lower_finite_rules`;
v1.5.3's single pass takes 2.85 s in all). The first pass counts only the
parse-time `DataHasValue` conversion as carrying assertions, so it reports
81 uncarried ones, although the grounding carries all of them. The dumped
clause files of both passes are identical (8,552 clauses in the same
order; `rules`, `rbox` and `data_roles` equal); only the `nominal_abox`
diagnostics differ (`81 data-property assertion axiom(s) are unsupported`
and `ClassAssertion mismatch (242+0/434)` against `(242+81/434)`;
`complete` is false in both for other reasons). On these inputs the second
pass is therefore not needed and costs about 2.5 s of the remaining gap
to v1.5.3.

In general it is needed: without the grounding, the first pass drops the
assertions. Skipping it exactly would need the frontend to count
grounding-carried assertions as converted, and a proof that the first pass
then produces the same output as the converted pass on every input. The
two passes see different ontologies between parsing and the grounding
(`abox_consistency::collect`, `data_abox`, the inert-role and
existential-witness ABox probes, the atomic ABox certificate all read the
ontology before `lower_finite_rules` adds the assertions, and the parse
conversion also feeds the literal cap and the literal-profile path). I did
not do that audit, so I did not change it.

## Remedy (question 3): release inert object sorts in the rule checker

Candidate (a), a cheaper equivalent clause set for this worker. Before
`cb_to_ht::convert`, `rules_consistency` runs
`inert_sorts::release_inert_object_sorts` on the frontend clauses. A
definer `Q` is released when it is internal (no IRI, not a query, not in a
rule, a cardinality or a definer record, not a `__` marker), has a sort
clause `Q ∧ D → ⊥`, and

- (B) every clause with `Q(t)` in its body has a guard of `t`, and
- (H) every clause with `Q(t)` in its head has `D(t)` in its head too, or a
  guard of `t`,

where a guard is a body atom that is false at every data element in every
model (an object-sorted concept with its sort clause, itself not released,
or a role atom whose position at `t` has a domain or range sort clause), or
`t` is an individual pinned outside `D` by a unit fact with such an atom.
Candidates that fail are removed until none fails. For a released `Q` the
pass drops the `D(t)` disjunct of the facts that carry `Q(t)` and the sort
clause `Q ∧ D → ⊥`; the guard sort clauses stay.

Exactness. A model of the sorted set becomes a model of the result by
adding `Q` to every element of `D` (by (B) no clause reading `Q` fires at a
data element), and a model of the result becomes a model of the sorted set
by removing `Q` from every element of `D` (by (H) every unrelativized
derivation of `Q` is guarded, and the relativized facts hold through
`D`). The two clause sets have the same models up to internal definers on
data elements, so they are equisatisfiable, and consistency is all the
worker reports (`{"consistent": ...}`). Given a sound worker, the change
cannot flip a verdict; it can only change whether the worker finishes. On
the `require_source_model` path the worker also checks its model against
the original source theory; a released definer is not in that theory, so
the check reads the same source symbols (argued, and exercised by the 191
released seeds below, not proved). No admission decision changes: the frontend output, the meta,
the route and every other consumer of the clause stream are untouched,
and nothing is dropped. `KM_RULES_KEEP_INERT_SORTS=1` turns the pass off.

On 7278 and 3726 the pass releases all 11 range definers (`KM_TIMING
rules-consistency released 11 inert object sort(s): 11 fact(s)
unrelativized, 11 sort clause(s) removed`) and the worker takes 4.2 to
4.6 s inside the classification (`profile/exp-*-classify.err.txt`).

Candidate (b), omitting the carried assertions, does not apply: the
assertions cost nothing (the "drop every `D` clause" row keeps all of
them and runs in 4.4 s), and they are what the rules read.

## Validation (question 4)

Classification outputs: 7278 and 3726 with `km-fix` are byte-identical to
`km-v154-pgo` and `km-v153-pgo` (md5 `1be6b343...` for both inputs, both
policies; the two inputs differ only in IRIs the output does not contain).
All 7 timing inputs give the same md5 across the three binaries and both
policies (`timing/table.tsv`).

Tests (`tests/`, `cargo test --release --features mimalloc`, final
source):

- integration, all passed: cb_route_completeness 8, constant_data_rule_normalization 2,
  data_assertions_carried 9, empty_and_universal_data_ranges 10,
  finite_data_rule_normalization 3, finite_rule_taxonomy 4,
  forced_route_fail_closed 5, ground_rule_source 4, has_key_rules 6,
  integer_data_rule_normalization 2, isolated_named_rule_normalization 1,
  rule_independent_abox_clash 2, rules_route 5, source_incremental_rules 3,
  top_nominal_data_successors 16, transitive_rule_reduction 1,
  unary_rule_normalization 9, universal_role_and_top_data_range 13
  (`tests-rel-1.log`). A first attempt in the debug profile timed out two
  data_assertions_carried cases at their 60 s bound on route `nominals`
  (not the rule checker); in release they pass (58.6 s for the suite).
- `--lib orchestrate::inert_sorts`: 9 passed, among them the randomized
  check: on 3,000 generated sorted clause sets the release applies on
  2,358 (924 of them satisfiable) and never changes satisfiability (ground
  DPLL), while releasing without (B) and (H) changes it on 521
  (`tests-rel-2.log`); and `unchecked_release_turns_a_consistent_input_inconsistent`.
- `--lib -- tableau:: frontend::`: 634 passed, 20 failed; the 20 names
  (`lib-tableau-frontend-failed.txt`) are exactly the 20 of
  results/agents/2026-10-30/subset-blocking-cost/lib-failed-now.txt (they
  need the `KM_HT_LEAN_*` checkers).
- `--lib -- orchestrate::`: 292 passed, 0 failed, 1 ignored
  (`abox_quotient_survey`). The two pre-existing `orchestrate::` failures
  mentioned in the task did not fail in this run.
- Lean gates: not run.

Seed differential (`differential/`). The 2026-10-29 rule probes
(`top-nominal-data/rules`, 15 files) and the `gen_nomdata.py` seeds do not
reach the release (without the finite-rule grounding the rule checker
sees no sort encoding; a scan of 156 `gen_nomdata.py` seeds with
`DataPropertyRange` axioms and binary rules added, a generator I did not
keep, found 63 checker runs and 0 releases). So I wrote `gen_finite_rules.py`: the 7278
shape (full IRIs, an object TBox with nominals, object and integer data
assertions, `DataPropertyRange`/`Domain`/`Functional`, binary DL-safe
rules with `swrlb` comparisons). HermiT has no built-ins, so its gold
comes from `ground_builtins.py`, which replaces each comparison by the
asserted literals that satisfy it (the grounding KM certifies). 400 seeds
(fr1 to fr400), gold 198 consistent and 202 inconsistent. `scan-fix.tsv`
(`km-fix`, KM_TIMING): the rule checker runs on 244 seeds and the release
applies on 191.

`diff_run.py`, route auto, 60 s cap:

| binary | threads | ok | WRONG | TIMEOUT | file |
|---|---:|---:|---:|---:|---|
| km-exp (release on) | 3 | 339 | 1 | 60 | `diff-exp.tsv` |
| km-exp, `KM_RULES_KEEP_INERT_SORTS=1` | 3 | 339 | 1 | 60 | `diff-exp-keep.tsv` |
| km-v154-pgo | 3 | 339 | 1 | 60 | `diff-v154.tsv` |
| km-fix (62e7a33d) | 4 | 340 | 1 | 59 | `diff-fix.tsv` |

Per seed the first three are identical on all 400. km-fix differs on one
seed, fr225, which it answers correctly in 50.5 s where the other runs hit
the 60 s cap (a later run with 4 threads); everything else is identical. The WRONG row is fr282 on every binary: KM answers `CONSISTENT 1` with `DROPPED 2`
("2 rule(s) not applied to a nominal taxonomy") and misses `A ⊑ D`; the
answer is flagged as incomplete, `diff_run.py` does not read `DROPPED`, and
the release does not change it (same output md5 with and without the
pass, and on `km-base`, the c89e7c86 build). On the 148 released seeds
answered with and without the pass, the summed wall time is 164.7 s
against 203.0 s (km-v154-pgo 191.6 s), from the three 3-thread runs.

## Timing (question 5)

`timing/timing.sh` (one run at a time, one core, `run1.sh` environment,
`KM_ROUTE=auto`), wall seconds; the v1.5.3 binary does not read
`KM_ROUTING_POLICY` (the string is absent from it) and runs its own routing
under both settings. Load average during the runs
was about 13 on 56 cores from other users.

| input | policy | v1.5.3 PGO | v1.5.4 PGO | fix release | fix / v1.5.4 | output md5 (all equal) |
|---|---|---:|---:|---:|---:|---|
| ore_ont_7278 | v153 | 6.83 | 31.16 | 9.30 | 0.30 | 1be6b3438106 |
| ore_ont_7278 | general | 6.93 | 31.48 | 9.42 | 0.30 | 1be6b3438106 |
| ore_ont_3726 | v153 | 6.85 | 31.23 | 9.29 | 0.30 | 1be6b3438106 |
| ore_ont_3726 | general | 6.97 | 31.56 | 9.46 | 0.30 | 1be6b3438106 |
| ore_ont_7499 | v153 | 43.36 | 157.89 | 57.12 | 0.36 | 5ecdc990f3a3 |
| ore_ont_7499 | general | 43.51 | 159.46 | 57.07 | 0.36 | 5ecdc990f3a3 |
| ore_ont_205 | v153 | 47.78 | 179.06 | 65.50 | 0.37 | c0f5efa623a3 |
| ore_ont_205 | general | 48.22 | 180.64 | 65.68 | 0.36 | c0f5efa623a3 |
| ore_ont_10019 | v153 | 0.05 | 0.04 | 0.04 | 1.00 | 9b2a959e31b5 |
| ore_ont_10019 | general | 0.05 | 0.05 | 0.05 | 1.00 | 9b2a959e31b5 |
| ore_ont_12107 | v153 | 0.04 | 0.03 | 0.04 | 1.33 | de759cdf4f30 |
| ore_ont_12107 | general | 0.04 | 0.03 | 0.04 | 1.33 | de759cdf4f30 |
| ore_ont_5303 | v153 | 0.12 | 0.11 | 0.13 | 1.18 | ea58d38505e3 |
| ore_ont_5303 | general | 0.13 | 0.11 | 0.13 | 1.18 | ea58d38505e3 |

On 7499 and 205 the gain comes from the incremental subset-blocking fix
already in the base commit c89e7c86 (results/agents/2026-10-30/subset-blocking-cost);
the release pass does not apply there (no rule checker run). The three
small inputs are within timer resolution.

`km-fix` is a plain release build; the v1.5.3 and v1.5.4 binaries are PGO
builds (on 205 and 7499, PGO/release was 0.89 and 0.92 for v1.5.4 in
results/agents/2026-10-30/subset-blocking-cost). The remaining 2.5 s gap
on 7278 and 3726 is the second frontend pass.

## Not done

- Skipping the second frontend pass (see above).
- A PGO build of the fix.
- The worker still re-saturates the whole graph after every branch; a
  disjunction whose other disjunct a unit sort clause refutes could be
  decided without branching inside the `Tableau`. That would help other
  inputs with relativized facts on non-inert definers, but it is a worker
  change with its own backjumping obligations, and I did not attempt it.
