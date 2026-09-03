# 2026-09-03 bounded near-EL certified routing

## What this panel scores

The current strict external audit
(`.work/artifacts/v14-1194-default/full-sweep-strict-audit.json`, IBEX array
`51242642`, produced by `.work/strict_external_audit.py`) reports 489 of 592
ontologies strictly below both per-ontology external targets, 100 failures, and
3 unadjudicated ontologies (10860, 1194, 4669). The per-ontology targets are
`results/benchmarks/2026-08-25-v1.0.0-baseline/external-per-ontology-targets.tsv`,
the exclusive best wall and best peak over the correct external arms.

Cross-referencing those 100 failures against every KM procedure row in
`results/benchmarks/2026-07-27-solving-routes-full-sweep/full-results.jsonl.gz`
gives **37 failures for which some existing KM arm was recorded
sound-and-complete and strictly below both targets** in that sweep. The
selection keeps only rows with `status=ok`, `sound=yes`, `complete=yes` and a
matching signature verdict, and it does not change when arms using
`KM_HT_FORCE` or arms identical to the current route are excluded.
`strict-failures-with-a-winning-route.tsv` is that ledger, with the current
route, the current wall and peak, both targets, and the best qualifying arm.

Note on measurement basis: the 2026-07-27 sweep binary is slower than the
current candidate. Over the 460 ontologies where the sweep contains the same
route the current audit selected, the sweep/current wall ratio has median 1.48
and the peak ratio 1.13. Sweep numbers are therefore a conservative stand-in
for what the current binary would record on the same route, which is what makes
"this arm already beats both targets" a safe claim and the projection below a
pessimistic one.

## What changed

`engine/src/routing.rs` gains one source-only screen,
`bounded_near_el_certified_candidate`, consulted in the nominal-free
`SriqCore`/`PositiveAbox` arms of `select`, after every existing exact-fragment
gate and before the learned tree. The established one-worker production
refinement keeps priority. When the screen fires the route becomes
`Route::CertifiedElProduction` instead of `Route::ProductionAll`.

The screen admits only the EL class fragment from the source profile: named
subclass and equivalence, intersection, existential restriction, named
disjointness, and class bottom, which `elc` represents as NF5 empty-head
clauses. Every role-level feature is left to the normalized certificate.
Universal restriction, complement, any number restriction, nominal, `hasValue`,
`hasSelf`, a bottom role, negative object or data assertions, and the
asymmetric/irreflexive constraints all fail closed.

Four bounds keep the screen conservative:

* sources below 100 logical axioms keep their established route, so the screen
  does not perturb the clausification of trivial inputs;
* `disjoint_class_axioms <= distinct_classes` rejects the near-complete
  disjointness clique, whose pairwise bottom expansion is quadratic in the
  class count and which carries no positive EL structure to complete;
* `max_concept_depth <= 3` bounds the definer chains normalization introduces;
* `file_bytes <= 16 MiB` bounds the parse and normalization cost of an attempt
  that the certificate then refuses, because the exact fallback runs serially
  after it.

Disjunction follows the bound the established certified-EL gates already use,
at most 100 unions, and only alongside a genuine existential restriction and at
most one union per hundred logical axioms.

This is a scheduling change only:

* `Route::CertifiedElProduction` publishes an EL answer only on a passing
  canonical-model certificate (`KM_ELC_CERT=2`); a refusal, a residue, or a
  worker failure reruns the absorbed production portfolio, which is exactly the
  route the arm would otherwise have selected.
* The screen is restricted to the two nominal-free fragments, where
  `production_all` is the exact automatic fallback and the source is already
  ELC-publication-safe (`abox_axioms == 0`, or a positive-ABox separation
  certificate). Nominal sources keep the exact nominal calculus.
* No calculus rule, ordering, or redundancy criterion changes, so no Lean
  re-certification is due.

## Result

### Checksum-pinned IBEX validation

IBEX array `51248960` ran every one of the 119 profiles whose selected route
changes. It used the candidate binary with SHA-256
`65f289c182564acc062fe50d728e54f2d0a873d32b7635dca58e25d257de68f1`
on Intel Xeon Gold 6248 nodes, with a 480 s timeout and 20 GiB reasoner
memcap. All 119 tasks produced a result, checkpoint, route trace, and
`TASK_COMPLETE` marker. All 119 returned `status=ok`, and all 119 signatures
matched the Konclude gold. No failure artifact was produced.

The measured panel confirms 115 strict passes among the 119 changed profiles,
up from 107 on the preceding default sweep: **eight recoveries and zero
regressions**. The recovered ontologies are 1272, 1793, 2627, 6423, 7300,
10314, 13071, and 13887. Measurement noise moved one boundary result in each
direction relative to the projection: 14312 narrowly missed its wall target,
while 1272 passed both targets. The net result remains the projected eight.

The complete task outputs and checkpoints are retained under
`.work/artifacts/v14-bounded-near-el-panel/panel/`; the source archive and
Slurm scripts are in `.work/artifacts/v14-bounded-near-el-panel/`.

### Pre-run projection

The projection runs the real selector. All 592 recorded source profiles
(`.work/artifacts/v14-final-candidate-sweep-job51195701/profiles/`) were
deserialized into `OntologyProfile` and passed through `routing::select`
before and after the change, and each ontology whose executed path changes had
its measurement replaced by the 2026-07-27 `km_route_elc_cert` row, or by the
serial refusal-plus-fallback cost where that row is not sound-and-complete.

| | |
|---|---:|
| profiles whose selected route changes | 119 (all `production_all` -> `certified_el_production`) |
| of those, executed path actually changes | 100 |
| kept by an earlier path (18 `elc`, 1 `flat_nf1`) | 19 |
| strict failures recovered | 8 |
| strict regressions | 0 |
| fired ontologies whose certificate refuses | 2 |

Recovered: 1793, 2627, 7300, 10314, 13071, 13887, 14312, 6423.

The 19 selector-only rows are sources the frontend already upgrades to the bare
`elc` route after normalization proves the retained TBox is pure EL, or (2491)
the `flat_nf1` pre-route path. They keep that route; the only difference is
that their clause set is now built unabsorbed, which is the form `elc`
recognizes. All 19 pass the strict gate today with roughly a 2x wall and 4x
peak margin, and the sweep's `km_route_elc` arm, which is that same unabsorbed
bare-EL configuration on the slower binary, is sound-and-complete and strictly
below both targets for all 19.

The two refusals are 15491 (0.48 s attempt, 1.97 s serial total) and 7956
(3.50 s attempt, 8.79 s serial total). Both already fail the strict gate on the
current route and both stay far below the 240 s limit, so neither loses a
completion. Every other ontology whose path changes has a sound-and-complete
`km_route_elc_cert` row, so the 592/592 correct-completion count is preserved.

Projected aggregate over the 592 correct completions, using the same
pessimistic substitution: wall mean 1.4801 -> 1.4804 s, wall median unchanged
at 0.1401 s, peak mean 216.31 -> 211.63 MiB, peak median 23.87 -> 24.18 MiB.

## The other 29 candidates

They are not recovered here, and the reason is a soundness boundary rather than
a missing threshold:

* 12 sit on the exact nominal route (13035, 13132, 1555, 15615, 2678, 2744,
  2860, 5564, 8006, 9096, 9557, 10749) and 4 more on `certified_nominals` or
  `ht_general` over a nominal source (1340, 14450, 3905, 2453). Their winning
  arms are plain CB bundles without `KM_NOMINALS=1`, or the EL certificate on a
  source that is not ELC-publication-safe. Selecting either from a source gate
  would publish a TBox projection for singleton/ABox meaning.
* 10 sit on `production_all` (10123, 10127, 11207, 11316, 15725, 2195, 4827,
  7901, 8347, 9014) with bare-CB or thread-count winners. A blanket
  `production_all8`/`production_all1` reroute scores 6 recoveries against 7
  regressions on the absolute model and 1 against 1 on a within-sweep ratio
  model, so there is no separating source screen worth landing.
* 2195 is a 19-class complete disjointness clique. It is excluded by the same
  bound that keeps 9020 (10,315 disjointness axioms over 185 classes) from
  regressing.
* 4572 and 8480 are large ABox sources on `ht_general`.

## Files

* `strict-failures-with-a-winning-route.tsv` - the 37-row candidate ledger.
* `gate-projection.tsv` - the before/after selected route, the executed-path
  change, and the strict projection for all 592 profiles.
