# 2026-09-03 production-route source gates

## What this panel scores

IBEX array `51250847` re-measured nine ontologies from the residual list of the
preceding panel (`2026-09-03-v14-bounded-near-el-routing`), each of them a
strict failure for which some other KM procedure had been recorded strictly
below both external targets in the 2026-07-27 route sweep. It ran
the checksum-pinned candidate binary
`65f289c182564acc062fe50d728e54f2d0a873d32b7635dca58e25d257de68f1` on Intel
Xeon Gold 6248 nodes, three repetitions each of `auto` and the historical
winning route, 480 s timeout and 20 GiB reasoner memcap, every task verified
against the Konclude gold signature.

Five of the nine reproduce a strict recovery on the current binary:

| ontology | route | auto wall/peak | route wall/peak | target wall/peak |
|---|---|---|---|---|
| ore_ont_10127 | `cb_absorb8` | 1.110 s / 204.05 MiB | 0.889 s / 175.43 MiB | 0.905 s / 428.23 MiB |
| ore_ont_11207 | `cb_absorb8` | 0.953 s / 199.35 MiB | 0.889 s / 166.16 MiB | 0.939 s / 413.40 MiB |
| ore_ont_2195 | `cb_plain1` | 0.078 s / 31.80 MiB | 0.046 s / 8.32 MiB | 0.069 s / 29.87 MiB |
| ore_ont_4827 | `cb_absorb8` | 0.170 s / 41.47 MiB | 0.076 s / 16.66 MiB | 0.102 s / 50.52 MiB |
| ore_ont_7901 | `cb_trigger16` | 0.078 s / 13.54 MiB | 0.046 s / 14.17 MiB | 0.070 s / 30.16 MiB |

(medians of three repetitions; all fifteen route repetitions returned
`status=ok` with `verdict=match`.)

The other four are not recoveries and this panel does not try to produce one.
10123 misses its wall target on both arms (0.503 s and 0.621 s against 0.343 s)
and 14312 does the same (1.628 s and 1.893 s against 1.447 s). 15725 stays above
its wall target on the measured `cb_trigger8` arm (1.258 s against 1.046 s).
11316's recorded winner is `tab_race`, which is not a CB bundle and is out of
scope for a routing screen here; its `auto` arm is at its targets, passing on
the median of the three panel repetitions (0.206 s / 38.89 MiB against 0.220 s /
42.43 MiB) while one repetition measured 61.04 MiB, and it fails the peak
target on the default sweep row the audit uses.

## What changed

`engine/src/routing.rs` gains two source-only screens, both consulted after
every existing exact-fragment gate and before the learned tree, and both
restricted to the nominal-free fragments where `production_all` is the exact
automatic fallback.

### `positive_abox_horn_cb_candidate` -> `cb_absorb8`

A certified positive ABox (`SemanticFragment::PositiveAbox`) carrying class and
object-role assertions over a terminology whose class constructors are
intersection, existential and universal restriction only. Two properties follow
from the source alone:

* the clause set is Horn, because no source union, complement, named
  disjointness, class bottom or number restriction can produce a disjunctive
  head; and
* at least one universal restriction occurs, so the source is outside the EL
  class fragment and the portfolio's EL arm can only refuse.

The remaining portfolio arm is the certified Konclude bridge, which the CB
engine that actually decides the ontology has to be scheduled against.
`file_bytes <= 128 MiB` bounds the attempt, twice the largest measured member.
Nominals, `hasValue`, `hasSelf`, a bottom role, negative assertions,
`SameIndividual`, `DifferentIndividuals`, imports and rules all fail closed.

### `bounded_non_el_cb_terminology_candidate` -> `cb_plain1` / `cb_absorb8` / `cb_trigger16`

A small nominal-free terminology (`SemanticFragment::SriqCore`, no ABox) that
carries a construct outside the EL class fragment in every position: a
universal restriction, a number restriction, or role functionality. Any one of
them forces the portfolio's EL arm to refuse after paying for its own
normalization.

Three bounds keep the screen inside the family it was measured on:

* `logical_axioms <= 2_000` and `file_bytes <= 512 KiB`. The next larger ORE
  terminologies this screen would otherwise admit are 11623 and 1016 at 4,529
  and 5,771 source axioms, where every isolated CB arm in the 2026-07-27 sweep
  is slower than the portfolio, and then 7127, 7581, 9663, 9724 and 14817,
  where no isolated CB arm in that sweep produces a result at all.
* Disjunction density, reusing the bound the established certified-EL screens
  already use: at most one union and at most one complement per hundred logical
  axioms. This is what separates the admitted sources from the
  disjunction-heavy small terminologies (ORE 11291, 4897, 12141, 5303, 9024)
  whose isolated CB arms are slower than the portfolio or do not terminate.
* `logical_axioms >= 100` keeps the trivial band on its established route.

The bundle is chosen from the source constructors that decide whether either
absorption or a sixteen-worker partition can pay for itself. An explicit
complement occurrence keeps polarity absorption (`cb_absorb8`); a query set
below two classes per worker takes the single-worker plain bundle
(`cb_plain1`); everything else keeps the trigger-absorbed clausification the
production bundle also applies (`cb_trigger16`). Every branch runs the same
complete CB mechanism over the same retained terminology, so the choice cannot
change the published answer.

### Fail-closed behaviour

Unlike the production portfolio, these bundles set `KM_NO_RETRY=1`, so their
RSS-capped attempt is not repeated single-threaded. `automatic_atomic_fallback`
therefore now returns the exact displaced route for `cb_absorb8`, `cb_plain1`
and `cb_trigger16`: `production_all` on the nominal-free fragments,
`nominals` on a nominal source. A worker error, a non-fixpoint exit, or an RSS
trip on an automatically selected bundle returns to `production_all` instead of
failing the classification. Explicitly requested matrix routes stay atomic.

No calculus rule, ordering, or redundancy criterion changes, so no Lean
re-certification is due. `sriq_policy_eligible`, which gates what the learned
tree may emit, is unchanged.

## Result

### Projection

The projection runs the real selector. All 592 recorded source profiles
(`.work/artifacts/v14-final-candidate-sweep-job51195701/profiles/`) were
deserialized into `OntologyProfile` and passed through `routing::select` before
and after the change. Neither screen reads `profile.clauses`, which ordinary
classification leaves zeroed, so the projected selection is the selection the
shipped binary makes.

**18 of 592 profiles change route**, all of them from `production_all`, 15 to
`cb_absorb8`, 2 to `cb_trigger16`, 1 to `cb_plain1`. No other route family is
touched, and no profile outside the learned-tree population can reach either
screen.

The current measurement basis is the default full sweep
(`.work/artifacts/v14-1194-default/full-sweep-results/`, IBEX array `51242642`)
with the 119 rows the bounded near-EL panel re-measured (IBEX array `51248960`)
substituted in; that is 497 of the 592 strictly below both per-ontology
external targets. The projected measurement is:

* the measured `51250847` median for the five ontologies this panel ran on
  their new route;
* for ore_ont_15725, whose new route is `cb_absorb8` but whose measured
  `51250847` arm was the sibling `cb_trigger8`, the worse of the projection and
  that measured sibling, which keeps it a strict failure;
* for the remaining twelve, the worse of the 2026-07-27 sweep's absolute number
  on the new arm and that sweep's within-ontology arm ratio applied to the
  current measurement.

| | |
|---|---:|
| profiles whose selected route changes | 18 (all `production_all` -> an isolated CB bundle) |
| strict failures recovered | 5 |
| strict regressions | 0 |
| correct completions | 592 -> 592 |
| strict passes | 497 -> 502 |

Recovered: 10127, 11207, 2195, 4827, 7901, each of them measured on the current
binary in `51250847`.

Projected aggregate over the 592 rows: wall mean 1.4759 -> 1.4705 s, wall median
unchanged at 0.1275 s, peak mean 211.48 -> 210.17 MiB, peak median unchanged at
22.80 MiB.

### Why no rerouted profile regresses

`changed-route-evidence.tsv` carries the whole argument row by row. For all 18,
the 2026-07-27 route sweep records the new arm as `status=ok`, `sound=yes`,
`complete=yes` and signature-matching, so no completion and no correctness
verdict is at risk. On wall time and peak memory:

* the seven rerouted profiles that pass the strict gate today (10212, 10951,
  14375, 15536, 1618, 3640, 5103) keep passing under the pessimistic absolute
  sweep number on the new arm, with at least a 1.5x margin on both dimensions;
  six of them are faster than `production_all` in that sweep and ore_ont_10951
  is 2.7 ms slower;
* the five measured recoveries pass on the current binary;
* the remaining six (10697, 15725, 3164, 3658, 4187, 9958) fail the strict gate
  today and still fail it, but every one strictly improves on both wall and
  peak. They stay on the residual list.

The Horn positive-ABox family is uniform: all fourteen members share the same
RBox shape (15 RBox axioms, one functional and one sub-property axiom, three
transitive roles, four domains and four ranges). In the 2026-07-27 sweep the
isolated CB bundle beats `production_all` on wall for thirteen of them (by
roughly 2x on the eight large members) and is 2.7 ms slower on ore_ont_10951;
peak drops on thirteen and rises 2.4 MiB on ore_ont_10212, which has a 3.4x
peak margin to its target.

### What the forced-route arms did not measure

Both evidence sources ran their CB arms with an explicit `KM_ROUTE`, and the
frontend's separable-ABox elision is gated on automatic routing
(`omit_separable_abox` in `frontend::ofn_to_clauses`). The fourteen Horn
positive-ABox members therefore normalized their full asserted graph into the
measured CB runs, while under the gate the same bundle runs on the terminology
alone, exactly as `production_all` does today. That is strictly less work, so
the measured and swept numbers are an upper bound on what the gate produces,
but the combination itself was not measured.

## Residual risks

* Twelve of the eighteen rerouted profiles are projected, not measured on the
  current binary. Their evidence is the 2026-07-27 sweep, whose binary is
  slower (median wall ratio 1.48 over the ontologies where the sweep and the
  current audit share a route), which makes a "this arm already beats the
  portfolio" claim conservative but not a measurement.
* The recorded 592 profiles predate `inert_role_abox_probe_candidate`, which
  `select` consults first. The source half of that certificate declines for all
  eighteen rerouted profiles (the Horn ABox family carries role domains, ranges
  and a functional role; the terminology family has no ABox), so the missing
  field cannot change their selection.
* The `auto` plus isolated-CB-bundle combination has not been run end to end on
  the corpus. `51250847` measured the bundles under an explicit `KM_ROUTE`, so
  the selection path itself, and the ABox elision it enables, is projected.
* ore_ont_10127 and ore_ont_11207 clear their wall targets by 1.8 % and 5.3 %
  on the current binary. ore_ont_7901 clears its target on the median of three
  repetitions but one repetition measured 0.080 s against a 0.070 s target.
  These three recoveries are inside run-to-run noise of their gate.

## Files

* `gate-projection.tsv` - before/after selected route, current and projected
  wall/peak, strict verdicts and evidence basis for all 592 profiles.
* `changed-route-evidence.tsv` - the 18 rerouted profiles with the source
  features the screens read, both sweep arms, and the `51250847` measurement
  where one exists.
