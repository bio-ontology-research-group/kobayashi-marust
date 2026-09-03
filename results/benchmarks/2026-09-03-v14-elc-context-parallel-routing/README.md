# 2026-09-03 automatic EL context parallelism

## What this panel scores

`elcomplete`'s context-parallel saturation (section 9 of
`docs/ELC-HOT-LOOP-V14.md`) has been available since the mode landed, but only
as an explicit `KM_ELC_PAR_CTX` request. This panel measures it, derives a
source-feature selector for it, and arms that selector on the bare `elc` route.

The measurement is the paired IBEX array `51251013`: four arms (serial,
`KM_ELC_PAR_CTX` at 2, 4 and 8), three replicates each, over the eighteen
`elc`-routed strict residuals of `docs/ELC-HOT-LOOP-V14.md` section 8.1, on
Intel Xeon Gold 6248 nodes with 16 CPUs, a 480 s timeout and a 20 GiB reasoner
memcap, against a binary pinned to SHA-256
`06215e49a03249992718cb77df6084fc0870ad4e0a7962d995b65e217d745661`. All 216
runs returned `status=ok` with a signature matching the Konclude gold, and for
each ontology the twelve runs share one signature SHA-256: the parallel engine
is byte-identical to the serial one on real corpus input, as its determinism
argument requires.

`context-parallel-panel-medians.tsv` is that measurement, one row per
ontology, with the medians of all four arms and the external per-ontology
targets from
`results/benchmarks/2026-08-25-v1.0.0-baseline/external-per-ontology-targets.tsv`.

Two results decide the selector:

* Eight workers improved the median wall of all eighteen, by 0.3% (5566) to
  22% (795), and no member came near its external peak target on any arm.
* Two workers were **slower than the serial engine** on five members (1579,
  2469, 2828, 4802, 5566) and would have cost 2469 and 5566 their currently
  passing wall gates. Four workers improved all eighteen.

So the selector arms eight workers, four when the machine cannot supply eight,
and nothing below that.

## What changed

`engine/src/routing.rs` gains `elc_context_parallel_workers`, a source-profile
predicate returning the worker count for the EL completion. The orchestrator
consults it in `elc_context_parallel_setting`
(`engine/src/orchestrate/mod.rs`), which arms `KM_ELC_PAR_CTX` under three
rules:

* an explicit `KM_ELC_PAR_CTX` always wins, on every route, including the `0`
  that asks for the serial baseline. It is captured before route selection
  clears the route keys, so the A/B arms of this panel stay reproducible under
  `KM_ROUTE=auto` now that the key is route-managed;
* without a request, only `Route::Elc` is scheduled. The certified routes build
  their repair fork in derivation order and the worker declines the parallel
  engine under any certificate, `KM_ELC_FIFO`, or `KM_ELC_PAR_NF4`, so arming
  them would be inert at best;
* the count comes from the source profile alone. No ontology identifier
  participates, and a unit test asserts the gate body contains no `ore_ont_`.

The gate admits the shape the panel measured and nothing else. It requires the
same source EL certificate the bare route selects on
(`source_el_terminology_candidate`: an ABox-free terminology with no data
property, role domain or range, inverse declaration, or bottom role), the EL
class fragment (no union, complement, universal restriction, number
restriction, nominal, `hasValue`, `hasSelf`, or datatype constructor, and
`max_concept_depth <= 3`), work floors at the smallest measured member
(100,000 logical axioms, 20,000 classes, 20,000 existential restrictions;
`ore_ont_795` has 106,608 / 47,144 / 24,595), and ceilings at the widest
(400,000 logical axioms, 64 MiB of source and 32 role-chain axioms), and an
8--12 distinct-object-property interval.  The interval is the general
source-feature separator that retains all four measured recoveries while
excluding every otherwise-matching source absent from the panel.

Two bounds carry their own measurement:

* **No ABox.** The panel's two ABox members hold its two largest peak
  increases at eight workers (6722: 314 -> 618 MiB, a 1.97x increase, and
  1579: 819 -> 1101 MiB, 1.34x, against at most 302 -> 415 MiB and 1.38x for
  the terminology-only members), and neither
  recovers a strict gate. The individual layer stays serial.
* **The ceilings** keep the ORE giants, whose completions run in gigabytes, off
  a mode whose measured peak increase of 0-38% has no evidence at that scale.
  `ore_ont_8737`, the one giant with a parallel EL schedule today, keeps its
  NF4 frontier batch, which forces the FIFO and declines this mode anyway.

This is a scheduling change only. The context-parallel engine is a different
firing order for the same monotone rule set, reaches the same least fixpoint,
and rebuilds every label in sorted order before publication, so its output is
byte-identical at every worker count; the panel confirms that on 18 real
ontologies. No calculus rule, ordering, or redundancy criterion changes, so no
Lean re-certification is due. Failure stays closed: a worker thread that cannot
start reverts the classification to the serial engine.

## Result

### Projection over all 592 retained source profiles

`routing::tests::context_parallel_projection_over_the_retained_profiles` runs
the real selector, under full routing precedence, over every retained source
profile of the 592-ontology corpus, and asserts that no armed ontology is off
the bare EL route. It was run against both retained profile sets
(`.work/artifacts/v14-atomic-final-profiles/` and
`.work/artifacts/v14-final-candidate-sweep-job51195701/profiles/` of the `v1.4`
worktree) and produced identical projections.

`context-parallel-projection.tsv` is the complete 592-row ledger: the selected
route, the armed worker count, the source features the gate reads, the current
strict measurement (IBEX array `51242642`), both external targets, the panel
medians where the ontology was measured, and the projected verdict.

| | |
|---|---:|
| profiles whose selected route changes | 0 |
| profiles that arm the context-parallel schedule | 9 |
| of those, measured in the panel | 9 |
| projected strict recoveries | 4 |
| projected strict regressions | 0 |
| armed without a panel measurement | 0 |

The four projected recoveries are 795 (1.9122 s -> 1.5080 s against a 1.8461 s
target), 2828 (2.8614 -> 2.6597 against 2.7197), 5612 (2.4408 -> 1.6887
against 1.8041) and 15929 (1.9484 -> 1.5748 against 1.6922). Every one also
falls far below its peak target (253.68 / 431.11 / 271.63 / 266.62 MiB against
624.48 / 818.41 / 591.73 / 581.16 MiB).

The source audit predates the separately validated bounded-near-EL selector:
it contains 489 strict passes, 100 failures and 3 unadjudicated cases.  That
selector contributes eight disjoint recoveries, so the integrated default is
497/589 and this selector projects 501/589.

The five other armed, measured rows (2803, 4802, 10248, 11293, 12387) retain
their existing strict verdict; none regresses from pass to fail.

Confirmation array `51251710` increased every prospective recovery to ten
observations per serial/context-eight arm.  Their context-eight medians remain
strict wins: 15929 at 1.5757 s / 265.57 MiB, 2828 at 2.6113 / 431.23, 5612 at
1.6365 / 271.42, and 795 at 1.5222 / 253.53.  The 2828 wall margin is now
4.15%; the other margins are 7.39%, 10.24% and 21.28%.

### The twelve panel members that do not recover

4802 stays 0.5% above its wall target at eight workers (1.8471 against
1.8379), which is the closest miss of the panel. 7868, 12087, 12387, 13224,
15976 and 16596 gain 5-21% but remain 4-37% above their targets; they need the
frontend and output laps, not more EL workers. 1579 and 6722 are not armed.

## Residual risk

* **Selector generalization is deliberately bounded.** Exactly nine retained
  profiles are armed and all nine were measured.  Sources outside the 8--12
  object-property interval remain serial until a future panel supplies direct
  evidence.
* **The worker count follows the machine.** Eight workers on a host with eight
  or more CPUs, four between four and seven, serial below. The published answer
  is identical either way, but a wall measurement is only comparable to this
  panel on a 16-CPU node.
* **The serial baseline now needs an explicit arm.** On an armed profile the
  default is eight workers, so a future A/B has to request
  `KM_ELC_PAR_CTX=0` (or `KM_ELC_FIFO=1`) for its serial arm; the panel above
  measured its serial arm before the schedule existed.
* **Static `c % n` ownership does not rebalance.** A terminology inside the
  gate whose closure concentrates in a few hub contexts would gain less than
  the panel members; it cannot lose correctness, only the expected speedup.

## Integrated automatic-route confirmation

After integration at source commit `c806533837b8e27e5100ef3bb34574cb756826e7`,
IBEX build job `51251895` produced binary SHA-256
`6dacf48a554fe15663b695887cbfc232dd7f55262b5e0f54a0b62be5fba3d3cb`.
Array `51252332` ran the nine selected ontologies, automatic versus explicitly
serial, five times per arm on Intel Xeon Gold 6248 nodes.  All 90 tasks produced
a result, checkpoint, scheduler output and completion marker; every result was
`status=ok`, matched gold, and recorded route `elc`.  There were no failure
artifacts.

The automatic medians confirm the four projected recoveries.  ORE 4802 also
crossed its 1.8379-second target at 1.8226 seconds, but the 0.8% margin is too
narrow to promote before the full default-route sweep.  Therefore the retained
projection remains 501/589 and treats 4802 as an additional candidate rather
than a settled recovery.  `integrated-automatic-medians.tsv` records all nine
paired medians and targets.  The archived raw results are
`.work/artifacts/v14-elc-auto-integration/results-51252332.tar.gz`, SHA-256
`a5e9cd9eea30de895edce615e39b36bc3eaf615c92c9e02ba6c48e842663d21f`.

## Files

* `context-parallel-panel-medians.tsv` - the 18-ontology, 4-arm, 216-run panel.
* `context-parallel-confirmation-medians.tsv` - ten-observation confirmation
  medians for the four recoveries.
* `integrated-automatic-medians.tsv` - five automatic and five forced-serial
  observations for every selected profile after integration.
* `context-parallel-projection.tsv` - the complete 592-row projection ledger.
* `build_panel_medians.py`, `build_projection_ledger.py` - the two joins above,
  from the retained artifacts.
