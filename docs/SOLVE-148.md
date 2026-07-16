# Closure record for ore_ont_148

Status: **CLOSED for exact ORE classification on 2026-07-16.** Production
`km classify --route nominals` terminates within the 240 second and 20 GiB
limits and returns the exact Konclude canonical signature. This closes the
coverage failure. It does not yet close the separate performance gap to
Konclude; the routing benchmark must retain that distinction.

## Exact result

The final workstation validation used the normal named `nominals` route, with
no external `KM_STATIC_SCHED` setting:

| Measure | KM | Konclude gold |
|---|---:|---:|
| Consistent | yes | yes |
| Canonical non-self subsumptions | 21,037 | 21,037 |
| Unsatisfiable classes | 0 | 0 |
| Extra pairs | 0 | 0 |
| Missing pairs | 0 | 0 |
| Signature SHA-256 | `10ef79ea10318d5197169737fc59d7d5771162a452a2e4e1a74a7a0ca880d944` | same |
| Wall time on `ws` | 54.69 s | not compared across hosts |
| Peak RSS on `ws` | 3,029,400 KB | not compared across hosts |

The same source also keeps the two earlier exact nominal closures intact:
ore_ont_11016 returns 265/265 pairs in 0.74 seconds, and ore_ont_178 returns
56/56 in 0.23 seconds. Both have zero pair, unsatisfiability, and consistency
differences.

The first portable Bullseye closure binary has SHA-256
`bf2875c9c234017a47881dc9b25086c8fdf6c2a673a869fb0ebbb48b142691f8`.
IBEX smoke job 48943813 ran the same production route on an Intel Xeon Gold
6248 and independently confirmed the exact signature:

| Ontology | Wall time | Peak RSS | Canonical verdict |
|---|---:|---:|---|
| 148 | 53.7969 s | 2,985.21 MB | exact, signature SHA-256 `10ef79ea…944` |
| 178 | 0.2687 s | 40.94 MB | exact, 56/56 worker pairs |
| 11016 | 0.5875 s | 190.62 MB | exact, 265/265 worker pairs |

The later source-symbol typing correction does not change these signatures.
Current portable binary
`c229366fcc9efbfec729f5a7dcc1a5f1ef9b12fe41f433b67282930bf18a92f6`
repeats the exact gate in IBEX job 48946056: 148 takes 53.3149 seconds at
2,956.60 MB, 178 takes 0.2653 seconds at 43.71 MB, and 11016 takes 0.5871
seconds at 192.90 MB.

For 148, the worker reports 17,742 pre-output subsumptions; declared-class and
IRI output completion produces the 21,037-pair canonical ORE signature. The
comparison reads that final signature on both sides and reports zero extra,
zero missing, zero unsatisfiability differences, and no consistency mismatch.

## What failed before the fix

The failure was termination, not a known wrong answer. The pre-fix exact
nominal route ran for about 190 seconds before its internal resource backstop
reported an error. A proxy-only CB arm happened to match this ontology's gold,
but the proxy transformation is incomplete for OWL nominals in general. KM
therefore cannot select that result under the soundness and completeness
contract merely because it agrees on this input.

The exact ground context reached 240,153 inter-context messages, consisting of
4,983 Succ and 235,170 Pred messages, plus 74,106 worked-off successor clauses.
After isolating every contiguous query group, only the group containing
`Cryosphere` failed to terminate. Its relevant source axioms are:

```text
Cryosphere ⊑ Hydrosphere
Cryosphere ⊑ ∀ hasSubstance.Ice
Cryosphere ⊑ ∀ hasUpperBoundary.PlanetarySurface
Hydrosphere ⊑ PlanetaryRealm
Hydrosphere ⊑ hasSubstance value Water
```

The last two restrictions make the named individual `Water` query-dependent:
the base ABox label gains `Ice` while classifying `Cryosphere`. A Pred trace
then found one eight-premise incoming clause with six exact providers for each
premise. Rebuilding its Cartesian product costs `6^8 = 1,679,616` candidate
resolvents each time it fires. Dynamic query scheduling made the problem worse:
a long-lived worker accumulated several independently conditioned nominal
labels in one ground context, multiplying later r-Pred joins even though the
clause bodies kept the labels logically separate.

## Konclude and Sequoia correspondence

Konclude's
`CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyNOMINALRule`
does not recompute a nominal from an unstructured union of every classification
task. It obtains the nominal's completed consistency-graph or backend full
concept-set label, compares the task's saturation label with that base, marks
the nominal as influenced when the task contributes a new concept, and copies
the completed base label into the task. Its enabled-by-default
`Konclude.Calculation.Optimization.NominalSaturation` option explicitly says it
uses the consistency-test completion graph for concepts connected to nominals.
The relevant upstream implementation is at lines 6878 through 6966 of
`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`.

For the context-calculus side, Sequoia's `Rules.Pred` still defines the exact
Cartesian product, followed by `resultsBuffer.removeRedundant`. Its context
state also uses exact maximal-head predicate and term indexes plus an active
redundancy index. KM follows those semantics and changes only how it enumerates
the same antichain.

## Targeted fix

Four related changes close the exact path:

1. **Exact Sequoia lookup indexes.** Pred now uses the exact maximal-head
   predicate index, Eq uses the exact maximal-head term index, local Pred pins
   the current triggering clause, and back-subsumed queued Pred pushes no longer
   fire. These changes remove scans and stale work without changing any rule.
2. **Exact active redundancy semantics with a Rust-appropriate index.** A direct
   generic tree port proved slower on the long nominal clauses. KM now indexes
   every worked-off head literal, scans the rarest exact posting, handles
   empty-head clauses separately, and explicitly checks the normally short todo
   queue. Exact strengthening tests preserve Sequoia's complete active set.
   At the same 20,000-message ground state, the generic tree spent 11.97 seconds
   in its search and 13.55 seconds in clause addition; the posting index reduced
   those figures to 1.66 and 2.73 seconds. Full ground closure then completed in
   19.56 seconds at 158,120 KB instead of exceeding 120 seconds.
3. **Incremental Pred antichain join.** KM orders Pred dimensions by candidate
   count and applies the same strengthening antichain after every left-deep join
   step. If partial clause `P` strengthens `Q`, then `P ∪ R` strengthens
   `Q ∪ R` for every remaining completion `R`. Every pruned extension
   therefore has a stronger final extension, so the final antichain is exactly
   Sequoia's Cartesian-product result. The isolated `Cryosphere` query now
   completes in 30.53 seconds at 232,672 KB.
4. **Nominal-influenced task isolation.** The `nominals` route now assigns one
   fixed contiguous query slice to each exact Engine. This mirrors Konclude's
   separation of influenced saturation tasks and bounds the number of
   conditional labels coexisting in one ground context. It changes only the
   partition of independent per-query fixpoints. `KM_NOMINAL_DYNAMIC=1`
   restores the general work-stealing scheduler for controlled measurements;
   `KM_STATIC_SCHED=1` remains available for every mechanism.

KM also implements a narrower, proof-carrying version of Konclude's nominal
label reuse for classes proved equivalent to a finite nominal enumeration. The
detector requires both directions of the union equivalence, every singleton
equality, and every ground nominal fact. It takes the exact sameAs closure and
intersects the completed labels of all enumerated individuals. This closes
ore_ont_11016, but ore_ont_148 contains no `ObjectOneOf`, so that shortcut does
not participate in the 148 result.

## Correctness argument and permanent tests

The fix changes lookup structures, join enumeration, and query scheduling. It
does not add, remove, or weaken a CB inference rule:

- exact indexes return the same eligible clauses as the previous scans;
- incremental Pred returns the same final strengthening antichain as the full
  product;
- static partitions compute the same independent query fixpoints and union the
  same subsumptions;
- the enumeration shortcut publishes an answer only after its explicit finite
  equivalence certificate and a complete ground-message fixpoint.

No CB calculus re-certification is needed for the first three changes because
the derived fixpoint is unchanged. The existing nominal calculus remains
covered by `lean/ContextCalculus/Nominals.lean`. Permanent Rust tests compare
incremental Pred with the Cartesian antichain, verify the active redundancy
index against exact linear strengthening, require the reverse nominal-union
proof, and exercise completed nominal-label reuse. The release suite reports
1,515 passed, 0 failed, and 7 ignored after the source-symbol typing tests.

## Remaining performance obligation

The frozen same-node matrix measured official Konclude on ore_ont_148 at
0.3175 seconds and 177.27 MB with one worker, and 0.2699 seconds and 267.90 MB
with 16 workers. The pre-fix exact nominal KM arm errored after 190.33 seconds.
The current IBEX smoke measures the exact path at 53.3149 seconds and 2,956.60
MB on the required CPU model. The time and memory gaps are therefore far beyond
20 percent against the frozen Konclude references. The first paired matrix job
48943875 was cancelled after exposing an independent source-symbol
completeness bug. Corrected full matrix job 48946164 measures all 28 isolated
arms over all 592 ontologies; its regression audit and learned-tree training
remain pending. The performance gap is an algorithmic issue, not a reason to
select the incomplete proxy arm.
