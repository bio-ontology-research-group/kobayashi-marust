# Hard residual audit and gold-adjudication status

## Current default-route status (2026-07-31)

The source-bound sweep is the current authority for one automatic
`km classify` binary. IBEX array `49701329`, accepted by independent audit
`49710709`, completes 589 of 592 ontologies: 587 exact full-IRI gold matches
and two adjudicated consistency mismatches, 2669 and 15516. The three
non-completing rows are:

| Ontology | Default-route result | Current obligation |
|---|---|---|
| `10860` | unsupported | Four DL-safe rules contain unsupported data-property or built-in atoms; establish a complete rule procedure and authoritative gold. |
| `1194` | error | The large SRIQ ABox exceeds the current packed-term boundary or practical CB completion budget; no validated route exists within the standard contract. |
| `4669` | timeout | Previously terminating KM outputs were unsound; retain fail-closed behavior until a sound complete route exists. |

Ontology 7499 is no longer residual. Automatic `certified_card_proxy_abox`
matches exactly in 86.7359 seconds at 2,409.59 MiB. The normalized
positive-role ABox certificate proves that publishing the TBox taxonomy is
exact and retains the nominal CB fallback when any obligation fails.

Ontology 6934 is no longer residual. The post-normalization typed-ABox SHOIQ
certificate selects `nominal_ni_abox`; it matches exactly in 199.3235 seconds
at 1,434.64 MiB. The remainder of this document preserves older panel and
cross-revision evidence for provenance and must not be read as current
default-route status.

## Current panel and cross-revision ledger status (2026-07-22)

The fresh uniform panel on 2026-07-22 tests the frozen current revision across
all 592 ontologies and all 66 procedures. It validates 562 automatic-route
answers, 575 answers under the routes selected before the panel, and 579 under
a post hoc fastest-correct current-route selection. The older 589 total below
is a source-bound cross-revision ledger, not the behavior of one current binary.
See
[`../results/benchmarks/2026-07-22-reproduced-route-performance/`](../results/benchmarks/2026-07-22-reproduced-route-performance/).

Direct full-IRI validation supersedes the local-name-only status below for the
source-collision family. Identity-safe source symbols close 3524, 15703, and
13503; a fixed 7581 run remains exact. The complete route registry now records
587 exact-to-authoritative-gold ontologies and two additional independently
adjudicated correct inconsistent ontologies, for 589 demonstrated-correct
inputs out of 592.

IBEX job `49272959` reproduced all 589 claims from exact source/build/runtime
evidence and fresh full-IRI references. The authoritative 592-row ledger and
its external receipt are
[`../results/benchmarks/2026-07-21-route-confirmation/reproduced-route-ledger.tsv`](../results/benchmarks/2026-07-21-route-confirmation/reproduced-route-ledger.tsv)
and
[`reproduced-route-ledger-receipt.json`](../results/benchmarks/2026-07-21-route-confirmation/reproduced-route-ledger-receipt.json).
The remaining three rows are explicit nonclaims, not failed provenance checks.

The source-bound Capsule-10 revision closes 10621 through `KM_ROUTE=ht_bridge`
in 118.2149 seconds at
1096.54 MiB. One runtime trace selects `ht_bridge`; KM and fresh source-built
Konclude produce the same full-IRI taxonomy with 70,827 subsumptions and 33,433
unsatisfiable named classes. The taxonomy SHA-256 is
`066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e`.
The frozen current revision in the 2026-07-22 panel rejects that route, so this
remains a source-bound cross-revision result rather than a current-binary one.

Three ontologies remain unclosed:

| Ontology | Current state | Blocking evidence |
|---|---|---|
| `4669` | known incorrect bridge output now rejected; no validated sound-and-complete route | HermiT proves eight sampled production-UNSAT classes and all 56 additional HT-UNSAT classes satisfiable. A reproducible source-built Konclude also times out after 3,600 seconds at 53,014 MB without a taxonomy. The inverse negative-existential mirror gate now makes the bridge defer before search; see the [Konclude verification and source trace](ORE-4669-KONCLUDE-VERIFICATION.md). |
| `10860` | unsupported and no authoritative full gold | Four of 17 DL-safe rules contain unsupported atoms. Three date/time rules are provably inert because the source has no data assertions or data-property inclusions/equivalences. The sole live gap is a finite named-ABox rule using `hasClass` and `isSubClassOf`; CB bypass reaches its internal cap. |
| `1194` | no completion within 240 s / 20 GiB | Konclude exceeds 20 GiB and HermiT times out on the 221,086-assertion SRIQ ABox. KM's own 20 GiB wall was the per-worker clone of the million-clause arena; sharing one prepared ontology across parallel CB workers cut the 56-thread engine peak from 19.58 GiB to 4.15 GiB (2026-07-30, [`../results/benchmarks/2026-07-30-cb-shared-prepared-ontology/`](../results/benchmarks/2026-07-30-cb-shared-prepared-ontology/README.md)). The adaptive composite-term layout now represents this ontology losslessly. A source-current `km classify` run on 2026-07-31 selected `nominals`, finished the frontend in 8.64 seconds, and ran the exact CB worker to its 190-second central cap; it returned no taxonomy after 198.98 seconds total at 3.58 GiB peak. KM is now wall-clock bound, not term-encoding or memory bound. |

The certified-EL investigation of `1194` now passes the original same-filler
Skolem-witness obstruction, but exposes the next exact model-construction gap.
Residual concepts `Q_118720` and `Q_118721` encode the exhaustive, disjoint
partition between at most two and at least three `connects` successors in
`UBERON_0001075`. The current greedy repair repeatedly makes a locally
incompatible side choice and reconstructs the full model. Setting its restart
budget to zero was tested as a diagnostic: it declined safely after 113.92
seconds at 5.15 GiB and emitted no taxonomy. Closing this path requires a
cardinality-aware partition assignment that still passes every residual
clause, not a smaller retry budget.

The executable identities, full-IRI fingerprints, told-edge checks, HermiT
counterexamples, and per-ontology commands are retained in the source-bound
ledger above. Historical route provenance remains under
[`../results/benchmarks/2026-07-18-ore-solve-routes/`](../results/benchmarks/2026-07-18-ore-solve-routes/).

## Previous production sweep checkpoint (2026-07-17)

The current production array, job `49012346`, has completed. It published 590
ordinary rows; `3524` and `15703` reproduced explicit Slurm OOM kills, after
which the guarded finalizer published their SHA-matched `memout` rows. The
dataset contains exactly 592 unique rows for binary SHA `8771789c…`.

The current `production_all` candidate reports 582 `ok`, six timeout, three
memout, and one unsupported. It has 575 literal matches to stored signatures.
Its only literal outcome change from job `49009500` is `13503`, where KM now
reports the logically required unsatisfiability of `daml+oil#Nothing`; the
stored signature omits that entailment. Correct tab-delimited gold loading also
removes the false `extra=1` verdict on `11745`. Its remaining production-route timeout tail is `10702`,
`15672`, `6934`, `9540`, `3215`, and `10621`; `7499` completes but remains
incomplete only under the known CHEBI local-name-collision comparison; its
reasoning result is complete. `1194`, `3524`, and `15703` are memout, while
`10860` is unsupported. This checkpoint
does not replace the 584-case cross-run exact union: it measures one current
production route and identifies which historic route closures still need to
be restored into that route.

At this previous checkpoint, the current-result route registry retained 577
literal exact ontologies. Its
oracle-minimum averages are 3.368 seconds and 297 MB, with medians of 0.191
seconds and 27 MB. The next cycle reviews the remaining route and correctness
patches, runs release tests and focused ontology checks, then freezes and sweeps
the next candidate over all 592 inputs.

Full sweep `49014377` tested the attempted `9635` positive-`CCEQ` recognition
repair. It left the missing `FiniteSemanticStructure` to `FiniteRuleSetModel`
subsumption unchanged and made `9724` exceed the 20 GiB cap, so that repair was
reverted. The corrected tab-delimited gold loader independently verifies
`11745` as exact and accounts for the registry increase from 576 to 577.

This is the durable status record for the six ontologies that were called the
"hard residuals" during the 2026-07-15 routing-matrix analysis:

```text
10621 10702 10860 1194 15672 6934
```

Do not treat membership in this list as evidence that KM has never solved an
ontology. The list mixed three different states:

1. an exact KM classification existed but the current route matrix did not
   restore it;
2. the available Konclude signature was not an authoritative gold;
3. no reference signature existed at all.

## Evidence vocabulary

Use these terms consistently:

- **exact closure**: KM completed classification and its canonical signature
  matched an authoritative reference with zero missing and zero extra
  subsumptions;
- **verdict adjudicated**: consistency or a particular unsatisfiability claim
  has a self-contained semantic witness, but a complete taxonomy may still be
  unavailable;
- **no authoritative gold**: a parseable KM result is not enough to call the
  ontology solved; the result still needs an independent signature or a
  proof-producing/adjudicated decomposition;
- **measurement-only route**: a route produced the right corpus answer
  empirically but lacks the contract needed for automatic production routing.

## Audited status

| Ontology | Audited status | Historical evidence | Required action |
|---|---|---|---|
| `10702` | **Previously closed exactly** | Commit `f985b97`: production default route, 587/587 subsumptions, byte-exact to corrected Konclude gold; full 584-ontology panel had zero DIFF. Retained 2026-07-10 run: default about 20 s / 786 MB. | Preserve the nominal ABox role-assertion augmentation and restore the production route in the current matrix. |
| `15672` | **Previously closed exactly** | Fast Ht recognition sweep: 142/142 MATCH, 3.0 s / 14.8 MB. SHOQ production sweep independently matched 142/142; the old fallback presentation waited about 225 s for doomed CB, while Ht itself decided in 0.2–3 s. Retained 2026-07-10 runs also match. | Restore a sound, contract-eligible SHOQ/HT route or equivalent bridge route. |
| `6934` | **Previously closed exactly by a measurement route** | Retained full-sweep `htforce` row: MATCH in under 1 s at about 40 MB. Retained default rows also matched after waiting for the fallback budget. Current source profiling finds 624 data assertions and 11 max/exact-data-cardinality properties. The latter cover 563 asserted individual/property pairs, with no pair carrying two syntactically distinct values. This removes one obvious clash mechanism but does not discharge datatype equality, ranges, inverse functionality, object cardinality, nominals, or the universal-role occurrence. | Revalidate the closing Ht mechanism under a sound complete-or-defer fence before making it an automatic route. A parsed-AST certificate must cover the remaining interactions; the syntactic value count alone is not an admission predicate. |
| `10621` | **Closed exactly by a source-bound candidate; not reproduced by frozen current main** | The earlier told-axiom, bottom-prepass and filtered-ELK work localized the missing mechanism. The final source-bound capsule-10 replay selects `ht_bridge` exactly once and matches fresh source-built Konclude on all 70,827 subsumptions and 33,433 unsatisfiable named classes. The 2026-07-22 frozen current route returns unsupported. | Preserve the source-bound record and full-IRI regression, then restore and revalidate the mechanism on current main. Do not replace it with the earlier partial projections. |
| `1194` | **No authoritative gold; no confirmed prior KM closure** | No retained Konclude signature. The ontology is a 75 MB SRIQ input with about 1.06 M normalized clauses, 70,231 named classes, and 221,086 class assertions. Historical KM routes time out. Earlier “thread artifact” language was a hypothesis, not a closure. Since 2026-07-30 the parallel CB attempt is no longer memory bound (19.58 GiB to 4.15 GiB at 56 threads after prepared-ontology sharing). The adaptive `f(o)` layout also removes the former encoding failure: a 2026-07-31 source-current default run reached the exact worker's 190-second cap at 3.58 GiB instead. The remaining operational blocker is wall clock. | Reduce the exact nominal CB search enough to reach fixpoint, while pursuing an independently checked consistency/taxonomy decomposition; do not treat `nogold` as success. |
| `10860` | **No authoritative gold; no confirmed prior KM closure** | No retained Konclude signature. The ontology contains 17 `DLSafeRule` axioms; Konclude's ORE path cannot supply valid gold and HermiT cannot parse the raw input. Historical KM routes time out or exhaust memory. Direct source inspection proves the three date/time built-in rules inert: there are no data assertions, sub-data-property axioms, or equivalent-data-property axioms. One `hasClass`/`isSubClassOf` meta-rule remains live. | Evaluate the one finite named-ABox meta-rule together with the 13 parsed rules, materialize their role heads, and establish consistency independently; do not treat the inert data rules or `nogold` as success. |

## Additional no-gold ontologies from the complete 592 matrix

The 2026-07-16 complete routing matrix
(`results/benchmarks/2026-07-16-routing-complete592/`) confirmed the corpus
contract as **587 Konclude-gold plus five no-Konclude-gold**. Two of the five,
`1194` and `10860`, are tracked above. The strict correctness audit reported
three more that HermiT could not adjudicate in that run:

| Ontology | HermiT status | Audited status |
|---|---|---|
| `15703` | error | **Closed by fixed KM; fresh full-IRI Konclude and ELK agree exactly** |
| `3524` | error | **Closed by fixed KM; fresh full-IRI Konclude and ELK agree exactly** |
| `4669` | timeout | **Completed KM outputs disproved by targeted HermiT queries** |

The strict analyzer deliberately exited with code 2, and no `nogold` result was
promoted to a match. Subsequent full-IRI Konclude/ELK checks supply the missing
references for 3524 and 15703; targeted HermiT queries refute 4669's completed
answers. The original fail-closed handling was therefore correct.

## Corpus remainder after the all-retained-run union

After restoring every retained exact closure, applying the source-symbol fix
and validating the final 10621 bridge route, five ontologies lie outside the
587-case exact-to-authoritative-gold union:

- `2669` and `15516` are solved by KM and independently adjudicated
  inconsistent, but cannot enter the exact-Konclude column because their stored
  Konclude signatures are stale parse-failure artifacts.
- `4669` has retained historical KM classifications that targeted HermiT
  queries disprove. Current source rejects that bridge fragment instead of
  publishing either retained answer.
- `10860` and `1194` have neither an authoritative full gold signature nor a
  confirmed retained KM closure.

Thus the source-bound cross-revision ledger contains 587 exact and 589
demonstrated-correct answers after gold adjudication. One additional ontology
has terminating but unsound KM outputs whose logical completeness is unknown;
the current guard returns no answer. Two more have no validated
sound-and-complete route within the limits.

## Consequences for coverage accounting

- `10702`, `15672`, and `6934` are restoration failures, not new reasoning
  frontiers.
- The frozen 592-ontology route matrix also omitted retained exact closures for
  `10908`, `11745`, `7499`, `9540`, `9635`, and `3215`. Together with the three
  hard-residual restorations, these nine closures raised the pre-fix exact
  cross-run KM union from the matrix-local 575 to 584. The corrected route
  registry, source-symbol fix and final 10621 bridge route establish the
  cross-revision documented exact count of 587.
- `2669` and `15516` raise the adjudicated demonstrated-correct total to 589,
  but must not be described as matches to their stale Konclude signatures.
- `10621` has a complete source-bound `ht_bridge` result against fresh
  source-built Konclude, but frozen current main does not reproduce it. Do not
  use or describe the older zero-unsatisfiable signature, and do not substitute
  the bottom-prepass or filtered-ELK partial projections for the final full
  taxonomy.
- `1194` and `10860` must not count as correct merely because a KM route returns
  `ok` or `nogold`. They need adjudicated gold.
- Therefore the phrase "six unsolved hard residuals" remains prohibited. The
  current unclosed frontier has three ontologies with the distinct blockers
  listed at the top of this document.

## Primary retained evidence

- `f985b97` for the `10702` nominal ABox fix and corpus-wide validation.
- `results/benchmarks/2026-06-25-ht-recognition-sweep.md` for the direct
  `15672` closure.
- `results/benchmarks/2026-06-25-shoq-route-sweep.md` for the independent
  production SHOQ confirmation.
- IBEX retained rows under
  `/ibex/scratch/hohndor/km/fullsweep/res/ore_ont_{10702,15672,6934}.owl.jsonl`.
- `docs/CONTESTED-GOLD.md` for the existing `10621` witness and the invalid
  Konclude/SWRL gold mechanism.
- `results/benchmarks/2026-07-15-routing/profile-table.csv` for the current
  structural profiles of `10860` and `1194`.
