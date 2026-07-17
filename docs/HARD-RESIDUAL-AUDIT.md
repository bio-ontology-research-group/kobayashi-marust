# Hard residual audit and gold-adjudication status

## Current production sweep checkpoint (2026-07-17)

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

The current-result route registry retains 576 literal exact ontologies. Its
oracle-minimum averages are 3.325 seconds and 292 MB, with medians of 0.192
seconds and 27 MB. The next cycle reviews the remaining route and correctness
patches, runs release tests and focused ontology checks, then freezes and sweeps
the next candidate over all 592 inputs.

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
| `6934` | **Previously closed exactly by a measurement route** | Retained full-sweep `htforce` row: MATCH in under 1 s at about 40 MB. Retained default rows also matched after waiting for the fallback budget. | Revalidate the closing Ht mechanism under a sound complete-or-defer fence before making it an automatic route. |
| `10621` | **Current gold semantically confirmed; KM performance residual** | A told-axiom witness proves `Zone_of_cell` unsatisfiable through two distinct boolean values on functional data property `has_mass`. Contrary to an older note, the current IBEX Konclude signature already contains `Zone_of_cell` and 33,433 unsatisfiable named classes. Checked descendants including `Apical_part_of_cell`, `Basal_part_of_cell`, and `Zone_of_cone_cell` are present in that unsatisfiable block. | Preserve the current corrected signature and treat KM's timeout as a classification-performance problem, not an unresolved gold dispute. |
| `1194` | **No authoritative gold; no confirmed prior KM closure** | No retained Konclude signature. The ontology is a 75 MB SRIQ input with about 1.06 M normalized clauses, 70,231 named classes, and 221,086 class assertions. Historical KM routes time out. Earlier “thread artifact” language was a hypothesis, not a closure. | Establish consistency and taxonomy by decomposition/cross-checking, not by treating `nogold` as success. |
| `10860` | **No authoritative gold; no confirmed prior KM closure** | No retained Konclude signature. The ontology contains 17 `DLSafeRule` axioms; Konclude's ORE path cannot supply valid gold and HermiT cannot parse the raw input. Historical KM routes time out or exhaust memory. | Inspect the rules and ABox directly, derive or refute an inconsistency witness, then classify the rule-free and rule consequences separately with independently checked results. |

## Additional no-gold ontologies from the complete 592 matrix

The 2026-07-16 complete routing matrix
(`results/benchmarks/2026-07-16-routing-complete592/`) confirmed the corpus
contract as **587 Konclude-gold plus five no-Konclude-gold**. Two of the five,
`1194` and `10860`, are tracked above. The strict correctness audit reported
three more that HermiT could not adjudicate in that run:

| Ontology | HermiT status | Audited status |
|---|---|---|
| `15703` | error | **No authoritative gold; unadjudicated** |
| `3524` | error | **No authoritative gold; unadjudicated** |
| `4669` | timeout | **No authoritative gold; unadjudicated** |

The strict analyzer deliberately exited with code 2, and no `nogold` result was
promoted to a match. These three still need an independent oracle; do not count
a KM `ok` result as correct without adjudication.

## Corpus remainder after the all-retained-run union

After restoring every retained exact closure, eight ontologies lie outside the
584-case exact-to-authoritative-gold union:

- `2669` and `15516` are solved by KM and independently adjudicated
  inconsistent, but cannot enter the exact-Konclude column because their stored
  Konclude signatures are stale parse-failure artifacts.
- `3524`, `15703`, and `4669` have completed KM classifications, but no
  authoritative reference signature. They are candidate closures, not yet
  demonstrated-correct full taxonomies.
- `10621` has authoritative current gold and a confirmed unsatisfiability
  witness, but no retained complete KM classification within the benchmark
  budget.
- `10860` and `1194` have neither an authoritative full gold signature nor a
  confirmed retained KM closure.

Thus the current counts are 584 exact, 586 demonstrated correct after gold
adjudication, and three further completed-but-unadjudicated candidates.

## Consequences for coverage accounting

- `10702`, `15672`, and `6934` are restoration failures, not new reasoning
  frontiers.
- The frozen 592-ontology route matrix also omitted retained exact closures for
  `10908`, `11745`, `7499`, `9540`, `9635`, and `3215`. Together with the three
  hard-residual restorations, these nine closures raise the exact cross-run KM
  union from the matrix-local 575 to 584.
- `2669` and `15516` raise the adjudicated demonstrated-correct total to 586,
  but must not be described as matches to their stale Konclude signatures.
- `10621` may be scored against the current IBEX Konclude signature. Do not use
  or describe the older zero-unsatisfiable signature. KM still owes a complete
  within-budget taxonomy.
- `1194` and `10860` must not count as correct merely because a KM route returns
  `ok` or `nogold`. They need adjudicated gold.
- Therefore the phrase "six unsolved hard residuals" is prohibited in reports
  unless the report immediately separates these three categories.

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
