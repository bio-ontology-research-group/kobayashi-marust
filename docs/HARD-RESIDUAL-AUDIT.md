# Hard residual audit and gold-adjudication status

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

## Consequences for coverage accounting

- `10702`, `15672`, and `6934` are restoration failures, not new reasoning
  frontiers.
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
