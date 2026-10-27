# Realization: individual types and equalities

`km classify --realize` reports, in addition to the class taxonomy, the
entailed named types of every named individual and the entailed equalities
between named individuals. Without the flag the output is unchanged.

```sh
km classify --lines --realize ontology.owl          # all entailed types
km classify --lines --realize=direct ontology.owl   # most specific types only
km classify --realize ontology.owl                  # JSON
```

## Output

Line output (`--lines`) prints the ordinary classification rows first, exactly
as `km classify --lines` prints them, followed by:

| Row | Meaning |
|---|---|
| `TYPE<TAB>a<TAB>C` | `O ⊨ C(a)` for the named individual `a` and the named class `C` |
| `SAME<TAB>a<TAB>b` | `O ⊨ a = b`, for `a ≠ b`; each unordered pair once, with `a < b` |

`TYPE` rows are sorted by individual, then class; `SAME` rows are sorted.
Individuals and classes use the same spelling as the classification rows.
Where a source writes one entity both as a prefixed name and as its full IRI,
KM canonicalizes it to the full IRI (printed without angle brackets); it is
one individual with one set of rows. An IRI written only as a prefixed name
keeps that spelling. A source that writes one individual with two different
prefixes and never in full is declined (exit code 3) rather than reported
under two names.

JSON output (no `--lines`) is the ordinary classification object with two more
keys: `"types"` (a list of `[individual, class]` pairs) and `"same"` (a list
of `[a, b]` pairs with `a < b`). `--realize` cannot be combined with
`--json-edges`.

## Semantics

Let `O` be the ontology, `a` a named individual of its signature, and `C` a
named class other than `owl:Thing`.

- `--realize` or `--realize=all`: `TYPE a C` iff `O ⊨ C(a)`.
- `--realize=direct`: `TYPE a C` iff `O ⊨ C(a)` and no other entailed type
  `D` of `a` is strictly below `C` (`O ⊨ D ⊑ C` and `O ⊭ C ⊑ D`). All
  members of a minimal equivalence class are listed. This is the flattened
  OWL API `getTypes(a, true)` without `owl:Thing`.
- `SAME a b` iff `O ⊨ a = b`, through `SameIndividual`, functional or
  inverse-functional roles, cardinality restrictions, nominals, or any other
  entailment.
- `owl:Thing` is never listed. An individual without `TYPE` rows has
  `owl:Thing` as its only type. A class equivalent to `owl:Thing` is a type of
  every individual and is listed.
- An inconsistent ontology is reported as `CONSISTENT 0` with no `TYPE` or
  `SAME` rows (every assertion is entailed).
- `DROPPED N` with `N > 0` means that neither the taxonomy nor the
  realization rows are complete.

The named individuals are those that occur in individual position anywhere
in the source: declarations, class and property assertions,
`SameIndividual`, `DifferentIndividuals`, `ObjectOneOf`, `ObjectHasValue`,
and DL-safe rule atoms. Anonymous individuals are not reported.

## Mechanism

Realization uses the exact reduction to classification. For each named
individual `a`, KM adds a fresh class `P_a` with `P_a ≡ {a}` and classifies
the extended ontology once with the ordinary production pipeline. The
extension is conservative: it adds no subsumption between source names. For a
consistent ontology, `O ⊨ C(a)` iff `P_a ⊑ C`, and `O ⊨ a = b` iff
`P_a ⊑ P_b`. KM removes every row that mentions a probe class, so the
taxonomy rows equal the plain classification.

No route reads types directly from its saturated state, for these reasons:

- The EL++ completion (`elc`) rejects individual terms.
- TBox-only routes keep the ABox out of the saturated clause set and check it
  separately.
- The consequence-based and hypertableau routes are complete for query-class
  subsumption, not for unit ground facts `C(a)`. Reading types from the CB
  ground context would need a new completeness argument and Lean
  re-certification.

The probe classes make each individual a query class, so the published
completeness of the route for class subsumption covers the realization.

Realization is answered only under the automatic route policy, as for
`km explain`. A manually forced route (`--route`, or `KM_ROUTE` other than
`auto`) is refused with exit code 3. Several non-nominal routes are
incomplete on the probe-extended ontology, which always contains nominals.
`KM_REALIZE_ANY_ROUTE=1` lifts the check for route diagnostics.

## Cost

The extended ontology has one more query class per named individual, and it
always contains nominals, so it can take a route other than the one used for
the plain classification. On the W3C wine ontology with food merged (206
individuals), `--realize` takes about 19 s against about 7 s for the plain
classification on the development workstation. Its rows match HermiT
exactly (1,035 `TYPE`, 12 `SAME`).
