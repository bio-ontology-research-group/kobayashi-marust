# Object property hierarchy, domains and ranges

`km classify --properties` reports, in addition to the class taxonomy, the
entailed object property hierarchy, the empty and universal object
properties, and the entailed named domains and ranges of every named object
property. Without the flag the output is unchanged.

```sh
km classify --lines --properties ontology.owl             # line output
km classify --properties ontology.owl                     # JSON
km classify --lines --realize --properties ontology.owl   # with realization, one run
```

## Output

Line output (`--lines`) prints the ordinary classification rows first, exactly
as `km classify --lines` prints them, then the `TOP` rows of the classes
equivalent to `owl:Thing` if `--top` is given, then the `TYPE` and `SAME`
rows if `--realize` is given (see `docs/REALIZATION.md`), then:

| Row | Meaning |
|---|---|
| `SUBPROP<TAB>r<TAB>f` | `O ⊨ r ⊑ f` for a named, non-empty `r` and an expression `f ≠ r` |
| `TOPPROP<TAB>r` | `O ⊨ owl:topObjectProperty ⊑ r` |
| `BOTPROP<TAB>r` | `O ⊨ r ⊑ owl:bottomObjectProperty` |
| `DOMAIN<TAB>r<TAB>C` | `O ⊨ ObjectPropertyDomain(r C)` |
| `RANGE<TAB>r<TAB>C` | `O ⊨ ObjectPropertyRange(r C)` |

Each kind of row is sorted. An object property expression is a named object
property `r` or `ObjectInverseOf(r)`. Names use the same spelling as the
classification rows.

JSON output (no `--lines`) is the ordinary classification object with five
more keys: `"subproperties"` (`[r, f]` pairs), `"topproperties"` and
`"bottomproperties"` (lists of names), `"domains"` and `"ranges"` (`[r, C]`
pairs). With `--realize` the object also carries `"types"` and `"same"`.
`--properties` cannot be combined with `--json-edges`.

## Semantics

The rows follow the convention of the class rows: `SUB` lists every entailed
pair of distinct satisfiable classes (equivalent classes in both directions,
no reflexive pairs), never `owl:Thing` itself, but classes equivalent to
`owl:Thing`, and an unsatisfiable class is marked by `UNSAT`.

- `SUBPROP r f` lists every entailed pair, strict or not, with a named `r` on
  the left. A pair with an inverse on the left is the mirror of a listed pair:
  `O ⊨ ObjectInverseOf(r) ⊑ f` iff `O ⊨ r ⊑ ObjectInverseOf(f)`.
- `r` and `s` are equivalent iff `SUBPROP r s` and `SUBPROP s r`.
- `s` is an inverse of `r` iff `SUBPROP r ObjectInverseOf(s)` (and then also
  `SUBPROP s ObjectInverseOf(r)`). `r` is symmetric in the sense
  `r ≡ ObjectInverseOf(r)` iff `SUBPROP r ObjectInverseOf(r)`.
- `owl:topObjectProperty` and `owl:bottomObjectProperty` never appear as a
  property in any row. `TOPPROP r` marks a property equivalent to
  `owl:topObjectProperty`; every non-empty property then has `SUBPROP` rows to
  `r` and to `ObjectInverseOf(r)`.
- `BOTPROP r` marks an empty property. It has no `SUBPROP`, `DOMAIN` or
  `RANGE` rows: an empty property is below every property and has every class
  as domain and range, so these rows carry no information. (The class rows of
  an unsatisfiable class are not a fixed closure either: a route may print
  some of its `SUB` rows.)
- `DOMAIN r C` iff `O ⊨ ∃r.⊤ ⊑ C`, and `RANGE r C` iff `O ⊨ ∃r⁻.⊤ ⊑ C`, for a
  named class `C` other than `owl:Thing`. Every entailed domain is listed, not
  only the most specific ones. A class equivalent to `owl:Thing` is listed.
- An inconsistent ontology is reported as `CONSISTENT 0` with no property rows.
- `DROPPED N` with `N > 0` means that neither the taxonomy nor the property rows
  are complete.

The named object properties are those that occur in object property position
anywhere in the source: declarations, class expressions, property axioms and
characteristics, assertions, `HasKey` and DL-safe rule atoms. Data properties
are not reported.

## Mechanism

The property hierarchy uses the same exact reduction to classification as
realization. Let `B` be a fresh class. For each named object property `r`
KM adds a fresh class `P_r ≡ ∃r.B`, and, depending on the source, also

- `P_{r⁻} ≡ ∃r⁻.B` for each `r`, unless the source is *inverse-free* (below);
- `P_⊤ ≡ ∃owl:topObjectProperty.B`, only when the source uses
  `owl:topObjectProperty` (other than as the super-property of a
  `SubObjectPropertyOf` tautology) or an object nominal (`ObjectOneOf`,
  `ObjectHasValue`).

It classifies the extended ontology once with the ordinary production
pipeline. The extension only defines fresh names, so it is conservative.

Because `B` is fresh, a model of `O` can interpret it as any set. If
`(x, y) ∈ e \ f` in a model of `O`, interpreting `B` as `{y}` puts `x` in
`P_e` and not in `P_f`. Conversely, `x ∈ P_e \ P_f` gives some `y ∈ B` with
`(x, y) ∈ e \ f`. So, for a consistent `O`:

- `O ⊨ e ⊑ f` iff `P_e ⊑ P_f`;
- `e` is empty iff `P_e` is unsatisfiable;
- `owl:topObjectProperty ⊑ f` iff `P_⊤ ⊑ P_f`;
- `C` is a domain of `r` iff `P_r ⊑ C`, and a range iff `P_{r⁻} ⊑ C`, for a
  source class `C` (interpret `B` as the whole domain).

Without `owl:topObjectProperty` and object nominals, every model of `O` has
a disjoint union with an individual-free copy of itself that is again a
model, and no named property relates the two parts: no named property is
universal, so `P_⊤` is not needed.

A source is inverse-free when it has no `ObjectInverseOf`,
`InverseObjectProperties`, symmetric, inverse functional or reflexive
property axiom, no `ObjectHasSelf`, no object nominal, no
`owl:topObjectProperty` beyond that tautology, and no `DLSafeRule` or
`HasKey` (the test is syntactic; any doubt counts as not inverse-free).
Unravel a model of such a source into a forest from the named individuals:
an `r`-edge to a child has no edge back, so a nonempty named `r` is below no
inverse `s⁻`, and there are no inverse rows. The ranges then come from a
second classification: after the first run has found the empty properties,
KM adds two fresh named individuals and the assertion `r(a_r, b_r)` for every
nonempty named `r`, with a realization probe `{b_r}`, and reads the named
types of `b_r`: `O ⊨ ∃r⁻.⊤ ⊑ C` iff `O ∪ {r(a_r, b_r)} ⊨ C(b_r)`. All pairs go
into one ontology; the disjoint union of models argument shows that they do
not interact (keys and rules, whose named-individual semantics would reach
the fresh individuals, are excluded by the inverse-free test). The fresh
individuals never appear in the output, also with `--realize`. A source that
is consistent while this extension is not would be a bug in the reduction;
KM then refuses the answer.

KM removes every row that mentions a probe class, so the taxonomy rows equal
the plain classification. It refuses an answer in which `P_r` and `P_{r⁻}`
disagree on emptiness, since they are empty together in every model.

As for realization, the property hierarchy is answered only under the
automatic route policy: the extension can contain inverse roles and the
universal role, which several manually forced routes do not handle exactly.
A forced route exits with code 3; `KM_REALIZE_ANY_ROUTE=1` lifts the check
for route diagnostics.

## Cost

Measured on 32 ORE 2015 inputs with role axioms (one thread, development
workstation, `KM_THREADS=1`): plain classification, the first
`--properties` (v1.7.0 development, with `Dom_r`, `Ran_r`, inverse probes
and `P_⊤` for every input) and the current one. "Shape" is the source test
above; on inverse-free inputs the target was at most three times the plain
time plus one second, and every one meets it.

| Input | Shape | Plain s | MB | Old `--properties` s | MB | New `--properties` s | MB | Target |
|---|---|---:|---:|---:|---:|---:|---:|---|
| ore_ont_394 | general | 0.06 | 13 | 0.41 | 31 | 0.26 | 20 | n/a |
| ore_ont_3349 | inverse-free | 0.02 | 11 | 1.16 | 33 | 0.19 | 16 | met |
| ore_ont_9402 | inverse-free | 0.06 | 14 | 1.33 | 34 | 0.42 | 25 | met |
| ore_ont_13113 | general | 0.24 | 20 | 2.49 | 69 | 2.13 | 42 | n/a |
| ore_ont_16821 | inverse-free | 0.03 | 10 | 0.19 | 17 | 0.10 | 15 | met |
| ore_ont_3685 | general | 0.46 | 22 | 0.71 | 31 | 0.50 | 23 | n/a |
| ore_ont_2488 | general | 0.08 | 14 | 0.84 | 33 | 0.79 | 25 | n/a |
| ore_ont_316 | inverse-free | 0.05 | 14 | 1.47 | 64 | 0.39 | 23 | met |
| ore_ont_11416 | general | 0.09 | 16 | 4.33 | 94 | 0.19 | 23 | n/a |
| ore_ont_13545 | general | 0.65 | 38 | 2.35 | 47 | 2.30 | 42 | n/a |
| ore_ont_10702 | general | 0.59 | 41 | 3.02 | 62 | 2.50 | 57 | n/a |
| ore_ont_6437 | general | 0.30 | 29 | 1.05 | 59 | 0.35 | 36 | n/a |
| ore_ont_3806 | general | 0.04 | 12 | 0.08 | 14 | 0.06 | 12 | n/a |
| ore_ont_8951 | general | 0.03 | 12 | 0.39 | 25 | 0.07 | 14 | n/a |
| ore_ont_13805 | general | 0.10 | 19 | 0.36 | 30 | 0.42 | 27 | n/a |
| ore_ont_9557 | general | 0.80 | 15 | 0.81 | 36 | 0.68 | 26 | n/a |
| ore_ont_5292 | general | 0.02 | 10 | 0.14 | 17 | 0.04 | 12 | n/a |
| ore_ont_2652 | general | 0.32 | 290 | 0.61 | 52 | 0.36 | 330 | n/a |
| ore_ont_10388 | general | 0.03 | 11 | 0.40 | 31 | 0.10 | 16 | n/a |
| ore_ont_13139 | general | 0.11 | 20 | 44.69 | 2268 | 0.24 | 111 | n/a |
| ore_ont_4668 | inverse-free | 0.05 | 12 | 0.11 | 14 | 0.09 | 14 | met |
| ore_ont_155 | general | 0.07 | 13 | 0.89 | 46 | 0.65 | 29 | n/a |
| ore_ont_4724 | inverse-free | 0.01 | 10 | 0.21 | 25 | 0.07 | 12 | met |
| ore_ont_7188 | general | 0.15 | 27 | 122.31 | 5605 | 8.23 | 2923 | n/a |
| ore_ont_9690 | inverse-free | 0.08 | 14 | 1.48 | 30 | 0.17 | 16 | met |
| ore_ont_13078 | general | 0.12 | 27 | 123.58 | 5922 | 4.59 | 2954 | n/a |
| ore_ont_14588 | inverse-free | 0.14 | 24 | 5.25 | 180 | 0.30 | 41 | met |
| ore_ont_10009 | inverse-free | 0.36 | 54 | 77.48 | 344 | 0.94 | 104 | met |
| ore_ont_7988 | inverse-free | 0.21 | 27 | 1.22 | 37 | 0.52 | 32 | met |
| ore_ont_16670 | inverse-free | 0.19 | 20 | 76.23 | 332 | 0.61 | 56 | met |
| ore_ont_2749 | inverse-free | 0.30 | 55 | 0.43 | 58 | 0.27 | 57 | met |
| ore_ont_9800 | inverse-free | 2.64 | 226 | over 300 | 710 | 5.86 | 237 | met |

Where the time goes on the slowest rows: ore_ont_9800 (inverse-free, 42
properties) classifies twice, once with the probes and once with 42 asserted
pairs; ore_ont_7188 and ore_ont_13078 (reflexive properties, so not
inverse-free) first fail the positive-EL ABox certificate on the inverse
probes and are then classified on the general route (see `realize.rs`,
`classify_probe_source`); the old reduction needed over 120 s and 5.6 GB
there.

## Known limitations

- None known for `owl:Nothing` domains and ranges or `owl:topObjectProperty`:
  every position of `owl:topObjectProperty` is encoded exactly
  (`frontend/universal_role.rs`) or is not OWL 2 DL and fails the
  conformance check.
- ore_ont_9240 (symmetric, inverse and reflexive properties) takes 50 s and
  7 GB for plain classification and does not finish `--properties` in 300 s
  (the old reduction also gave no answer: exit 3 after 255 s). HermiT
  answers in 16 s.

## Data properties (W6, 2026-11-15)

With `--properties` km also reports, after the object property rows:

| Row | Meaning |
|---|---|
| `SUBDATAPROP<TAB>p<TAB>q` | `O ⊨ p ⊑ q`, `p ≠ q`, `p` not empty |
| `TOPDATAPROP<TAB>p` | `O ⊨ owl:topDataProperty ⊑ p` (never in OWL 2 DL, which admits `owl:topDataProperty` only as a super-property) |
| `BOTDATAPROP<TAB>p` | `p` is empty; it has no other rows |
| `DATADOMAIN<TAB>p<TAB>C` | `O ⊨ DataPropertyDomain(p C)`, `C` named, not `owl:Thing` |
| `DISJOINTDATAPROP<TAB>p<TAB>q` | `O ⊨ DisjointDataProperties(p q)`, `p ≠ q`, both not empty, both orders |
| `NODATADISJOINT` | more than 64 data properties: the disjointness rows were not computed |

JSON keys: `subdataproperties`, `topdataproperties`, `bottomdataproperties`,
`datadomains`, `disjointdataproperties`. The data properties are those in
data property position anywhere in the source, other than the top and bottom
data properties.

Mechanism (`orchestrate::data_properties`): one classification of the source
extended with `W_p ≡ ∃p.{v}` for every data property `p`, where `v` is a
literal of a fresh datatype read under `--unknown-datatypes=free` (an opaque
value about which the source says nothing), `X_pq ≡ W_p ⊓ W_q` for each pair,
and `T ≡ owl:Thing`. Since `v` can be interpreted as any data value,
`O ⊨ p ⊑ q` iff `W_p ⊑ W_q`, `p` is empty iff `W_p` is unsatisfiable,
`W_p ⊑ C` iff `C` is a domain of `p`, and `p`, `q` are disjoint iff `X_pq` is
unsatisfiable. The data ranges of data properties are not reported (HermiT's
`OWLReasoner` has no such query).
