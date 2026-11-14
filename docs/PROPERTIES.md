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
as `km classify --lines` prints them, then the `TYPE` and `SAME` rows if
`--realize` is given (see `docs/REALIZATION.md`), then:

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
realization. Let `B` be a fresh class. For each named object property `r` and
its inverse, KM adds fresh classes

- `P_r ≡ ∃r.B` and `P_{r⁻} ≡ ∃r⁻.B`,
- `Dom_r ≡ ∃r.⊤` and `Ran_r ≡ ∃r⁻.⊤`,

and one more, `P_⊤ ≡ ∃owl:topObjectProperty.B`. It classifies the extended
ontology once with the ordinary production pipeline. The extension only
defines fresh names, so it is conservative.

Because `B` is fresh, a model of `O` can interpret it as any set. If
`(x, y) ∈ e \ f` in a model of `O`, interpreting `B` as `{y}` puts `x` in
`P_e` and not in `P_f`. Conversely, `x ∈ P_e \ P_f` gives some `y ∈ B` with
`(x, y) ∈ e \ f`. So, for a consistent `O`:

- `O ⊨ e ⊑ f` iff `P_e ⊑ P_f`;
- `e` is empty iff `P_e` is unsatisfiable;
- `owl:topObjectProperty ⊑ f` iff `P_⊤ ⊑ P_f`;
- `C` is a domain (range) of `r` iff `Dom_r ⊑ C` (`Ran_r ⊑ C`).

KM removes every row that mentions a probe class, so the taxonomy rows equal
the plain classification. It refuses an answer in which `P_r`, `P_{r⁻}`,
`Dom_r` and `Ran_r` disagree on emptiness, since they are empty together in
every model.

As for realization, the property hierarchy is answered only under the
automatic route policy: the extension contains inverse roles and the universal
role, which several manually forced routes do not handle exactly. A forced
route exits with code 3; `KM_REALIZE_ANY_ROUTE=1` lifts the check for route
diagnostics.

## Cost

The extension always contains inverse roles and the universal role (which KM
rewrites into a fresh nominal and an inverse role, `frontend/universal_role.rs`),
so an input that plain classification answers on a fast route can take a
general route with `--properties`. On 32 ORE 2015 inputs with role axioms
(one thread, development workstation), the median time rose from 0.10 s to
1.1 s and the median peak memory from 17 MB to 42 MB. 26 inputs stay under
7 s, but six inverse-free, nominal-free inputs became much slower (and a
seventh, ore_ont_14588, went from 0.2 s to 6.4 s):

| Input | Plain | `--properties` | without `P_⊤` | without inverse probes | without both |
|---|---:|---:|---:|---:|---:|
| ore_ont_9800 | 5.2 s | over 300 s | 3.6 s | over 300 s | 3.6 s |
| ore_ont_7188 | 0.2 s | 109 s, 5.6 GB | declined | 73 s | 0.2 s |
| ore_ont_13078 | 0.2 s | 125 s, 5.3 GB | declined | 49 s | 0.5 s |
| ore_ont_10009 | 0.5 s | 87 s | 54 s | 1.6 s | 0.5 s |
| ore_ont_16670 | 0.3 s | 77 s | 54 s | 1.1 s | 0.4 s |
| ore_ont_13139 | 0.2 s | 35 s, 2.2 GB | 0.6 s | 25 s | 0.4 s |
| ore_ont_14588 | 0.2 s | 6.4 s | 1.2 s | 0.7 s | 0.2 s |

The last three columns classify hand-built variants of the extension with the
v1.6.4 binary. "Declined" means KM exited with "positive EL ABox consistency
certificate declined". Both the universal-role probe and the inverse probes
cost time; removing either alone is not enough.

## Known limitations

- `ObjectPropertyDomain(r owl:Nothing)` and `ObjectPropertyRange(r owl:Nothing)`
  are dropped by the frontend without being counted in `DROPPED`, so `r` is not
  reported as `BOTPROP` (plain classification misses the same unsatisfiable
  classes). The ignored test `domain_or_range_nothing_empties_the_property`
  records it.
- When the source uses `owl:topObjectProperty` in a position that the
  universal-role rewrite does not cover (for example
  `SubObjectPropertyOf(owl:topObjectProperty r)`), KM treats it as an ordinary
  role, as plain classification does. The property rows are then sound but can
  be incomplete.
