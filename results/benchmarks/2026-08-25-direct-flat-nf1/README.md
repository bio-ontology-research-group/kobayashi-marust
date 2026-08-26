# Direct flat-NF1 source classifier

This candidate targets the large, generated named-class hierarchy represented
by ORE10689. The general frontend takes about 14 seconds and materializes about
one million normalized clauses before ELC computes the same graph closure.

The candidate scans a fail-closed Functional Syntax subset directly. It accepts
only prefixes, an ontology header, named-class declarations, named
`SubClassOf` edges, and the final ontology delimiter. It declines before
publication on every other axiom, semantic top or bottom endpoint,
non-trivial cycle, malformed line, explicit non-functional input format, or
trailing content. The established complete frontend remains the fallback.

The route computes the DAG's reverse-topological transitive closure and emits
the grouped JSON taxonomy without constructing normalized clauses or expanded
string pairs. `lean/ContextCalculus/ELFlatNF1.lean` proves:

- every non-top ELC completion fact in this fragment is graph reachability;
- every graph-reachable pair is an ELC completion fact; and
- the accepted fragment has a model, justifying the positive consistency
  verdict.

Both exported theorems compile without `sorryAx`; `#print axioms` reports only
`propext` and `Quot.sound`.

IBEX root: `/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825`.
Final focused build job `50841713` passed all four route tests and produced
binary `395785d08a622bbe9f5179d770988da368963270b63cce79bc1e9d5a444e0920`.
The original exclusive Gold-node smoke `50841793` was cancelled after its
candidate arm produced no output for more than four minutes and reached 13.7
GiB despite an earlier 4.04-second, 400-MiB run of the same exploratory binary.
Its directory contained stale records from prior jobs, so it is not publication
evidence. The isolated manifest-backed build and fresh dependent gates below
replace it.
Hardware-independent functional job `50841864` passed on ORE10689: production
route trace `elc` (the candidate predated the final trace label), exact retained signature
`be6be6663ffd9721606bf3cb61308789c55c28ffbe8d4ba2d85d0ee60b7fcc0f`,
4.1298 seconds, and 399.95 MiB process-tree peak RSS. The prior direct-compact
candidate took 20.60 seconds and about 1.77 GiB on the same AMD node class.
Exclusive AMD job `50842277` independently reproduced the result against the
v1.0.0 baseline: 4.0442 seconds and 399.98 MiB versus 22.5879 seconds and
1,813.26 MiB, with the same full-IRI signature and distinct binary hashes.

Source-shape job `50841874` identified seven large pure flat hierarchies and
four additional large named-class hierarchies with only a disconnected role
box. The latter extension is under separate build and correctness validation.
The exclusive Gold comparison remains pending, so no release claim is based on
this candidate yet.

Additional hardware-independent exact-signature gates produced:

| ontology | wall s | peak MiB | result |
|---:|---:|---:|---|
| 8486 | 4.7559 | 349.59 | exact |
| 9674 | 4.4472 | 401.85 | exact |
| 10689 | 4.1298 | 399.95 | exact |
| 14459 | 3.7917 | 333.05 | exact |
| 16008 | 3.3166 | 294.63 | exact |

ORE868 and ORE15059 remained on the ordinary ELC path at 31.9694 and 25.1529
seconds because their apparent line-level hierarchy shape contains constructs
outside the strict scanner contract. They are not counted as fast-path gains.

The production candidate now performs an allocation-free lexical screen before
building its declaration table and graph. This matters for giant misses such
as ORE868, whose first unsupported axiom occurs after roughly 1.96 million flat
lines: the scanner now declines without retaining that million-node prefix.
Build job `50842878` passed all five scanner tests. Its installed executable is
byte-identical to the later bridge-exploration build because both exploratory
jobs shared a Cargo target; this is acceptable for functional testing because
the extra bridge setting is opt-in, but it is not release provenance. A final
candidate must be rebuilt from one source tree in an isolated target directory.
Exclusive sequential functional array `50843330` then validated both sides of
the screen contract with that binary. ORE10689 selected `flat_nf1`, matched the
retained full-IRI signature, and completed in 4.3734 seconds at 400.71 MiB.
ORE868 declined to the established `elc` fallback, matched the same retained
signature, and completed in 26.5957 seconds at 1,813.29 MiB. Both records are
terminal and checkpointed; no partially allocated direct graph survived the
ORE868 miss.

The source audit showed that ORE868 differs from the flat fragment only by two
`A ⊓ B ⊑ owl:Nothing` axioms. Theorems
`flatNF1Disjoint_sub_iff_flatReach` and `flatNF1Disjoint_has_model` prove the
taxonomy and consistency claims for inert instances without `sorryAx`.
Nevertheless, focused job `50842516` reached 13.7 GiB while constructing the
explicit closure, versus about 1.9 GiB on the established ELC route. The job
was cancelled by ID before publication and the activation was removed. ORE868
therefore continues to use ELC; a semantically valid route that regresses
memory is not a v1.1 candidate.

## Existential-leaf projection

Source-shape job `50843557` exposed a second exact fragment hidden by the
generic frontend. ORE15059 and ORE16744 contain only axioms of the form
`A ⊑ ∃r.B`; ORE8737 has the same class shape plus eight declared roles and
a small positive RBox. Their retained results are all consistent, contain zero
named subsumptions and zero unsatisfiable classes, and share full-IRI signature
`25a9dfe36078…`. ORE14042 adds 11,232 named NF1 edges to 641,123 existential
leaves and is also eligible for graph projection. ORE1559 is deliberately
ineligible because it contains two bottom-producing conjunctions.

Declaration-order audit `50843968` described the initial targets. Declarations
are semantically inert in OWL, so the scanner now treats their order,
duplication, and omission as administrative variation while collecting the
complete class signature from declarations and logical uses. It accepts only
full-IRI NF1 edges,
`A ⊑ ∃r.B` leaves, and simple positive role inclusions, inverses,
equivalences, symmetry, transitivity, and binary role chains. A role inclusion
into `owl:topObjectProperty` is recognized as a tautology. It still declines
domains, ranges, existential antecedents, class top/bottom endpoints, cycles,
imports, annotations, and malformed input.

`flatNF1Leaf_sub_iff_flatReach` instantiates the existing EL edge-safety proof:
NF3 leaves and role-only clauses cannot feed a named conclusion without NF4 or
NF5, so the complete named taxonomy is exactly NF1 graph reachability.
`flatNF1Leaf_has_model` proves the accepted fragment consistent. Both compile
without `sorryAx`; the taxonomy theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`, and the model theorem only `propext` and
`Quot.sound`. Seven focused release-mode Rust tests pass.

Isolated source build `50844797` completed on `cn506-11-l`. All eight focused
release-mode tests passed, the source-manifest SHA-256 is
`b9f12dfec35270a6e3dd28b56f606df2dd25ca58dc294c9811e3da240dcdf1dd`,
and the installed binary SHA-256 is
`515a3201e7bf2199e39df24b73931d2025c075c1b1677f8776d88e341b488ecf`.
The unconstrained exact-signature array `50844954` completed all eleven of its
tasks with checkpointed `status=ok`, retained-gold `verdict=match`, and the
expected route. ORE8737, ORE15059, ORE16744, ORE14042, ORE9794, ORE2243,
ORE10445, ORE11389, and ORE14607 selected `flat_nf1`; ORE1559 and ORE868
declined and completed through ELC. The nine direct results consumed 20.615
summed wall-seconds and 265.24 MiB of summed process-tree peak RSS. The two
fallback controls also retained their exact signatures. Gold-6248 arrays
`50844798`, `50844799`, and `50844800` remain queued for publication-quality
performance measurements; their semantic result is already independently
established by `50844954`. Superseded queued jobs
`50843989`, `50843990`, `50844243`, `50844244`, `50844288`, `50844493`,
`50844566`–`50844569`, `50844606`–`50844609`, and `50844730`–`50844733`
were cancelled before producing a binary. Job `50844730` exposed two omitted
repository-level `include_str!` fixtures; the final manifest covers both the
engine and those regression inputs. The final build is unconstrained because compilation is
hardware-independent; every performance gate remains Gold-6248 constrained.
It records a complete source-file manifest before compilation.

ORE9794 shape audit `50844262` found another pure existential-leaf source:
678,470 `A ⊑ ∃r.B` axioms over 37,373 classes and three roles, with no other
logical form. Job `50844954_4` selected the direct route and matched the
retained full-IRI signature in 1.1618 seconds with 12.72 MiB peak RSS.
Gold-6248 job `50844799` remains queued for the hardware-controlled performance
measurement.

All-empty source audit `50844304` found four further sources above the direct
route's size threshold with the same strict logical shape: ORE2243, ORE10445,
ORE11389, and ORE14607. Array `50844954` proved the direct route and exact
signature for all four. Dependent array `50844800` remains queued only for the
Gold-6248-controlled timing and memory record.
