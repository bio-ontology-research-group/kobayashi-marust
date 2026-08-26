# Empty-taxonomy source projection audit

The immutable v0.2.36 sweep has 83 exact, consistent classifications with zero
named subsumptions and zero unsatisfiable classes. Together they consume
437.5978 seconds. This audit examines the remaining slow members after the
proved existential-leaf and positive-ABox projections, looking for a general
source fragment whose empty taxonomy and consistency can be proved without
running full completion.

No source shape is accepted from the observed answer alone. A route requires a
syntactic fail-closed recognizer, an independent semantic theorem, exact
full-IRI gates, and a complete-corpus regression sweep.

Top-level source audit `50844190` completed successfully. Ten of the eleven
targets are one generated annotation family: they contain only declarations,
subclass axioms, and positive complex class assertions. Their sources range
from 21.8 to 101.5 MB. These forms make them candidates for the independent
positive-ABox separation theorem, but a top-level lexical audit does not prove
that the fail-closed profile accepts each complete source. Exact differential
array `50844429` tests all ten and records the selected route.

ORE9794 is the exception: a 127.0-MB TBox with 37,376 declarations, 678,470
subclass axioms, and no ABox. Follow-up shape job `50844262` confirms all
678,470 axioms are `A ⊑ ∃r.B`, with 37,373 class declarations and three
object-property declarations before the first axiom. It therefore satisfies
the independently proved existential-leaf source contract. Exact-signature job
`50844288`, dependent on the frozen candidate build, is its publication gate.

Corpus audit `50844304` inspected all 83 exact, consistent empty-taxonomy
sources. Its deliberately narrower lexical recognizer accepted six inputs:
ORE2243, ORE9794, ORE10445, ORE11389, ORE14607, and ORE15059. This is an
opportunity inventory, not publication evidence: the executable recognizer and
its semantic contract remain authoritative, and each newly selected input
still requires an exact-signature gate.
