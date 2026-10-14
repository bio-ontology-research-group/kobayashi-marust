# Isolated disjoint-role merge experiment

This candidate remains outside the production worktree and default admission.
It includes the earlier experimental decimal and datatype-padding changes.
The source patch and manifest record the exact modified files against the
shadow checkout's base commit; they are not a production certification receipt.

The missing directed merge check now compares negative role edges with positive
edges after endpoint identification and retains both conflict dependencies.
An experimental relocation path transfers positive and negative edges under
merged dependencies. Both paths require further relocation, rollback, and
proof validation before promotion.

The initial build failed because arena node handles do not implement Ord.
Sorting by their numeric arena indices fixed compilation. The new CLI passes
all six semantic controls: identical Boolean values on disjoint roles clash;
different values and values attached to distinct objects remain satisfiable;
two disjoint Boolean requirements are satisfiable, three are not; a shared
functional superproperty preserves its inconsistency check.

The first merge-control receipt incorrectly marked the three-value test failed
because its assertion expected an expanded IRI while explicit bridge output
uses the source spelling `:A`. The actual output already marked `:A`
unsatisfiable. Both the initial receipt and the corrected driver/receipt are
retained. This is a harness correction, not a reasoner change.

The bounded paired diagnostic on 14379 records a 15-second timeout with the
experimental flag off and a 1.080-second completion with it on. The latter's
full answer agrees with the pinned Konclude, HermiT, and Openllet answers.
This is not a release benchmark or an additional verified full-corpus solve.

Two new direct engine tests check retention of both positive/negative edge
dependencies and preservation of distinct source objects. Both tests pass in the release test build (two passed, zero failed).
Log: /tmp/agent/km-v150-diagnostics/data-disjoint-merge-tests.log.
