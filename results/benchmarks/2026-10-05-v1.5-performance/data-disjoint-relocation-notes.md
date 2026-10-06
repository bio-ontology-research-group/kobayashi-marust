# Preserve disjoint constraints through equality relocation

The first relocation implementation loses an outgoing negative role constraint
when its source node is merged. A focused regression reproduces that failure;
three other tests, including incoming-edge branch rollback, pass before the fix.
The earlier six CLI controls did not cover this topology.

The shadow repair enumerates the union of incoming connection IDs, outgoing
positive successors, and outgoing negative successors. The directed conflict
check tests all original positive endpoint pairs whose images coincide with
an incident negative edge after equality. Relocation also removes the old
outgoing connection indexes after installing the corresponding survivor edges.
The default production admission and runtime are unchanged.

After the fix, all five focused tests pass. One exhaustively checks the 72
initially consistent positive/negative edge arrangements on three nodes,
including self-loops, incoming/outgoing orientations, and edges between the
merging nodes. A second checks both conflict dependencies. The other tests
cover separate roots, outgoing negative relocation, and incoming positive/
negative rollback through a real branch epoch. All 41 nearby disjointness
tests pass. The test logs and hashes are retained in the validation receipt.

`DatatypeRoleDisjointness.relocation_conflict_iff` proves the exact edge-image
conflict criterion, without axioms. It is supporting evidence, not a proof
that the runtime enumerates every edge or realizes the concrete value domain.
Full runtime proof binding and datatype realization remain prerequisites for
production admission. The complete shadow patch includes the earlier decimal
and datatype-padding experiments; it is not a standalone production patch.

A first test-file append used an incorrect relative path and failed. Its build
therefore ran only the two existing tests. The corrected before-fix build ran
four tests and reproduced the outgoing-edge failure; only that latter run is
used as regression evidence. The five-test after-fix result is separate.

The rebuilt CLI passes all six semantic controls. In the bounded paired
diagnostic, 14379 times out at 15 seconds with the experiment disabled and
finishes in 1.074 seconds with it enabled. Its full result agrees with pinned
Konclude, HermiT, and Openllet answers. This remains a local diagnostic, not
a full-corpus coverage gain or release performance measurement.
