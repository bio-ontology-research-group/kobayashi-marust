# Isolate disjoint-role support from other datatype experiments

The no-padding diagnostic first showed that 14379 does not require the
experimental padding assignment. A separate checkout at f5a1a01d then received
only the role-disjointness recognition/encoding, merge conflict/relocation
changes, and their tests. Decimal parsing and padding source remain identical
to that base commit. The earlier combined checkout is preserved.

The new isolated CLI passes all six semantic controls and all 64 undirected
four-role Boolean disjointness graphs. The graph oracle independently searches
every Boolean assignment: existential witnesses with pairwise-disjoint value
sets exist exactly when the role graph has a proper two-coloring. A Lean
theorem establishes this equivalence using Classical.choice. Failed attempts
would remain in the report; all 64 complete correctly with zero dropped axioms.
All 41 disjointness-related Rust tests also pass.

14379 times out at the local 15-second diagnostic bound with the flag off and
completes in 1.079 seconds with it on. Its full answer agrees with the pinned
Konclude, HermiT and Openllet answers. The source manifest and binary hash bind
this observation to the isolated candidate, not the previous combined shadow.

HypertableauRoleDisjointness.lean proves the exact same-endpoint, distinct-variable,
empty-head clause equivalent to role disjointness. It also proves that a role
disjoint with itself is empty and that inverse-role disjointness is equivalent
to forward-role disjointness. The first proof uses propext; the others are
axiom-free. No proof uses sorryAx. These support the bridge representation;
they do not replace concrete datatype model transport, runtime refinement,
or the exact-source production certification gates. Production remains
unchanged and no full-corpus coverage gain is claimed.
