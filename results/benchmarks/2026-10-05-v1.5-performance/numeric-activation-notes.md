# Numeric incremental invalidation

Source invalidation now propagates numeric expression IDs directly, avoiding
construction of string-named JSON clauses and their immediate conversion back
to numeric IDs. The source-rule sets, union abstraction, symmetric difference,
query/global seeds, fixed-point rules and resource limits are unchanged. This
changes representation, not the inferred affected set or its locality argument.
The previous implementation remains a test-only equivalence oracle.
Source-locality reuse keeps its existing opt-in flag and certification guards.

Ten activation tests pass, including 384 finite-model revision transitions and
960 additional oracle comparisons spanning empty queries, global premises,
inverse-role expressions and 64-bit word boundaries. All 26 source-session
tests pass normally and with experimental module reuse enabled; all 14 typed
incremental tests pass. Every production Lean gate passes on the pinned
622-file source with no sorryAx.

Four real ORE9944 revision transitions have identical affected sets in eight
alternating-order repetitions each. Median invalidation time falls from
138–147 ms to 72–78 ms. The differential summary pins both inputs, the test
binary, source manifest and individual measurements. This is a local component
measurement, not an end-to-end performance claim.

Two end-to-end repetitions preserve exact fresh answers for all revisions in
both modes. Source-module reuse beats fresh reasoning on 4/8 attempts, all
small edits; full-input reuse wins on 0/8. The larger updates still take about
1.89–2.14 seconds against 1.63–1.67 seconds fresh. The v1.5.1 requirement remains
unmet; invalidation precision and repeated preparation remain open costs.

A separate read-only feasibility probe projects the remaining source theory
onto sound named-class Horn implications. On the 32-axiom deletion, these
implications support the entire previous row for 689 of the 2,180 invalidated
queries; all 689 rows also match fresh classification. The other 1,491 rows
remain unproved by this limited projection. No production row is reused on
this evidence. A production certificate would need explicit source coverage,
IRI binding and a checked derivation for every retained entailment, together
with the deletion-only monotonicity argument. See
`named-deletion-support-large.json` and `probe_named_deletion_support.py`.
