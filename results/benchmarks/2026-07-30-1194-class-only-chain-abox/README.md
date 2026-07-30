# ORE 1194 class-only chain-ABox bridge candidate

The accepted 6999-integrated production sweep reaches `ore_ont_1194.owl` via
the nominal CB fallback and fails because the fixed `u32` composite-term layout
cannot represent its simultaneous 124,950 Skolem functions and 18,055
individuals. The source profile has 221,086 class assertions and no object
property assertions.

This candidate broadens only the source-side typed-ABox bridge gate. A TBox may
contain complex role chains when its ABox has no asserted role edges. With no
ABox edge, no chain automaton can extend the native ABox. The converted-input
bridge remains authoritative: it checks the complete normalized clauses, RBox,
and typed ABox and either publishes an exact classification or defers to the
unchanged nominal CB fallback.

Source commit: `a513828a9c9c2b252058dc2d0e12615538b574d6`.

Source archive SHA-256:
`3958bb7660abd7c090263b5dad2a2885664cc810e6b4e47f7232997bf98d1418`.

Local validation:

- the focused routing test accepts class-only ABoxes with chains and rejects
  the same RBox when an object-property assertion is present;
- the complete serial release suite passes: 1,797 library tests, eight ignored,
  and all integration tests, with zero failures.

IBEX build and exactness results are recorded after their jobs terminate.
