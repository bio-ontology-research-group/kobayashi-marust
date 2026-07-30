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

IBEX build job `49642445` completed. Its binary SHA-256 was
`8a8a09cbb962108ad56df8524c14ed03f295f38164ff3ed25f114a10f334bcde`.
Dependent exactness array `49642446` rejected the candidate:

- `1194` still reached the nominal CB fallback and panicked after 200.96 s at
  9,404.93 MB with the same fixed-layout error:
  `f(o) term space exhausted (f id 124950, individual 18055)`.
- Controls `6999`, `10621`, and `15672` matched Konclude exactly.
- Control `15846` did not publish a terminal result before its array task
  failed, so the gate is not accepted independently of the `1194` failure.

This establishes that source-side admission alone is insufficient. The
converted-input bridge still defers on `1194`; the unchanged fallback then
reproduces the composite-term overflow. Do not count this candidate as a
recovered ontology.
