# Explicit-equivalence CB query collapse

Revision `3edebbf` classifies one representative for named concepts connected
by direct opposite unit implications and restores every non-reflexive output
row afterward. This is an exact query-scheduling optimization. It does not
change the CB calculus.

Local validation:

- focused mutual-equivalence and one-way-rejection tests pass;
- the complete serial release library suite passes: 1,815 passed, zero failed,
  eight ignored;
- the frozen ORE 1194 clause payload contains 3,426 eligible groups and 5,204
  removable roots out of 70,231.

`ibex_build.sbatch` builds the source archive on an IBEX compute node.
`ibex_gate.sbatch` runs the ordinary automatic route on 1194 plus exact-gold
controls. ORE 1194 has no authoritative full gold, so only a complete,
parseable result can establish operational closure there; every control must
match its retained Konclude signature exactly.

Source archive SHA-256:
`cff55e2a8d1df8792e2d9a1887ab76321afaea1ff7f7326bdc571477f08206ce`.

IBEX native build job `49678209` and dependent five-case gate `49678210`
remain pending.
