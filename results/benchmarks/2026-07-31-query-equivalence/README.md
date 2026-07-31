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

IBEX native build job `49678209` completed from the checksum-verified archive
in 2 minutes 19 seconds. Candidate binary SHA-256:
`faf66b360d50591d0f9bb5f0cbd4203070d489a540fa05a7f3311b334cc75486`.
Dependent five-case gate `49678210` completed. The candidate activated on 1194
with 65,027 representatives, 5,204 aliases, and 3,426 groups, but did not close
the ontology: the worker deadline fired after 195.6359 seconds at 5,125.2 MiB.
The profile showed several individual root contexts at 400,000 work-off
iterations with 87,759 clauses still queued, so hard roots remain after the
global query reduction.

Exact controls 1034, 2237, and 6999 matched Konclude. The 15846 task timed out
at 240 seconds while sharing one AMD EPYC node with the profiled 1194 task.
That near-budget route previously required about 210 seconds on the standard
Gold 6248 nodes, so the contended, profiled AMD run does not isolate a candidate
regression. Isolated Gold 6248 control job `49678643` also timed out at
240.0386 seconds with profiling disabled. The completed v13 binary classified
the same ontology exactly in 204.1191 seconds at 19,030.98 MiB, so array
`49678899` now compares the candidate with `KM_NO_QUERY_EQUIV=1` against the
pre-collapse v14 binary on the same controlled hardware.
