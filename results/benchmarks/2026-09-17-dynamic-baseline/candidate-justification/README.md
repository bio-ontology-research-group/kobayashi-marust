# Experimental ABox candidate explanation controls

Candidate source archive:
`9a77671d75ed4d72e5cf4786610da1daeedb4054058e9b7c13177d10e691204d`.
IBEX binary:
`b51533172b0dfe0def6fb10a8ae15146d5ae95462002cd1ac1289d11cbbd4ac9`.
Build51982442, control array51982551, independent audit51982553.

All30 scheduled controls pass: native/common KM, bounds1/10/100, unsatisfiable
class, inconsistent ontology, two independent subclass paths, irrelevant noise,
and a non-entailment query. HermiT independently checks source membership,
entailment and every single-axiom deletion of each returned support. Known
support-family counts and negative source entailment are also checked. The local
recomputed audit agrees with the remote audit.

The six inconsistency attempts previously returned no supports with v1.4.0.
This candidate returns the unique three-axiom support in every attempt. The
other24 controls pass without a regression. Each task independently checked the
archive bytes against the expected SHA and matched binary bytes to the build
receipt before execution.

This is experimental validation before Lean certification, not a final release
or repeated performance benchmark. Raw outputs remain under
`/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/justification-abox-candidate-v1/`;
a local copy is in the task worktree's `.work/justification-evidence/` directory.
