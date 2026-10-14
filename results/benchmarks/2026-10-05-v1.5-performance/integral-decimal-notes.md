# Integral decimal and data-domain embedding diagnostic

The isolated candidate at base commit `2032f765` admits decimal literals whose
exact values are representable integers. All 73 datatype tests pass. The patch,
source manifest, immutable binary inventory, and submission receipt accompany
this record; the production worktree has not adopted the patch.

IBEX job 53328160 completed both original-input cases under the unchanged
240-second, 20-GiB, one-CPU limits. Ontology 13799 completed in 0.161 seconds
and agreed with Konclude, HermiT, Openllet, and JFact. Ontology 12566 still
failed at the internal worker deadline after 235.182 seconds. Decimal admission
alone therefore adds no verified solved ontology.

The worker trace identifies the next guard: a non-datatype source axiom fails
on a blank data node. Read-only evaluation identifies source axiom 247,
`Tangible-Thing = not Intangible-Thing`. Setting every ordinary class false
does not satisfy that equivalence. Removing the guard would be unjustified.

The generic `probe_data_padding_type.py` searches single-class seeds, closes
atomic superclass implications, and independently evaluates every source GCI,
including datatype-bearing axioms, on an edgeless node. It finds a positive
class assignment satisfying all 311 source axioms. This establishes feasibility
of a stronger padding witness only. Model transport in both directions, query
preservation, ABox/RBox compatibility, and executable certificate binding remain
unproved. The script does not change production admission or benchmark counts.

Separately, all four production Lean gates for the already-landed
local-universal fix passed without `sorryAx`. The certification receipt binds
624 source files; their hashes and gate log hashes were rechecked after all
gates completed. That certification does not cover this isolated decimal patch
or a future padding-witness implementation.
