# Universal at-most restrictions in the native bridge

An unguarded equality-only role clause expresses an at-most restriction on
every object. The previous recognition path could partially absorb that
restriction behind an auxiliary role-domain trigger. The native ABox path
missed the restriction in a small inverse-functional example: r(a,c), r(b,c),
X(a), Y(b), and disjoint X/Y incorrectly returned consistent.

The bridge now installs unguarded equality-only recognition restrictions on
Top, using the same initialization mechanism as ordinary functionality.
Guarded recognition and disjunctive-head recognition retain their existing
encodings. This applies equally to qualified restrictions and incoming edges.
No source axiom is removed or weakened.

`HTUniversalAtMost.universal_pigeonhole_iff_atMost` proves the exact equivalence
between the equality-head pigeonhole condition and the universally required
qualified cardinality bound. The inverse theorem instantiates the converse
relation. Both use only Lean standard logical axioms.

The regression checks fresh completion, saturation/cache restoration and
classification, with both consistent and disjoint-owner cases and both native
cardinality schedules. The official HT gate includes it. The datatype fixture
matrix also exercises this path through automatic routing. The local debug
candidate passes all 60 route/process combinations; release and full corpus
validation remain pending.
