# Automatic bounded data-ABox source scheduling

Five nominal-route timeout cases admit the existing exact ground-source compiler:
ORE 3843, 4719, 586, 7342 and 7828. The compiler expresses data assertions through
source-level singleton-value class assertions, retains the other source axioms,
and requires complete native bridge admission before publishing an answer.
Previously the scheduling hint required a functional data property together with
an inverse-functional object property, except for its separate numeric path.
That restriction excluded these accepted inputs.

The general data-ABox hint now admits up to 1,024 source classes, 512 source
individuals, 4,000 logical axioms and 512 positive data assertions, with no imports.
The existing native and numeric bounds remain unchanged. These are scheduling
cost limits, not semantic admission. The compiler and bridge retain their exact
coverage and datatype checks; refusal restores the ordinary fallback. The
original narrower projection remains preferred for its existing eligible cases.

All five automatic-route outputs agree in consistency and full-IRI taxonomy with
Konclude, HermiT, Openllet and JFact. Local diagnostic times were 0.115, 0.115,
3.977, 0.165 and 1.671 seconds respectively, with a one-second optional saturation
cap and the candidate's DDB/native/cache flags. These are not full-corpus release
metrics. Four scheduling tests and four existing compiler tests pass.

ORE 1342 remains outside the literal compiler's exact supported values. ORE 14379
compiles, but native datatype admission defers on a non-atomic datatype
equivalence. Neither refusal was bypassed. Both remain in the full benchmark.

The source is pinned in `data-source-scheduling-source-manifest.json`. Final-source
certification and the standard optimized build are tracked separately in
`data-source-scheduling-work-state.json`. Job 53306225 tests the preceding frozen
successor-deadline artifact, not this later routing change.
