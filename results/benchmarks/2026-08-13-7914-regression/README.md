# ORE7914 independent atomic-ABox projection

Release v0.2.11 projects a large role-free ABox before native HT conversion
when every distinct individual has exactly one positive atomic assertion and
one distinct proxy. The ABox is checked from the completed TBox taxonomy; a
failed certificate or unsatisfiable asserted class defers to production.

IBEX inspection job 50432448 confirms that ORE7914 has 108,512 individuals,
one `Name` assertion and marker per individual, and no role assertions,
equality, inequality, negative roles, or unsupported content. Earlier
bridge-level experiments correctly showed no improvement because they ran only
after all proxy concepts had been allocated.

Source-bound candidate `78d5674` has binary SHA-256
`d19938110369da96167feddf2a257550bf80aca1793afd40154d18d303663f8e`.
Verification job 50433101 records an exact automatic result in 8.5783 seconds
at 1,514.75 MiB and an exact forced `ht_bridge` result in 7.2858 seconds at
910.61 MiB. Both signatures are
`5dfdc6168df75c9a1e2dd6485ea1d5b4bf9af6307ea210e9cd1634262e981923`.

Strict full sweep 50433149 produced 592 results, profiles, and checkpoints and
no temporary files. It records 591 successes and the unchanged ORE1194 error.
Comparison with v0.2.10 finds zero semantic, coverage, or route regressions.
Aggregate metrics are 4.5079-second mean wall, 0.2475-second median wall,
517.05-MiB mean peak RSS, and 42.27-MiB median peak RSS. The complete evidence
root is `ibex:/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813`.
