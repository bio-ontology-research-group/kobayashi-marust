# ORE 7499 positive-ABox component certificate

This capsule records a rejected attempt to make the exact explicit
`certified_card_proxy_abox` taxonomy route safe for automatic classification.
No result here changes the audited v16 default total of 588 operational and
586 exact ontologies.

## Source-bound IBEX gate

Commit `616521a` added an exact positive-ABox component consistency attempt.
The source archive SHA-256 was
`09e1810d492de1bada92dd6b8c14c4ef68c9b82b628b05c821ec504ed3441b1d` and
the IBEX-built binary SHA-256 was
`1dda6ea210ee1a876168048dc504d7b07b3512d4b9ededaa3a7bdca6f42e96c8`.
Build job `49694895` succeeded under
`/ibex/scratch/hohndor/km/7499-component-abox-v1`.

Gate job `49694931` is invalid: the job omitted `tree_watchdog.py` and all
tasks failed immediately. The corrected gate was job `49694939`. Controls
10702, 15846, 4755, and 6999 matched their full-IRI references. Ontology 7499
timed out at 240.0215 seconds after reaching 18,844.97 MiB and produced no
signature. The checkpoint is
`/ibex/scratch/hohndor/km/7499-component-abox-v1/results/ore_ont_7499.owl.ibex.checkpoint.json`.

The Slurm files in this directory preserve the source-bound build and focused
gate definitions. They are evidence, not current production launchers.

## Rejected local follow-ups

Several opt-in compositions were measured with the release binary under the
production worker watchdog:

- Consistency-only component completion followed by the existing cardinality
  taxonomy still crossed the 18 GiB worker threshold at about 109 seconds.
- Alpha-equivalent singleton/two-node component deduplication reduced 75 raw
  components to 21 shapes, but RSS still crossed the threshold at about 113
  seconds.
- Dropping cross-probe caches and calling `malloc_trim` did not change the RSS
  trajectory.
- Rebuilding and dropping a complete bridge environment per component did not
  help: one isolated component alone reached about 14 GiB by 82 seconds and was
  still growing. This rules out cumulative reset leakage as the primary cause.

All composition, deduplication, cache-isolation, and per-component environment
experiments were removed after measurement. Commit `fed6c61` keeps the
component bridge opt-in and restores 7499's default source route to `nominals`.
The 24 routing-policy tests pass, and no full IBEX sweep was launched from a
candidate that failed its focused local resource gate.

## Remaining viable direction

The explicit TBox-only cardinality route remains exact for 7499 (36,145
subsumptions and no unsatisfiable classes), but automatic use still requires a
cheap proof that the positive ABox is consistent. The asserted ABox has 149
class assertions and 74 assertions of `BFO_0000062`, with no negative role
assertions or inequalities. Every role-assertion endpoint's asserted class is
already subsumed by the role's required `BFO_0000003` domain/range in the exact
cardinality taxonomy; the one class assertion that is not is an isolated
individual. A future route may use a fail-closed positive-role constraint
certificate plus the exact TBox taxonomy. It must account for the complete role
closure, universal restrictions, disjointness, number restrictions,
irreflexivity/asymmetry, and source constructs before it can certify
consistency. Corpus agreement alone is not sufficient.
