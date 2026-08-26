# v26 mixed sparse-Horn route

Source capsule SHA-256: `7210c9d7cd372719a668bf95e5a5064fa25782baab48449a4fadc63298e83315`

Binary SHA-256: `163ea9899d9641b362d2e18fade1a73eb98f8e1314a26245a3d2b26f1436b9e0`

IBEX root: `/ibex/scratch/hohndor/km/v26-mixed-sparse-20260826`

The route extends the fail-closed sparse-Horn source calculus with exact
named/intersection equivalences, named union definitions, and redundantly
witnessed finite nominals. Unsupported syntax still declines before an answer
is published.

The alternating three-repetition ORE15803 comparison (job `50879173`) was
byte-identical to v20 in every repetition. Median wall time fell from 19.73 s
to 1.41 s and peak RSS from about 1.285 GiB to about 109 MiB. The complete
592-ontology sweep was job `50879778`. It produced 469 complete terminal,
profile, and checkpoint triples, with zero behavioral differences from v20 in
the shared-row audit. Its pending 123-task remainder was cancelled after v27
superseded the route and needed the same batch resources. The retained partial
evidence exposed unprofitable mixed routing on ORE11460 and ORE4604; v27 adds
the measured source-size profitability guard. An initial submission
(`50879324`) failed before running any ontology because the new sweep root
lacked the harness ontology list. The replacement wrapper checks all seven
required harness files, the 592-line list, Python imports, binary hash, and CPU
model before computation; task 0 then completed normally.
