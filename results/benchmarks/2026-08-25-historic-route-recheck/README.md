# Historical exact-route recheck on v1.0.0

The July route ledger contains several exact alternatives that were materially
faster or lower-memory than the then-automatic route. This panel rechecks ten
of the largest opportunities against the immutable v1.0.0 binary on the same
Intel Xeon Gold 6248 class used by the release benchmark. Each task runs
automatic and forced-route arms in alternating order, checks the retained
Konclude signature, records process-tree peak RSS, and compares all semantic
metadata.

The tested alternatives are `elc_cert` for ORE1272, 6682, and 7246; `elc` for
ORE12087 and 16596; and `ht_bridge` for ORE4604, 7581, 9663, 11460, and 11745.
These are route-family probes, not ontology-specific routing proposals. A
candidate can influence production only if current-source features describe a
sound applicability domain and a controlled pair confirms a repeatable gain.

Separate hardware-independent functional array tests the largest omitted
historical opportunities before consuming scarce Gold nodes: `ht_shoq` and
`ht_bridge` on ORE10908, and `ht_bridge` on ORE7499. These forced workers are
allowed to fail closed; only a checkpointed retained-gold match can advance to
a paired performance gate.

The two ORE10908 probes completed and failed closed as `unsupported` in 0.0421
seconds (`ht_shoq`) and 0.0741 seconds (`ht_bridge`). Both records identify the
immutable v1 binary and are checkpointed, but neither publishes a taxonomy.
The historical fast wrapper therefore is not recoverable by merely selecting
either current route; restoring it would require identifying its removed
preprocessing contract. The ORE7499 `ht_bridge` probe reached roughly 17 GiB
of Slurm-observed RSS without completing after 1 minute 48 seconds and was
cancelled by exact array-task ID. It is not the historical low-memory
`htforce_race` mechanism and cannot replace the current certified route.

The named-route probes are not equivalent to the historical wrapper. A second
functional array therefore reproduces its exact environment: manual routing,
16 CB threads, absorption portfolio, forced Ht race, retained chain axioms,
and the established 18-GiB worker bounds. It tests ORE10908 and ORE7499 against
the immutable v1 binary before any production-routing inference.

The exact wrapper recovers ORE10908 on immutable v1: checkpointed
`status=ok`, retained-gold match, signature `161a98a585fc...`, 0.2866 seconds,
and 104.01 MiB peak RSS. The retained automatic record is 10.1467 seconds and
848.29 MiB. This establishes a 9.8601-second and 744.28-MiB opportunity, but
does not yet provide a sound feature gate for automatic routing. The ORE7499
arm used about fifteen CPUs for 2 minutes 10 seconds without finishing and was
cancelled by exact task ID. It no longer reproduces the historical 8.3-second
measurement and is rejected as a v1 routing candidate.
