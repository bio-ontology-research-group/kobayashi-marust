# ORE 1194 current-route profile

This diagnostic profiles the current single-worker nominal CB engine on ORE
1194 after the adaptive composite-term layout and shared prepared-ontology
changes. It records phase, saturation, message-loop, and per-rule counters for
300 seconds under Slurm. It does not count a timeout as a closure and does not
substitute profiling output for a gold comparison.

The source-bound binary is the frozen v14 full-sweep candidate. Its expected
SHA-256 is recorded by the job itself. `ibex_profile.sbatch` performs the
frontend and engine compute on a Slurm worker and writes only diagnostics to
the persistent scratch root.

IBEX job `49677322` was submitted on the `batch` partition with account
`pi-hohndor`. It completed the requested diagnostic and timed out honestly at
300 seconds (`rc=124`). The frozen v14 binary SHA-256 was
`47514b377f31b76284dab43853c6a5a2ac90133472cec37bce567ff0dcd3ca0a`;
the ontology SHA-256 was
`72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2`.

The one-worker engine parsed 1,062,240 clauses and then spent the full budget
in root seeding. It reached only 2,850 of 70,231 queries, created 7,378
contexts, and accumulated 278,269 pending messages without entering the
message fixpoint. Peak RSS was 1,668,864 KiB. This establishes root-query
volume as the immediate bottleneck rather than the packed-term representation
or the 20 GiB memory cap.

Scanning the same frozen clause payload for named-class unit implications
finds 3,426 groups connected by direct opposite edges and 5,204 aliases.
The candidate query-equivalence scheduler therefore removes 7.4% of 1194's
roots. That reduction remains a candidate performance improvement and does
not establish completion within the benchmark contract.
