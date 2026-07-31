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
`pi-hohndor`. Its result remains pending and must be checked before drawing a
performance conclusion.
