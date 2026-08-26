# Large bridge subject-worker exploration

This exploratory gate measures bounded subject partitions on ORE3215,
ORE14817, and ORE10621. `KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE` accepts only one
through eight workers and changes scheduling only: every partition receives
the complete ontology and superclass universe, and publication occurs only
after all exact partitions complete and merge. The gate requires retained
full-IRI gold equality for every arm and records process-tree peak RSS so a
wall-time improvement cannot hide a memory-cap failure.

The first arrays (`50843116` and `50843331`) are not performance evidence.
The former oversubscribed one half-node; the latter used exclusive nodes but
did not constrain the CPU model, and its ORE3215 baseline landed on a Xeon
E5-2699 v3 and timed out. The harness rejected the nonterminal row before
publication. The remaining tasks and the old baseline-resume dependency were
cancelled by exact job ID. Replacement array `50843607` adds
`cpu_intel_gold_6248`, remains exclusive and sequential (`%1`), and starts from
empty result and failure directories. Only that replacement may support an
optimization decision.
