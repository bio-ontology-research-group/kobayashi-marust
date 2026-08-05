# Rejected compact predecessor-message deduplication

This experiment replaced each context's `neighbor_pred_seen: HashSet<u32>`
with a sorted `Vec<u32>` and binary-search insertion. The set only suppresses
duplicate predecessor-message arrivals, so the representation change would
have preserved the derived fixpoint. A focused unit test and release check
passed.

The workstation performance gate rejected the change before an IBEX run.
ORE4669's single-thread CB engine had not completed after 74.72 seconds and was
terminated by PID; current `main` completes the same gate in roughly 21 seconds.
Peak RSS at termination was 682,140 KiB, but the incomplete run cannot support
a memory comparison. The workload contains millions of predecessor-message
identifiers, and sorted-vector insertion shifts too many existing `u32` values.

No source code from this experiment was merged. The result narrows the useful
design space: `neighbor_pred_seen` needs constant-time insertion, or a compact
structure whose append-only assumptions are demonstrated from the actual
identifier arrival order.
