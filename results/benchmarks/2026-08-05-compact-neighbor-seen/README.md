# Rejected compact predecessor-message deduplication

This experiment replaced each context's `neighbor_pred_seen: HashSet<u32>`
with a sorted `Vec<u32>` and binary-search insertion. The set only suppresses
duplicate predecessor-message arrivals, so the representation change would
have preserved the derived fixpoint. A focused unit test and release check
passed.

The workstation production-route gate rejected the change before an IBEX run.
On ORE4669, current `main` and the candidate emitted byte-identical output
(SHA-256 `d9f2ef6fe9159392094a154c24201f90d502fc9ac5a7f02717d57642e282a58a`).
The candidate took 77.98 seconds at 4,824,304 KiB peak RSS versus 79.73 seconds
at 4,824,220 KiB for `main`: ordinary run noise in wall time and no memory
improvement. On ORE1194, both failed closed at the production memory watchdog;
the candidate took 32.62 seconds at 18,953,984 KiB versus 32.98 seconds at
18,923,964 KiB for `main`, a 30,020 KiB regression.

An initial direct-engine diagnostic was invalid because it fed the unrestricted
frontend clause set rather than the production-routed workload. Both `main` and
the candidate grew far beyond the production profile under that input, so it
is not used as promotion evidence.

No source code from this experiment was merged. The result narrows the useful
design space: `neighbor_pred_seen` needs constant-time insertion. Its hash-set
overhead is not material in process-tree peak RSS on these production routes.
