# OWLAPI monitor overhead investigation

Status: targeted revalidation in progress. No release acceptance is inferred
from diagnostic timings.

The 80-case signature-fix validation completed with 75 fully comparable OWLAPI
cases, 600 comparable update cells, zero canonical answer differences, and zero
comparable-cell performance failures. ORE12351 completed all five repetitions.
ORE9724 lost candidate-retained initialization in repetition 0 at the 240-second
limit. ORE15703 also lost one corresponding baseline initialization: the
baseline retained arm completed revision 0 in repetition 3 at 239.4 seconds;
the candidate timed out. These records remain preserved in
`validation/full80-11db48ce-v1` on IBEX.

## Confirmed measurement overhead

The OWLAPI readiness callback performed a complete `/proc` scan on every
watchdog tick, immediately after the watchdog had already scanned `/proc`.
The supervisor and worker share the job's one allocated CPU. Thus monitoring
cost depended on the other processes on the node.

An IBEX Gold 6248 control measured a sleeping child for 15.034 seconds. The
supervisor consumed 8.749 CPU seconds while making 611 whole-node scans over
about 750 processes. Removing only the duplicate scan still consumed 6.292 CPU
seconds in 15.030 seconds. In a real ORE9724 initialization, the original
supervisor consumed 58.934 CPU seconds over 135.466 seconds of lifecycle time.
These observations establish substantial measurement overhead; the scoped
revalidation must establish whether eliminating it resolves the release gates.

Two local ORE9724 initializations completed in about 54 seconds. A local
ORE15703 initialization completed in 138.78 seconds (50.49 parsing, 83.72
creation/classification, 4.57 taxonomy publication). Its canonical answer
matches the baseline's 1,604,386 pairs:
`1a229adb9250c83c96ea7ab33d70e444d57c9ab9a42ea00b8fd4374f4419c4ac`.
Local timings are diagnostic only.

## Correction and validation

The revised monitor enumerates the worker's kernel memory cgroup (or unified
cgroup) and its descendant cgroups, then applies the existing process-tree and
process-group RSS calculation. Fork, exec, and setsid preserve cgroup
membership. If the scope cannot be read or does not contain the watched PID,
it falls back to the original complete process-table scan. PID identity
tracking reuses the watchdog's sampled membership. The final subreaper cleanup
continues to inspect the complete process table. Resource trips are retained
explicitly even if killing the worker produces a subsequent stdout EOF.

The limits remain 240 seconds per request, 20,480 MiB for the worker tree,
one allocated Gold 6248 CPU, five paired repetitions, and the same balanced
four-arm ordering and ontology revisions. All arms use the revised harness.
The initial targeted array is 54101655, case indices 74 and 76. Each allocation
first proves that scoped sampling works on its node. The remaining 78 cases are array 54101937 (indices 0–73, 75, and 77–79).
Timing claims require the complete corrected panel. Initial corrected candidate
ORE9724 attempts completed in 54–80 seconds and ORE15703 attempts in 153–193
seconds; full sessions and all five repetitions remain subject to the release
guards. Ten allocation smoke checks measured approximately 2% monitor CPU
use with three scoped PIDs and zero full-table fallback samples.

The candidate native binary is unchanged from commit
`4dd7995b5def62bb8f9140dd2be62b671816f71b`; its Java adapter is unchanged from
`11db48ce73029227c7a28b9ad5e2e2a25189cc2a`. The baseline remains KM v1.5.0,
commit `d95f0b840a433b5b43c4eff48092e8b600bca8de`, with its published PGO binary.
The prepared release source before this harness correction is
`7baac356dd5a043676fef90e51f96e57e7c49f4d`.

## Focused tests

Five scoped-sampling tests, three OWLAPI process-cleanup integration tests,
and twelve existing process-tree watchdog tests passed. They cover nested and
detached children, PID-namespace fallback, missing scope files, RSS caps, timeout
kills, and shared-snapshot membership callbacks. The runtime directory freezes
the exact measurement sources; `four-arm-bindings.json` pins their hashes along
with the unchanged candidate and baseline artifacts.
