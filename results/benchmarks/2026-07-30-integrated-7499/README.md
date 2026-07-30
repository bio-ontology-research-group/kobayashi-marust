# Integrated cardinality-route validation

This capsule validates commit `51502e3`, which combines the feature-based
large-ABox router, the completion diagnostic cache, shared CB ontology state,
and the restored `certified_card_proxy_abox` route.

The new cardinality route is measurement-only. It solves
`ore_ont_7499.owl` exactly when selected explicitly, but automatic routing does
not select it because its ABox-elision step lacks a complete consistency and
ABox-irrelevance certificate.

## Local gate

The complete release suite passed on the workstation:

- 1,786 library tests passed;
- 32 integration tests passed;
- zero tests failed;
- eight tests were ignored.

## IBEX execution

`ibex_build.sbatch` builds the archived `51502e3` source on an IBEX compute
node. It installs the same resulting executable into the focused and full-sweep
capsules and verifies them with `cmp`.

`ibex_focused.sbatch` is a fail-fast semantic gate. It requires exact Konclude
signature matches for 19 automatic hard cases and for
`ore_ont_7499.owl` through the explicit `certified_card_proxy_abox` route. Any
nonzero reasoner exit, timeout, or signature mismatch makes the Slurm job fail.

The first focused submission, job `49627676`, intentionally demonstrated the
launcher checks: it rejected the workstation-built executable because IBEX
lacks `GLIBC_2.39`. Every attempt exited in 0.00 seconds, the job failed, and
the dependent full sweep remained `DependencyNeverSatisfied`. No ontology
result from that submission is valid.

The first corrected build, job `49627755`, compiled successfully but the
post-build smoke command used `km --help`, whose intentional usage exit code
made the fail-fast script stop before installation. Its dependent jobs did not
run. The smoke command is now `km routes`.

Focused job `49628099` then stopped after the first reasoner result because the
focused capsule lacked the comparator's `ore_canon.py` module. The reasoner
completed ontology 148, but its uncomputed verdict is not evidence. The job and
its dependent full sweep were cancelled. The gate now verifies the comparator
import before running any ontology and treats every comparator error as a
terminal gate failure.

The active source-bound chain is:

- IBEX build: job `49628097`, completed successfully;
- focused exactness gate: job `49628211`, using the installed build;
- complete 592-ontology automatic sweep: job `49628278`, after successful
  focused validation.

The full array uses one exclusive allocation per ontology, a 240-second
reasoner timeout, a 20,480 MiB watchdog, per-ontology profile validation,
terminal checkpoints, atomic result publication, and exact Konclude-signature
comparison. The initial 22 GiB and 28 GiB Slurm allocations both let two giant
reasoner processes cross the cgroup limit between watchdog samples, killing the
supervisor before it could publish a row. The Slurm allocation is 64 GiB so the
Python supervisor remains alive long enough to publish a terminal `memout` if
the reasoner crosses the 20,480 MiB contract. Results are not claimed until the
jobs complete and their output and checkpoint counts are audited.
