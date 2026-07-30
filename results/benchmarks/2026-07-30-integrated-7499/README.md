# Integrated automatic-route acceptance

This capsule validates KM's feature-based automatic classifier plus the
measurement-only `certified_card_proxy_abox` route.

Automatic routing does not select `certified_card_proxy_abox`. The route can
solve `ore_ont_7499.owl` exactly when requested explicitly, but its ABox-elision
step does not yet carry the consistency and ABox-irrelevance proof required for
an automatic complete answer.

## Current source and local tests

The acceptance source is commit `4368e2e`. It keeps independent class-only
ABoxes with named-class disjointness on the normalized ELC complete-or-defer
path. Binary `DisjointClasses(C D)` is the EL bottom axiom
`C ⊓ D ⊑ ⊥`; rejecting that source shape diverted ontologies 4755, 8068, and
11315 to the slower HT bridge.

The complete release suite passes:

- 1,786 library tests passed;
- 32 integration tests passed;
- zero tests failed;
- eight tests were ignored.

## Source-bound IBEX chain

`ibex_build.sbatch` verifies archive
`km-main-4368e2e.tar.gz` by SHA-256, builds it on an IBEX compute node, smoke
tests `km routes`, and installs one byte-identical executable into the focused
and full-sweep capsules.

The current chain is:

- build: job `49630715`;
- focused exactness gate: job `49631418`;
- complete 592-ontology automatic sweep: array job `49632192`;
- independent terminal-row audit: job `49632193`.

The focused gate completed successfully. All 19 automatic hard cases and
ontology 7499 through the explicit measurement route matched their Konclude
signatures exactly. In particular, the feature correction in `4368e2e`
recovered 4755 in 6.26 s, 8068 in 3.81 s, and 11315 in 9.53 s on the gate node;
11745 remained exact and completed in 25.03 s. Slurm therefore released the
full array.

An initial release of the full array, job `49631419`, exposed that the debug
partition could schedule unconstrained tasks on different CPU generations.
It produced two exact diagnostic rows, which are archived separately on IBEX,
and was cancelled before further tasks ran. Those rows are excluded from every
production aggregate. The replacement array above fixes and verifies the CPU
model.

## Full-sweep terminal guarantees

Each ontology receives one exclusive 24 GiB allocation on an Intel Xeon Gold
6248 node, a 240-second reasoner timeout, and a 20,480 MiB measured-tree
watchdog. The job checks the runtime CPU model before invoking KM, so a
scheduler or constraint regression fails instead of contaminating timing
aggregates. The runner writes terminal
checkpoints and publishes final rows atomically. Profiling happens only after
the authoritative result exists and has its own address-space limit.

IBEX can charge a parallel allocation burst to the whole task cgroup before the
RSS sampler sees it. In that case the kernel can kill the reasoner and its
in-process supervisor together. `ibex_full_audit.sbatch` therefore runs in a
separate 2 GiB allocation after every array task terminates. It:

1. validates every published terminal row;
2. atomically salvages a valid checkpoint when present;
3. recovers a missing row as `memout` only if that task's Slurm log contains an
   explicit OOM-kill marker;
4. fails on every unexplained, malformed, duplicate, or missing result;
5. declares success only with 592 validated terminal rows.

The array is resumable. A task with an existing validated row reports
`ALREADY_COMPLETE`; an invalid row fails instead of being silently overwritten.
The audit implementation passes a synthetic test containing a checkpoint,
an OOM-proven missing row, and an unexplained missing row.
