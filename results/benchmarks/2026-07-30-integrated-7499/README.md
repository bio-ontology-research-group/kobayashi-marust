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
- focused exactness gate: job `49630735`;
- complete 592-ontology automatic sweep: array job `49630737`;
- independent terminal-row audit: job `49630738`.

The focused gate requires exact Konclude signature matches for 19 automatic
hard cases and for ontology 7499 through the explicit measurement route. A
completed diagnostic gate established 18 automatic exact matches plus the
7499 exact match; ontology 11315 timed out because the source EL pre-gate
rejected its three named-class disjointness axioms. Commit `4368e2e` corrects
that feature rule. The current gate must prove all 20 cases before Slurm releases
the full array.

## Full-sweep terminal guarantees

Each ontology receives one exclusive 24 GiB allocation, a 240-second reasoner
timeout, and a 20,480 MiB measured-tree watchdog. The runner writes terminal
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
