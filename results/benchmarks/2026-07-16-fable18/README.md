# Fable implementation panel over the historical hard 18

The 18 ontologies are the historical residual list, not a current gap list.
Most were already closed on `payg-strategy`; current status is recorded in
[`../../../docs/SOLVED-ONTOLOGIES.md`](../../../docs/SOLVED-ONTOLOGIES.md) and
[`../../../docs/HARD-RESIDUAL-AUDIT.md`](../../../docs/HARD-RESIDUAL-AUDIT.md).

This panel compares four isolated Fable-agent commits:

- cardinality: `b4dbabc`
- rules: `a295d2d`
- KPSet routing: `a58db7a`
- root ordered resolution: `cb258a1`, explicitly enabled with
  `KM_ROOT_ORDERED=1`

The cardinality, rules, and KPSet arms do not alter CB-calculus derivations.
The ordered arm does, so its Lean re-certification is required and is currently
deferred.

Each implementation is built and unit-tested in its own worktree, copied to
IBEX as an immutable binary, and run over the historical 18-ontology residual:

```text
541 1603 2669 3215 6934 7499 7581 7914 9540
9663 9724 10621 10702 12653 14817 15516 15672 15803
```

The panel uses the frozen matrix runner with a 240-second timeout and 20 GB
memory cap. The retained Konclude signature is used for the mechanical diff.
For `2669` and `15516`, a consistency disagreement with stale Konclude output
must be adjudicated against the committed inconsistent witnesses and must not
be labelled KM unsound.

IBEX result root:

```text
/ibex/scratch/hohndor/km/fable18_20260716/
```

## Execution status

The first 72-run submission completed, but every row failed before KM started:
the workstation-built binaries require GLIBC 2.39 and the IBEX compute image
provides an older GLIBC. Those rows are deployment errors, not reasoner
results, and must not be included in coverage or performance totals.

The four commits have since been consolidated into the active source tree.
Their workstation release tests passed independently before integration. The
panel must be rerun with binaries built inside a compatible IBEX compute
environment. Until that rerun completes, the ontology recoveries stated in the
individual commit messages remain historical/focused evidence rather than a
new combined 18-ontology benchmark result.

Root ordered resolution remains gated and uncertified. Its panel row is an
experiment with `KM_ROOT_ORDERED=1`, not a production-route endorsement.
