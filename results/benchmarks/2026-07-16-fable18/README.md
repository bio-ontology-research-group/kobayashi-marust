# Fable implementation panel over the historical hard 18

This panel compares four isolated Fable-agent commits:

- cardinality: `b4dbabc`
- rules: `a295d2d`
- KPSet routing: `a58db7a`
- root ordered resolution: `cb258a1`, explicitly enabled with
  `KM_ROOT_ORDERED=1`

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
