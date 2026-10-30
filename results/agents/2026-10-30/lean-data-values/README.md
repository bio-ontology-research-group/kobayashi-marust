# Lean proofs of the v1.5.5 data-value encodings (agent `lean-data-values`)

2026-10-30, branch `fix/v155-lean-data-values` off `development/v1.5.5`
(e62a4bce). Proofs: `lean/ContextCalculus/TwoSortedDL.lean`,
`DataValueProjection.lean`, `DataValueSingletonElision.lean` (and the
existing `LinearValueEncoding.lean`, now built by `lake build`). Statements,
hypotheses and findings: `docs/DATATYPES.md`, "Lean coverage (2026-10-30)".

## Probes

`probes/*.ofn`, HermiT answers in `gold/*.json` (HermiT oracle of
`.work/agent-scratch/data-values/oracle`, as in
`results/agents/2026-10-30/data-values/`). Runner: `scripts/diff_run.py`
(copy of the data-values runner), routes `auto`, `certified_nominals`,
`nominals`, 60 s cap:

    DIFF_THREADS=4 DIFF_KM_TIMEOUT=60 python3 -I scripts/diff_run.py KM \
      .work/agent-scratch/data-values/oracle gold diff-TAG.tsv \
      auto,certified_nominals,nominals probes/*.ofn

Binaries:

- `dev`: `cargo build --release --bin km` of e62a4bce (this branch's base;
  the branch changes no Rust), copied to
  `.work/agent-scratch/lean-data-values/km-e62a4bce` (sha256 prefix
  `cd6d02d748dff754`).
- `v154`: `.work/pgo-v154/km-pgo-use` (sha256 prefix `ac15b82272bd22ad`).

| probe | HermiT | dev (3 routes) | v1.5.4 (3 routes) |
|---|---|---|---|
| `opaque_merge` | inconsistent | WRONG (consistent) | DROPPED / REFUSED |
| `opaque_merge_keep` (same + unrelated `Z ⊑ ≥ 2 q`, singletons kept) | inconsistent | ok | not run |
| `opaque_merge_tbox` | `A ≡ B` | WRONG (misses 2 subs) | WRONG (misses 2 subs) |
| `opaque_merge_tbox_keep` | `A ≡ B` | WRONG (misses 2 subs) | not run |
| `opaque_single` | inconsistent | ok | DROPPED / REFUSED |
| `range_exhaust` (9 values) | inconsistent | WRONG (consistent) | DROPPED / REFUSED |
| `range_exhaust_keep` | inconsistent | WRONG (consistent) | not run |
| `range_exhaust8` (8 values) | inconsistent | ok | not run |
| `range_exhaust_tbox` | `A ⊑ ⊥` | WRONG (misses `A`) | WRONG (misses `A`) |

`opaque_merge` against `opaque_merge_keep` isolates the singleton elision
(finding 1 in the doc): the only difference is a construct that closes the
elision gate. `range_exhaust` against `range_exhaust8` isolates the missing
cover of a 9-value range (finding 2; not caused by the elision, see
`range_exhaust_keep`). Rows: `diff-dev.tsv`, `diff-v154.tsv`.

## Lean build

`lean/.lake/packages` is a hard-link copy (`cp -al`) of
`.work/worktrees/checkers-on/lean/.lake/packages` (built Mathlib). The
host's memory commit limit (`vm.overcommit_memory = 2`) made a fully
parallel `lake build ContextCalculus` fail with ENOMEM, so the library was
first built by import level, four modules per `lake build` call
(`.work/agent-scratch/lean-data-values/levelbuild.py`, 330 modules), and
then confirmed with a plain `lake build ContextCalculus`: "Build completed
successfully (8643 jobs)", no `declaration uses 'sorry'`. Axioms of the main
theorems (`#print axioms`): `propext`, `Classical.choice`, `Quot.sound`.
