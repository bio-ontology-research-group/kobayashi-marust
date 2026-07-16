# Codex handoff to `ws` — 2026-07-16

This is a temporary continuity note for resuming the active Codex thread on
the workstation. Read `AGENTS.md` first. The repository is intentionally dirty:
do not discard, reset, or overwrite any local change.

## User objective

Finish the ORE 2015 classification-routing project:

1. measure every isolated KM mechanism and the additive HT combinations;
2. compare them with ELK, HermiT, and Konclude on IBEX;
3. characterize ontology expressivity using the Konclude-compatible profiler;
4. compute ontology statistics;
5. learn a correctness-first decision tree using only mechanisms with an
   independent soundness and completeness contract;
6. wire that tree into default `km classify`;
7. retain every mechanism as an explicit route;
8. investigate every time or memory gap greater than 20 percent against the
   corresponding Konclude or Sequoia implementation.

The user explicitly rejected racing procedures for both benchmarking and
default routing. Each matrix arm must be an isolated mechanism. Sequentially
combined HT features are allowed because they form a new additive mechanism.
CB changes should follow Sequoia; HT and completion changes should follow
Konclude.

## Repository state

- Branch: `payg-strategy`
- HEAD before the dirty routing work: `98c761be6def27d2cf5046c4bcb395fb43816001`
- The worktree contains extensive intentional tracked and untracked changes.
- Do not clean it, reset it, or replace it with the older
  `~/km-frontend/kobayashi-marust` snapshot.
- Build artifacts are not transferred. Reuse the existing cache by exporting
  `CARGO_TARGET_DIR=~/km-frontend/kobayashi-marust/engine/target` before Cargo
  commands in the new checkout.
- The laptop was the previous source of truth. After this handoff, continue in
  `~/Public/software/kobayashi-marust` on `ws`.

Important new files include:

- `engine/src/frontend/profile.rs`
- `engine/src/routing.rs`
- `engine/src/routing/routing_tree_generated.rs`
- `docs/ROUTING.md`
- `docs/POSITIVE-ABOX-SEPARATION.md`
- `docs/SOLVE-148.md`
- `results/benchmarks/2026-07-15-routing/`

## Named ontology closures

The following difficult ontologies were individually closed and documented:

- 7914: exact Konclude cache invariants;
- 3215: Konclude KPSet phase barrier;
- 9663: native RBox links and role-specific saturation successors;
- 9724: Konclude intrusive free-list representation;
- 14817: saturation-aware cardinality successor construction;
- 148: exact nominal classification with isolated influenced labels and
  incremental Pred antichains.

Do not infer from these individual closures that the complete 592-ontology
corpus is closed. The most recent fully published production sweep before the
routing matrix had 575 completed and 17 timeouts, with 515 exact Konclude
matches. It also reported disagreements that later work partly corrected.

## Current IBEX matrix

IBEX root:

```text
/ibex/scratch/hohndor/km/routing_20260715
```

Frozen matrix:

```text
job:             48946164
binary SHA-256:  c229366fcc9efbfec729f5a7dcc1a5f1ef9b12fe41f433b67282930bf18a92f6
results:         matrix-results-c229366f/
manifests:       manifests-c229366f/
failures:        failures-c229366f/
profiles:        profiles-schema2-positiveabox1/
```

The array is no longer running, but the matrix is not complete:

- expected ontology panels: 592;
- atomically published panels: 579;
- rows per complete panel: 28;
- total published rows: 16,212.

Two of the 50 shard tasks ended `OUT_OF_MEMORY` at about 192 GiB. The Python
watchdog's 20 GiB polling cap did not prevent a rapid allocation spike from
killing the whole Slurm allocation. Because each panel is published only after
all 28 arms validate, the active partial panels were lost and later ontologies
in those shards never started.

Exact missing-panel diagnosis:

| Shard | Trigger | Arm at allocation death | Collateral ontologies never started |
|---|---|---|---|
| 5 | `ore_ont_3524.owl` | ELK | 5089, 5090, 6207, 7639 |
| 6 | `ore_ont_15703.owl` | `ht_bridge` | 16167, 16626, 16777, 2228, 3770, 8369, 8806 |

Thus the 13 absent files are not 13 KM classification failures. Eleven were
never attempted. Production KM had previously classified all thirteen:

- the eleven collateral ontologies matched retained Konclude signatures;
- 3524 and 15703 completed in about 12 seconds at approximately 2.6 and
  2.4 GB, but they have no retained Konclude gold and still need independent
  HermiT adjudication.

Required matrix repair:

1. rerun these 13 ontologies as separate ontology jobs;
2. isolate every arm in its own Slurm step or allocation with a hard cgroup
   memory limit, so one runaway mechanism cannot kill the panel;
3. retain atomic 28-row panel validation;
4. rerun the strict analyzer only after all 592 panels exist.

The five frozen no-Konclude-gold inputs are:

```text
10860 1194 15703 3524 4669
```

They require HermiT adjudication. A parseable `nogold` output is not proof of
correctness.

## Interim performance result, not a final claim

On the 579 published panels, using the best exact,
contract-eligible KM mechanism per ontology and the strict faster-time /
lower-memory Konclude envelope:

```text
paired correct KM candidates: 419
KM average time:              6.287 s
Konclude average time:        1.306 s
KM median time:               0.261 s
Konclude median time:         0.166 s
KM average memory:            483 MB
Konclude average memory:      377 MB
KM median memory:             40 MB
Konclude median memory:       133 MB
```

If all empirically exact measurement arms are admitted, including procedures
not certified for automatic routing:

```text
paired candidates:            471
KM average time:              2.906 s
Konclude average time:        1.784 s
KM median time:               0.214 s
Konclude median time:         0.217 s
KM average memory:            270 MB
Konclude average memory:      516 MB
KM median memory:             31 MB
Konclude median memory:       141 MB
```

These are oracle selections, not a learned or deployed router. They exclude
ontologies without a correct candidate and the 13 missing panels. Never report
them as the final full-corpus result.

## Correctness gates

The analyzer permits automatic policy learning only for mechanisms with an
independently established contract:

- strict `elc` when its normalized-clause fragment check accepts;
- plain and absorbed CB variants;
- `lean`, `seq_on`, and `seq_off`;
- exact `nominals` for nominal/ABox inputs;
- `ht_rules` only on its validated rule fragment.

Measurement-only HT/QO/SHOQ/cardinality/general/tableau arms remain excluded
even if they happen to match corpus gold. Several have known incomplete
counterexamples. The bridge and additive HT packs also remain excluded until
their automatic applicability contract is established.

The positive-ABox separation certificate safely routes 10697 and 15725 to
ordinary TBox classification. It deliberately rejects 15846.

## Active 15846 debugging

Ontology 15846 remains the active exact-nominal performance problem.
Konclude's architecture precomputes ABox consistency once, then classifies the
TBox. KM's exact nominal path currently rebuilds and saturates a large ground
context across query work.

The current dirty `engine/src/engine.rs` adds:

1. Hyper role postings indexed by one fixed ground endpoint, including mixed
   ground/variable role atoms such as `S(o,y)`;
2. batched inter-context message completion, saturating each touched context
   once per batch rather than once per message;
3. `KM_NO_BATCH_COMPLETION=1` to restore the old per-message schedule;
4. `KM_TRACE_HYPER_PRODUCT=<threshold>` to report large pre-join Hyper
   Cartesian upper bounds.

The endpoint index was initially too restrictive because it indexed only roles
with both endpoints ground. It now indexes a fixed ground endpoint even when
the other endpoint is a variable. After that correction:

- `nom_rule_oiq_example3` passes;
- its negative control passes;
- the nominal test group passed;
- the new role-endpoint ordering test passes;
- batching is enabled by default and the diagnostic opt-out restores the old
  schedule.

The latest direct optimized 15846 run still timed out at 180 seconds. Its
diagnostics showed:

```text
initial ground closure:     about 1.523 million clauses
messages applied:           about 2.12 million
saturation calls:           20,635, down from one per message
returned ground clauses:    about 1.26 million
queue remaining at timeout: 155,930
new clauses added:          94,564
Hyper profile time:         about 97.7 seconds
peak RSS:                   about 2.38 GB
```

The next precise step is to run 15846 with the release binary and
`KM_TRACE_HYPER_PRODUCT` on `ws`, identify the largest remaining Hyper
candidate products, and compare the corresponding indexing or join discipline
with Sequoia. Do not make speculative semantic changes. The current batching
and endpoint indexing are scheduling/index changes intended to preserve the
fixpoint; verify that argument and run the full release suite before promotion.

## Operational reminders

- This Codex process is already running on `ws` (`hostname leechuck-office`).
  Treat `ws` as the local host and never invoke `ssh ws` or a `ws:` transfer.
- The workstation-adjusted `remote-connect` skill is installed at
  `~/.codex/skills/remote-connect/SKILL.md`; its local-host override takes
  precedence over its generic remote-host instructions.
- Build and run KM directly in this checkout on `ws`.
- Export
  `CARGO_TARGET_DIR=/home/leechuck/km-frontend/kobayashi-marust/engine/target`
  before Cargo commands to reuse the existing build cache.
- Benchmarks and full corpus runs go through Slurm on IBEX.
- From `ws`, use the configured host alias:

```bash
ssh ibex
```

- Use PID-specific kills, never `pkill -f`.
- Preserve all existing dirty changes.
- Before committing, inspect the full diff, run release tests on `ws`, perform
  the relevant IBEX exact-signature regression sweep, and update the closure
  and routing documentation.
