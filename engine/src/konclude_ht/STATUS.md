# konclude_ht — current state & next steps

A direct, function-by-function Rust port of Konclude's hypertableau reasoning
kernel, incorporated as a self-contained KM module. This file is the at-a-glance
status; `PORT.md` holds the full wave-by-wave history (W0–W16) and the per-unit
status table. **License note:** Konclude is LGPL; this is a derivative work —
LGPL headers + attribution still need to be added (see Next steps §5).

_Last updated 2026-06-30. HEAD `c1e5e9a` on branch `payg-strategy` (local, not
pushed)._

## What it is

~100k LOC across 145 `.rs` files under `engine/src/konclude_ht/`, wired into
`lib.rs` (`pub mod konclude_ht;`). The entire Konclude kernel was translated
structurally (model + process + completion[36 units] + saturation[12 units] +
cache + task + calculation), then progressively brought to life. It is now a
**running, test-validated reasoner** for a usable fragment, not just a compiling
skeleton.

## Current state

### Works, and is tested (26 `#[test]` in `completion/{selftest,classify_test}.rs`, all green on ws)
- **ALC consistency**: conjunction (`⊓`), disjunction (`⊔`) with **branch
  creation + chronological backtracking**, negation, **clash detection**, TBox
  unfolding (`A ⊑ B` via the implication rule).
- **Roles / successors**: `∃R.C` creates a successor node + R-edge and labels it;
  `∀R.C` propagates over edges; **nested `∃` grows multi-node** (root→n1→n2…).
- **SHIQ breadth**: qualified number restrictions `≥n R.C` (n distinct
  successors) and `≤n R.C` (merge-or-clash via the u15 merge); RBox — role
  **hierarchy** (`R⊑S`), **inverse** (`R⁻`), **transitivity** (`Trans(R)`).
- **Classification**: consistency-based subsumption (KM's actual task) —
  `A⊑B` iff `A ⊓ ¬B` unsatisfiable; direct, transitive, and conjunctive
  subsumption + unsatisfiable-concept all verified.

### Architecture in place (compiles clean on ws, `cargo check --release` exit 0)
- **Substrate**: `model/substrate.rs` — typed arena `Id<T>` + `Arena<T>` +
  watermark/truncate backtrack (replaces Konclude's raw `CXxx*` + memory pool).
- **`ProcessContext`** (54 arenas) — the per-test ownership root; **`CacheContext`**
  (64 arenas) — the cache pool root.
- All process/saturation satellites (variable-binding paths, distinct/connection-
  successor, blocking-candidate hashes, propagation/representative bindings,
  merge/condensed-reapply/successor-role hashes, saturation successor tower).
- **Dependency factory** (7 variant allocators) + **clash/stop propagation** via a
  cooperative `CalcSignal` on the context (KONCLUDE-PORT-NOTE[exceptions], avoids
  threading `Result` through ~450 rule signatures).
- **Live engine**: the driver loop (`handle_task`/`take_next_process_individual`),
  the processing-queue subsystem (4 queue kinds), the rule-dispatch jump table
  (`tableau_rule_choice`, ~60+17 opcode arms → `apply_*_rule`), and the test
  entry `run_completion_on(ctx)` (bypasses the still-deferred Task adapter).

### Remaining deferral markers (grep counts, the honest scope of "not yet live")
| marker | count | meaning |
|---|---|---|
| `W6-DEFER` | 1182 | cache backend IO (the whole Cache optimization layer) |
| `W3-DEFER` | 1216 | completion in-method deferrals (mix: cache/datatype/Task-blocked + some now-resolvable) |
| `PORT-PENDING` | 402 | whole-method stubs awaiting siblings/subsystems |
| `W2-DEFER` | 313 | process-layer api gaps (hash population paths, edge-install reapply) |
| `W4-DEFER` | 218 | saturation bodies |
| `todo!` | 50 | unfilled method bodies (off the tested path) |
| `RECONCILE-NEED` | 42 | flagged sibling-method gaps (mostly stale — already ported under Rust names) |

## Build & test (ws only — NEVER on the laptop)

```bash
rsync -a engine/src/ ws:km-frontend/kobayashi-marust/engine/src/
ssh ws 'cd ~/km-frontend/kobayashi-marust/engine && cargo test --release konclude_ht 2>&1 | grep "test result"'
# or: cargo check --release 2>&1 | tail
```

## Next steps (priority order)

1. **Blocking (termination on cyclic TBoxes).** The biggest *correctness* gap. A
   cyclic axiom like `A ⊑ ∃R.A` currently grows forever (a 5M-iteration hard cap
   in `run_completion_on`/`run_saturation_loop` is only a hang-guard). Port the
   pairwise/subset blocking test: the `detect_*` units + the blocking-test path
   in `individual_node_initializing` (`completion/u03.rs`) → consult the already-
   ported `blocking_hash` / `reapply_sat` signature-blocking satellites. Test:
   `A ⊑ ∃R.A` → blocked, terminates, CONSISTENT.
2. **Dependency-directed backjumping.** Replace the chronological backtrack with
   the faithful `clashedBacktracking` (`completion/u29.rs:430/495`), which needs
   the tracking-line records from units 28/30. Improves correctness on hard
   disjunction and is the faithful Konclude search.
3. **Drive a real ontology end-to-end.** Wire a thin entry that feeds KM's
   existing DL-clause/`ofn` output (or a hand-built `OntologyArenas`) into
   `run_completion_on`, and classify a small real ontology. Surfaces the next
   hot-path `todo!`s (the natural enqueue still has W3-DEFER seams; the reapply
   queue uses a re-drive-to-fixpoint stand-in — see `classify_test.rs`).
4. **Broaden the un-defer tail** (toward "the entire port"):
   - Saturation un-defer (s02–s12, the W4-DEFER bodies) — the W4.5 satellites
     exist; the lazy-saturation pre-pass is what makes Konclude fast.
   - Cache backend (the 1182 `W6-DEFER`): the F8 cache-event family + a single-
     thread write drain + the missing linker/counting APIs (see the W6.5 note in
     PORT.md). This is an optimization layer — the reasoner runs without it.
   - Datatypes, nominals (`O`) expansion, the `Self` and role-chain rules.
5. **Productionize**: add LGPL headers + attribution to `konclude_ht/`; expose a
   `km konclude_ht <ont>` subcommand or route the hybrid router to it; validate
   verdicts against Konclude on a small ORE fragment (the existing `.sig.gz`
   signature-diff harness).

## Faithfulness deviations (tagged in-source as `KONCLUDE-PORT-NOTE[...]`)
- `[ownership]` raw pointers + memory pool → typed `Arena<T>`/`Id<T>` + watermark.
- `[exceptions]` `throw CCalculationClash/StopProcessing` → cooperative
  `CalcSignal` pending-signal on the context, drained at the loop boundary.
- Chronological backtrack stands in for dependency-directed backjump (next step 2).
- The role reapply-queue / link-processing-restriction path is approximated by a
  label-set scan in the `∃`-rule (`ht_reapply_universal_restrictions`); the
  inverse direction uses the ancestor link rather than an installed reverse edge.
- Classification re-drives to a label-count fixpoint as a sound stand-in for the
  unported reapply queue.

## Commits this session (newest first)
```
c1e5e9a successor nodes drain - nested ∃ grows multi-node      (26 tests)
5751e72 SHIQ breadth + classification                          (24 tests)
b767ef1 ALC consistency complete - ∃/∀ + edges
527421c ALC propositional core (AND/OR/branch/unfold/clash)
dbe13ac rule engine drives - first inference over main loop
18c56fc FIRST RUN - port executes + produces verdicts
66abbb3 live processing-queue subsystem (inner drive loop)
a646ace main driver loop + merge/expansion satellites
7c7c07a checkpoint the compiling kernel
```
