# Deterministic-subsumer shortcut in the konclude_ht bridge

Status: implemented, default ON, disable with `KM_HT_NO_DET_SUBSUMER=1`.
Scope: `engine/src/konclude_ht/bridge.rs` (pairwise verification) and
`engine/src/konclude_ht/classifier/mod.rs` (`SynchronousKPSetClassState`).
No Lean re-certification (bridge classification bookkeeping, not CB-calculus
logic).

## The mechanism in Konclude

Konclude classifies by satisfiability tests, but it never runs a subsumption
test for a subsumer it already knows deterministically. After a class
satisfiability test completes, `CSatisfiableTaskClassificationMessageAnalyser`
walks the root node's label and, in `create_root_class_subsumption_message`,
collects the named concepts whose dependency branching tag is at or below the
maximum deterministic branch tag:

```
deterministic = branching_tag <= max_deterministic_branch_tag
```

Those concepts are **branch-independent**: they are present in the completion
model without any nondeterministic (`⊔` / `≤n` merge / …) choice, so they hold
in *every* model of the tested class. They are shipped as a
`TellClassSubsumption` message and recorded on the subsumed class item through
`add_subsuming_concept_item` (the item's `mSubsumingConceptItemSet`). Only the
separate **possible-subsumption map** — the branch-dependent candidates — is
ever scheduled for a pair satisfiability test.

## The gap in the port

The port already ran this whole chain in production:

1. `bridge.rs::analyse_kpset_completion_model` invokes the live analyser with
   `EFEXTRACTALL` (includes `EFEXTRACTSUBSUMERSROOTNODE`).
2. `create_root_class_subsumption_message` emits the branch-tag-gated
   deterministic subsumers.
3. `process_class_subsumption_message` deposits them into the item's
   `subsuming_concept_item_set` via `add_subsuming_concept_item`.

But the bridge's non-deterministic pairwise loop (`classify_one`) verified
every candidate in `subs` with a full `bridged_unsat(s ⊓ ¬c)` probe. Its two
cheap pre-checks were:

- `candidate_state(s, c)` — reads the **possible-subsumption map** only;
- `pseudo_model_refutes(s, c)` — the pseudo-model merge test (can only refute).

A deterministic subsumer lives in the **subsumer set**, not the possible map, so
`candidate_state` returned `None` for it and the loop fell through to a full
satisfiability probe — re-deriving a subsumption that was already certain. On a
deep hierarchy each non-deterministic subject carries many deterministic supers,
so this was `O(deterministic supers)` redundant probes per subject.

## The fix

`SynchronousKPSetClassState::certain_subsumer(subsumed, subsumer)` reads the
recorded subsumer set:

```rust
self.ontology_item
    .get_concept_satisfiable_test_item_container()
    .get(subsumed_item.index())
    .is_some_and(|item| item.has_subsumer_concept_item(subsumer_item))
```

The pairwise loop consults it right after the saturation-known-pairs skip and
before the `candidate_state` / `pseudo_model_refutes` / `bridged_unsat` cascade:
a certain subsumer records the pair and `continue`s with no probe.

It is recorded like an **authoritative** subsumer (a bare `pairs.push((s, c))`),
not routed through `interprete_subsumption_result`. This matches the existing
authoritative read-off branch in the same file, which already pushes
deterministic label positives with no probe, and it keeps the change free of any
classifier propagation-state mutation, so budget-retry re-runs of a subject are
idempotent.

## Why it cannot weaken soundness or completeness

- **Sound.** A recorded deterministic subsumer was extracted under the branch-tag
  gate, so `subsumed ⊑ subsumer` holds in every model. Accepting it asserts only
  entailed subsumptions. Trusting deterministic subsumers without a probe is
  already established behavior for authoritative subjects in the same file; this
  extends the identical trust to the deterministic subset of a non-deterministic
  subject, which the analyser has explicitly separated out.
- **Complete.** Nothing is dropped. Possible (branch-dependent) subsumers still
  take the full pairwise probe. The shortcut only removes probes whose answer was
  already `true`.
- **Complete-or-defer preserved.** The shortcut never returns a verdict a probe
  would not have; it never causes a defer and never suppresses a needed probe.

If the deterministic-subsumer extraction ever regressed to record a
non-subsumer, this shortcut would surface it as a spurious subsumption instead of
having a probe silently mask it. `KM_HT_NO_DET_SUBSUMER=1` runs the
probe-every-pair path for an A/B and for bisection.

## Validation to run

- `cargo test --release -p konclude_ht` (or the crate's test target) — new unit
  test `certain_subsumer_reads_recorded_deterministic_subsumer_set` plus the full
  konclude_ht suite (no regression expected; the change is additive and gated).
- Bridge-arm corpus A/B: `KM_HT_ONLY=bridge` (or the certified production
  portfolio) with and without `KM_HT_NO_DET_SUBSUMER=1`; confirm identical
  subsumption signatures and a reduced `BRIDGE-PAIR-START` count
  (`KM_BRIDGE_PROGRESS=1` prints `BRIDGE-KPSET-SKIP … deterministic-subsumer`).

## Likely ontology families

Deep-hierarchy live-`∀ + ⊔` timeout onts where the bridge runs as the CB
fallback and each non-deterministic subject has many deterministic supers:
`10702`, `9540`, `5303`, `1603`, `12141` and neighbours. The win is a reduced
pairwise probe count, not a new verdict — it shrinks the search volume that
pushes those subjects past the probe budget into a defer.

## Batched refutation of the possible subsumers (2026-10-30, agent `data-values-2`)

Status: implemented, default ON, disable with `KM_BRIDGE_NO_BATCH_REFUTATION=1`.

Before the pairwise probes of a non-deterministic subject `s`, the bridge
collects the candidates `c1 … ck` that would each need a probe (not a told
or saturation-known pair, not a deterministic subsumer, not already decided
by the KPSet state or a hierarchy countermodel) and, for `k ≥ 2`, runs one
probe of `s ⊓ ¬c1 ⊓ … ⊓ ¬ck` (`bridged_unsat_rooted` with the negated seeds).
A satisfiable verdict is a completion model whose root is in `s` and in no
`ci`, so it is a countermodel of every `s ⊑ ci`; each `ci` is then recorded
as refuted exactly as a pairwise `false` verdict would be (KPSet
interpretation, hierarchy propagation, `refuted_here`). An unsatisfiable
verdict or no verdict within the probe budget changes nothing: the pairwise
probes run as before. The verdict carries the same trust as a pairwise
non-subsumption verdict (a clash-free completion), so neither soundness nor
completeness changes; only the number of probes does. The cost is one extra
probe for a subject whose batch is unsatisfiable (one of its candidates is a
subsumer).

Measured on qudt-merged (GitHub issue #4): every one of its 227 subjects
has 8 to 13 candidates defined by universal restrictions
(`FinancialUnit ≡ ∀quantityKind.FinancialQuantityKind`), its consistency
completion leaves 12,090 disjunctions open (so the precomputation replay is
off) and every probe re-derives the nominal-connected ABox (about 28,900
label insertions). Pairwise verification took 3,308 s for about 3,000
probes; with the batch, all 187 batched probes are satisfiable, one
pairwise probe remains, and
verification takes 65 s. Forced `ht_bridge`: 3,379 s → 146 s; automatic
route 156 s; 759 subsumptions, as HermiT 1.4.6 (2,340 s).
