# ORE 1194 QO/KPSet residue probes

These workstation probes start from the retained cardinality-aware TInput
`/tmp/1194-card.tin.json` (932,183 clauses, 70,231 queries) and use the current
production source at `45a051a`. Every route was bounded, certify-only where
applicable, and emitted zero bytes on timeout or deferral.

## Shared-filler precompute and diagnostic residue completion

The production batching/indexing options reproduce the established bounded
precompute:

```text
QO PRECOMPUTE converged el=183200ms nodes=80557 stored_edges~21019012 pending=483811
KPSET saturate_global: 185.67s nodes=80557 unsupported=false kp_insuff=true qo_insuff=true pending=483811
QOKP card-split: clean=0 affected(residue)=70231 of 70231
```

The explicitly unsound diagnostic bypass `KM_HT_QO_RESIDUE_FORCE=1` did not
produce an approximate result. Its one-model global completion immediately
reported `unsupported`, then the ordinary fallback was still saturating at the
240-second cutoff. This rules out a cheap final branch over the 483,811 parked
instances.

## Predecessor-local successors

`KM_HT_QO_SAT=1` creates predecessor-local successors and avoids relying on
shared filler identities. With `CARDMERGE`, propagation batching, exact edge
membership, `EDGEFAST`, and `FASTIMPL`, it still timed out at 240.17 seconds,
peaked at 6.69 GiB, and emitted zero bytes. A traced replay showed three broad
literal/edge waves; at 231.7 seconds it retained 2,817,004 literal events and
2,687,284 edge events.

## Rejected propagation layouts

- Dense node-indexed `Vec<Option<HashSet<CLit>>>` batches preserved stable
  node/literal order but produced no measurable 240-second improvement.
- Consequence-indexed `HashMap<CLit, RoaringBitmap<Node>>` batches passed an
  expanded eager-vs-batched fixpoint test over repeated conclusions and multiple
  target nodes. They reduced peak memory from 6.69 GiB to 4.71 GiB, but their
  literal-major fair schedule delayed edge feedback and regressed closure
  progress. The prototype is preserved at `23bd927` on branch
  `codex/1194-qo-dense` and is not enabled in production.
- Transposing those deduplicated bitmap pairs back into the established
  node-major application order also passed the fixpoint test. Under the exact
  predecessor-local route it timed out at 240.33 seconds, peaked at 6.68 GiB,
  and emitted zero bytes. It only delayed allocation relative to the 6.69 GiB
  node-major baseline, so it is rejected as neutral.

## Decision

None of these routes closes ontology 1194. Automatic coverage remains 591/592.
The next QO change must reduce the actual predecessor-local NF3/NF4 closure
volume while retaining the productive node-major schedule. Container swaps and
the existing residue brancher do not address the blocker.
