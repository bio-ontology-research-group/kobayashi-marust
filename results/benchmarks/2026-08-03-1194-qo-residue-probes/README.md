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
- A path-level trace found 265.5 million ordinary NF4 propagation presentations
  by 111 seconds. Only 18.8 million were unique pending writes, 115.8 million
  already existed in node labels, and about 130.9 million were duplicate
  presentations within the wave. The same run had already performed 329.6
  million inverse-edge KPSet containment checks. This identifies both sources
  of repeated work rather than attributing the timeout to container overhead.
- A persistent `(role,target)` consequence bitmap plus per-source bulk bitmap OR
  preserved the tested eager/hash-batch fixpoint and the node-major application
  schedule. It nevertheless timed out at 240.26 seconds, peaked at 7.25 GiB,
  and emitted zero bytes. Retaining vectors and the parallel bitmap index cost
  more than the avoided hash insertions, so this layout is also rejected.
- Deferring inverse-edge KPSet checks into the same per-node bitmap union also
  preserved labels and the insufficiency result on a focused load-bearing
  inverse control. On 1194 it still timed out at 240.20 seconds, peaked at
  7.16 GiB, and emitted zero bytes. Avoiding repeated containment lookups is not
  enough while the route still materialises the predecessor-local inverse-role
  consequence volume.

## Composed-forward FPROP micro-batches

The alternative `INVCOMPOSE + FPROP + SAT + KPSET` representation removes most
reversed edges. Its eager profile made 77.5 million `fprop_emit` calls and 81.4
million `add_lit` calls by 35 seconds while keeping about 70,000 literal events
live. A result-preserving FPROP batch reduced these repeated presentations, but
an end-of-wave batch starved forward feedback and grew the model to 186,000
nodes and 8.6 million queued edges.

Bounded micro-batches retained feedback. Thresholds 4,096, 16,384, 32,768, and
65,536 were profiled; 16,384 gave the best measured balance. At about 35 seconds
it held 91,259 nodes and 2.23 million edges with only 4.55 million `add_lit`
calls. The exact 240-second gate still timed out, emitted zero bytes, and peaked
at only 2.08 GiB. A 180-second trace showed genuine closure volume remained:
99,592 literal events and 4.20 million edges were queued at 174.6 seconds after
a later node-growth wave. The opt-in prototype is preserved at `9d99a68` on
branch `codex/1194-fprop-batch`; it is not enabled or merged into production.
A transient-bitmap variant kept only each current 16,384-item micro-batch in
positive/negative Roaring bitmaps. It preserved the focused fixpoint but reached
four million literal pops at 46.6 seconds, versus 45.4 seconds for the hash
micro-batch at the same model state. Bitmap container overhead therefore loses
at this bounded wave size; the variant is rejected and not preserved.
Grouping each guard's FPROP rules by role removed repeated scans and allocations
of the same source successor list. It preserved the exact trace state and moved
the four-million-literal marker from 45.4 to 44.2 seconds, only a 2.6% gain and
far too little for the remaining closure. Prototype commit `574d9c3` on branch
`codex/1194-fprop-grouped` is not merged. Adding an exact membership set for
materialised `(role,source,conclusion)` forward links left the marker unchanged
at 44.2 seconds and raised short-profile RSS to about 1.77 GiB. Most links are
fresh, so linear duplicate checks are not the bottleneck; the index is rejected.

## Decision

None of these routes closes ontology 1194. Automatic coverage remains 591/592.
The next QO change must reduce the actual predecessor-local NF3/NF4 closure
volume, especially the inverse KPSet containment workload, while retaining the
productive node-major schedule. Container swaps and the existing residue
brancher do not address the blocker.
