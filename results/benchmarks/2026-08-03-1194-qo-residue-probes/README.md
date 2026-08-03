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
A true role-grouped bulk-union prototype ORed each guard's whole positive and
negative conclusion bitmaps into every current successor batch. The naive form
replayed conclusions already present in node labels: it reached two million
literal pops at 7.3 seconds, then inflated `add_lit` from 5.5 million at eight
seconds to 20.2 million at 54.6 seconds without reaching four million pops. A
second form maintained an exact positive/negative bitmap mirror of every node
label and subtracted it after each union. That removed the replay, but bitmap
maintenance on every genuine label insertion dominated instead: after 55.1
seconds it had processed only two to four million literal pops, 2.20 million
edges, and 4.46 million `add_lit` calls. It did not reach the hash route's
four-million-pop marker at 45.4 seconds. Both forms passed the focused
eager/hash/bitmap fixpoint comparison, but are rejected as substantially slower.
The uncommitted experiment remains isolated in worktree/branch
`codex/1194-fprop-bulkor`; no Roaring dependency or source change is merged.

## Virtual role relations

An edge-role census at four million literal events found 2,575,019 stored
edges. Three roles accounted for 2,326,114 of them (90.3%): `BFO_0000050`
(role 0, 932,811 edges), `RO_0002202` (role 8, 701,364), and
`UBREL_0000002` (role 40, 691,939). Their remaining clauses after NF4 capture
were only simple role inclusions plus the inverse bridge already handled by
`INVCOMPOSE`; none was a cardinality consumer.

The opt-in `KM_HT_QO_VIRTUAL_EDGES` prototype stores roles with no residual
generic consumer as compressed incoming source bitmaps plus compact outgoing
target lists. It applies captured `prop`/`fprop` links directly and recursively
materialises exact same-orientation role-super aliases. Role-chain participants,
FCHECK, and PSPLIT remain physical. A focused eager/physical/virtual fixpoint
test passes. Capturing the role aliases made roles 0, 8, and 40 virtual: at eight
million literal events only 11,491 physical edges remained, versus 2.58 million
at four million events on the hash-microbatch route.

Eager inheritance over the compressed relation exposed 379 million duplicate
`add_lit` presentations by 60 seconds. A bounded 16,384-item node-major virtual
inheritance batch reduced this to 14.1 million (27-fold) and moved the
eight-million-event marker from 55.2 to 45.3 seconds. The exact 240-second gate
still timed out, emitted zero bytes, and remained near 2.0 GiB RSS late in the
run. Prototype commit `6b02747` is preserved on branch
`codex/1194-sat-share`; it is not merged pending broader semantic controls and
an actual 1194 closure.
A 180-second trace confirms the remaining work is a genuine large fixpoint:
18 million distinct literal events had completed at 174.3 seconds, with 81,307
nodes, 41,670 physical edges, and 127,321 literals still queued. Increasing the
virtual batch threshold from 16,384 to 65,536 delayed the eight-million-event
marker from 45.3 to 53.1 seconds, so feedback starvation returns at the larger
wave. Replacing immutable trigger-posting remove/reinsert operations with `Rc`
postings left the 45.3-second marker and model state exactly unchanged; that
constant-factor variant was discarded.

Naive query sharding does not isolate this closure. A round-robin quarter of
the 70,231 query seeds still timed out at 240 seconds and grew to roughly the
same 2 GiB range, because lazy clause expansion recreates most of the shared
model. A one-query diagnostic reduced the precompute to about 6,400 nodes, but
then accumulated 38,529 parked disjunctions at 53 seconds and was still cycling
through later saturation/residue waves at the 120-second cutoff. Parallel
output-query shards would therefore duplicate the expensive closure rather than
divide it; only a true clause-dependency component split could help.

Eagerly closing pure unary concept implications while suppressing worklist
events for literals without another indexed consumer also regressed. The
prototype preserved label insertion, clashes, role-guard re-fire, and events
for concept, propagation, and disjunction consumers. It nevertheless converted
the useful interleaved schedule into a large initial burst: at 59.2 seconds it
still held 2,984,821 literal events, versus 106,905 for the virtual-relation
baseline at 59.3 seconds. It reached eight million processed events at 43.0
seconds versus 45.3 seconds, but only by eagerly creating 8.33 million label
presentations and advancing to a different, larger intermediate model. This is
not a closure reduction and is rejected rather than integrated.

Positive unary-implication SCC quotienting found 53,836 nontrivial components
covering 111,745 of 382,846 concepts; 59,081 of 70,231 query concepts belong to
one of them, but the largest component has only 14 members. Representative
remapping reduced the unique query roots to 64,986 and moved the eight-million
event marker from 45.3 to 42.9 seconds. The exact combined route still exited
at the 240-second cutoff with zero output, so quotienting alone is insufficient.

The one-query residue was much more concentrated than its raw size suggested.
Six global binary disjunctions each parked on all 6,420 live nodes at the phase
change, accounting for 38,520 of 38,529 parked instances. Each cover clause
`P or N` has a matching disjointness clause `P and N -> bottom`; the fresh `N`
concept occurs only in concept-literal positions. Rewriting `N` as signed
`not P` and removing those twelve tautological cover/disjoint clauses is
therefore exact. It makes the original easy one-query diagnostic certify over
eight nodes immediately instead of expanding to 6,435 nodes, but the complete
70,231-query run, with and without SCC quotienting, still timed out at exactly
240 seconds and emitted zero bytes.

Complement elimination changes the earlier sharding result. Prefixes of 10,
100, 250, 375, 437, 468, and 476 queries certified with nonempty output in 5,
5, 5, 6, 29, 36, and 36 seconds, respectively; prefixes of 500 and 1,000 timed
out. The first isolated hard seed is query position 477, `CL_0000071`: it times
out alone at 60 seconds, while adjacent isolated queries 476 and 483 certify in
five seconds. Its trace reaches 6,125 nodes, then a late virtual-inheritance
flush raises the literal queue from 11,798 to 1,195,980 at about 55 seconds.
This establishes a useful routing boundary: normalized easy queries can be
batched, while the hard seeds require a separate reduction of the virtual NF4
inheritance wave.
The flush is not passive output payload. A consumer census over the isolated
hard-seed trace observed 432 full virtual micro-batches containing 7,115,533
distinct node/literal pairs in total. Every pair's literal keys a downstream
concept, propagation, role-guard, or disjunction consumer. The late queue jump
therefore accumulates genuine eventful NF4 closure. Shared passive labels or a
container-only rewrite cannot remove it; the next prototype must compose or
quotient trigger chains before those pairs are materialised.

A direct index for pure `C(X) -> exists R.F(X)` clauses passed a focused
generic-versus-fast fixpoint comparison and reduced generic `apply_head` calls
on the isolated hard seed from about 2.98 million to 202,000 by the late wave.
It did not move any wall-time, event, node, or queue marker: eight million
literal pops remained at 46.7 seconds and the 1.20-million-item late queue
appeared at 55.3 seconds. Suppressing existential-only literal events and
creating their edges eagerly also preserved the focused fixpoint, but regressed
the productive schedule: two million pops moved from 6.8 to 11.9 seconds and
`add_lit` presentations reached 19.1 million by 53.7 seconds. Both variants are
rejected; generic head dispatch is not the bottleneck.

The retained 1194 frontend clause set was also tested against the existing
near-EL certificate routes. Ordinary EL completion deferred in four seconds.
`KM_ELC_CERT=1` performed substantive completion but declined with exit 3 after
85 seconds and emitted no output. `KM_ELC_CERT=2` was still repairing at the
exact 240-second cutoff and exited 124 with zero output. The current EL
certificate therefore cannot supply a certified taxonomy or partial seed under
the benchmark contract.

The EL saturation itself is nevertheless a useful lower bound. With profiling
enabled it completes in 83–84 seconds and derives 78,387,044 subsumption facts
plus 43,893,622 role edges. Its original residue marks all 499,871 concepts
insufficient only because the same six top-level cover clauses touch every
canonical node. Omitting those six covers and their matching disjointness
clauses from the EL *lower-bound input* is sound (it removes axioms rather than
asserting an approximation). The resulting EL completion is unchanged, while
the disjunction residue falls to 303 subjects after common-disjunct hoisting,
from 499,871 before omission.

This lower bound is not yet a certified partial classification. Plain
certificate checking still fails at the first of 196 residual clauses after
85 seconds. Repair reaches the residual phase but records the 100,000-violation
collection cap in its first round (`97,373` additions and `17` merges), then
times out at 240 seconds with zero output. A hybrid must therefore compute the
subjects affected by *all* violated residuals, not assume that the 303
disjunction-affected subjects are the entire exact tail.

A one-round census with a one-million-violation ceiling confirms that this tail
is not small. It reaches the cap after touching 72,107 canonical nodes and
28,174 named concepts; 144 residual clauses have already been violated at that
point. One clause accounts for 997,025 of the first million violations:
`BFO_0000050(x,y) -> BFO_0000051(y,x)`, one direction of a mutual inverse-role
pair. The next largest residual contributes only 2,106 violations. The census
finishes in 84.73 seconds at 3,756,508 KiB peak RSS, so this concentration is a
measured property of the completed lower-bound model rather than a timeout
sample.

An opt-in prototype scheduled all twelve forced inverse implications from the
six retained mutual pairs directly on EL edge creation. This is the bulk form
of the role-head additions that certificate repair otherwise performs one
violating assignment at a time. Focused tests confirmed exact swapped-wiring
recognition and terminating reciprocal closure. On the no-cover 1194 lower
bound, however, the reciprocal edges activate enough downstream EL propagation
to time out at 240.51 seconds, peak at 23,373,876 KiB RSS, and emit zero bytes.
Materialising the inverse closure is therefore rejected. A useful successor
must treat the dominant BFO pair symbolically or avoid completing irrelevant
inverse consequences; merely batching the same edge set exceeds both benchmark
limits.

## Decision

None of these routes closes ontology 1194. Automatic coverage remains 591/592.
The next QO change must reduce the actual predecessor-local NF3/NF4 closure
volume, now localized to the late virtual-inheritance wave of hard seeds such
as `CL_0000071`, while retaining the productive node-major schedule. Container
swaps and the existing residue brancher do not address the blocker.
