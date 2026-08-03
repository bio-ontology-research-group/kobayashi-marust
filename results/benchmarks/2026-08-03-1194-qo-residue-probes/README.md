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
The independent grouping change was also combined cleanly with the retained
16,384-item FPROP batches and virtual role relations, with the focused
eager/batched/virtual fixpoint test passing. The gains are not additive: the
full 70,231-query exact gate reached eight million events in 45.3 seconds and
18 million in 174.8 seconds, versus 45.3 and 174.3 seconds for the virtual
baseline. It timed out at 240.14 seconds, peaked at 2,150,300 KiB RSS, and
emitted zero bytes. The aggregate is preserved on
`codex/1194-aggregate-retained` but is not merged.
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

The first isolated hypertableau-hard query, `CL_0000071`, is not itself in the
post-hoist disjunction residue. Its EL lower-bound label contains 80 reported
superconcepts, and the target name occurs in none of the 196 normalized
residual clauses. A stronger assignment-level scan is not clean, however: 245
violated residual instances bind the target node. They come from only three
forced inverse-role implications: 101 instances of the forward BFO bridge, 14
of its converse, and 130 of the forward RO bridge. The complete scan and EL
base finish in 87.13 seconds at 3,726,544 KiB, with 1,976,651,773 of the
two-billion extension budget remaining and no collection-cap hit.

A target-local prototype added those 245 forced singleton role heads and
re-entered the unchanged EL fixpoint. This avoids the million-edge global
repair and remains memory-safe, but the consequences still do not close by the
240-second production cutoff: 240.41 seconds, 8,352,092 KiB peak RSS, and zero
output. The target route therefore needs a reduction or acceleration of the
post-repair NF3/NF4 wave. It does not need global inverse materialisation,
cardinality branching, or disjunction search for this seed.

### Target dependency projection

An opt-in projection restricted post-repair EL conclusions to the forward
dependency cone of `CL_0000071`. The base model contains 1,790 nodes and
780,883 role edges reachable from that root, while only the root lies in both
its forward and backward cones. Two focused regressions verify that inactive
sources cannot enqueue conclusions and that an edge from an active source
activates its target before downstream NF4 propagation.

With residual checking still pinned to assignments containing the root, the
projected repair completed in three rounds. It added 245, 3,701, and 806 forced
role edges, respectively, reached a clean root-local check in 164.63 seconds,
and peaked at 3,836,280 KiB. The root label grew from 806 to 2,743 interned
concepts. This is a sound derivation probe, not a completeness certificate:
residual consequences at a descendant can still change a label that later
propagates back to the root.

The conservative follow-up checked every residual assignment touching any
active node. It completed the same base phase and first 245-edge repair, then
hit the 100,000-violation collection cap. Materialising that batch expanded the
active inverse-connected region and recreated the NF4 avalanche. Two opposite
disjunction policies run concurrently both timed out at 240 seconds before
reaching their first choice, at roughly 9 GiB RSS each. The only non-singleton
heads encountered before that expansion were nine unary instances from two
clauses:

```text
Q_126534(x) -> UBERON_0003898(x) or UBERON_0003899(x)       (1 instance)
Q_128321(x) -> UBERON_0002323(x) or UBERON_0004457(x)       (8 instances)
```

The result rules out physical active-cone inverse closure. A follow-up therefore
represented the mutual inverse-role pairs symbolically and composed them with
their NF4 consumers. For an
implication `R(x,y) -> S(y,x)`, it feeds a physical `R(c,d)` edge directly to
the NF4 consumers of the logical `S(d,c)` edge. Edge-first and label-first
focused tests produce the same consequence without storing the reverse edge.
The implementation screens each implication separately and leaves any inverse
role with outgoing hierarchy, reflexivity, or role-chain consumers in the
residual. It activates only after the target projection, so base completion is
unchanged.

The exact target gate still timed out. An initial version scanned all
43,893,622 physical edges after projection and reached the 240-second cutoff at
5,142,880 KiB. Replacing that scan with the exact-role predecessor index also
timed out before entering the branch phase, at 7,368,552 KiB. Fewer than ten
million ordinary worklist items were processed after projection; the cost is
the direct inverse-to-NF4 seed join over the active nodes and their incoming
relations, not reverse-edge storage or queue dispatch. Symbolic representation
alone therefore does not close 1194. A successor must prune or compose that
join by relevance to the target label rather than enumerate every virtual NF4
consequence. The prototype remains unmerged.

A grouped symbolic seed then unioned all NF4 supers per active source before
touching the completed labels. This measured **188,496,961** virtual
edge/conclusion presentations but only **2,857,789** distinct source/conclusion
pairs, a 66-fold reduction. The union itself completed immediately after the
base phase, confirming that duplicate presentation dominated the raw join.
Inserting and closing those 2.86 million genuine facts still exceeded the
remaining benchmark budget: the gate timed out at 240.34 seconds and peaked at
7,876,216 KiB before reaching residual branching. This narrows the next step
again. Batching can remove presentation multiplicity, but a complete target
route must avoid materialising facts that cannot contribute to the root's
named label, using backward rule relevance or an equivalent demand-driven
closure. The grouped prototype is also unmerged.

A sparse continuation prototype then kept the saturated base immutable and
stored only new labels in Roaring bitmaps, new NF3 edges in sparse sets, and new
NF4 propagations in a delta index. It fails closed for role chains and reflexive
roles. Two focused controls compared the base-plus-delta union with ordinary
full reclosure and matched exactly for combined NF1–NF5 behavior and
symbolic-inverse NF4.

The compact representation did not make full projected materialisation viable:

| continuation schedule | terminal evidence | peak RSS KiB | result |
|---|---:|---:|---|
| per-fact sparse delta | 240.19 s | 7,191,620 | timeout before closure |
| direct Roaring seed | 240.38 s | 8,327,828 | timeout before one million delta items |
| cloned grouped NF4 map | stopped at 123.89 s | 11,591,816 | duplicate grouped relation growing rapidly |
| all-target pending union | stopped at 146.95 s | 12,312,260 | pending target relation growing rapidly |
| one grouped NF4 bucket at a time | stopped at 151.17 s | 17,948,372 | semantic target labels approached the cap |

The last three runs were deliberately terminated by exact PID before the
20-GiB contract was endangered. None emitted `closure_complete` or a taxonomy.
The evidence separates representation overhead from the remaining semantic
volume: an exact compact overlay still cannot eagerly materialise the full
inverse-connected NF3/NF4 continuation. The next route must evaluate only
consequences relevant to the requested named root label, or construct an
equivalent demand-driven certificate, rather than building the projected model.
The overlay remains isolated on `codex/1194-sat-share` and is not production
code.

Backward relevance was then measured before building another continuation.
A conservative concept-level slice starting from named conclusions retained
2,304,600 of the 2,320,144 genuinely fresh seed facts, so concept identity alone
does not separate the useful wave. A context-sensitive magic-set census was
also too broad. Its instrumented 180-second run reached 31,411,167 demanded
pairs over 369,446 contexts after processing only 300,000 pairs. Restricting
root goals to seed-tainted named concepts produced essentially the same growth:
31,815,491 demanded pairs after 300,000 processed. Both runs remained near
4 GiB because their Roaring demand sets were compact, but neither approached a
fixpoint within the time contract.

A memoized top-down Horn prover tested existential witnesses as alternatives
instead of enqueueing all of them. On the observed new root consequence
`HP_0000001`, unbounded recursion overflowed the ordinary process stack at
109.81 seconds and 5,777,816 KiB. A 64-MiB-stack diagnostic also overflowed and
peaked at 21,779,380 KiB, outside the benchmark contract. Reordering immediate
base/seed witnesses first still overflowed. A positive-only, depth-512 variant
avoided stack growth but timed out at 180.14 seconds and 3,584,800 KiB without
finding a proof. These are search-control diagnostics, not evidence that the
consequence is absent. No top-down implementation is merged.

The retained base graph gives a different certification opportunity. For
`CL_0000071`, the forward cone has 1,790 nodes and 780,883 edges; the backward
cone has 52 nodes and 245 edges; their intersection contains only the root.
This does not by itself certify root-local repair because NF4 can propagate a
changed descendant label back along an outgoing root edge. The next exact route
therefore uses the clean root-local repair as a lower bound and a sound quotient
of the forward cone as an upper bound. Equality of their named root labels would
certify the result without constructing the full descendant continuation.

The first quotient gates preserve the root as a singleton and merge all other
forward-cone contexts by capped BFS depth. The repaired lower bound contains
217 named root consequences. A two-level quotient produced 1,465 named upper
consequences, leaving 1,248 extras in 269.03 seconds at 3,965,676 KiB. Raising
the partition to four depth levels produced 1,462 upper consequences, leaving
1,245 extras in 294.08 seconds at 3,963,760 KiB. Three removed extras do not
justify further depth refinement: most logically different descendants remain
in the final depth bucket.

A finer probe split descendants by depth, their complete EL label, and their
incoming and outgoing role sets. It stayed below the memory contract but did
not finish in 420.17 seconds, peaking at 4,386,160 KiB. Exact label signatures
therefore discard too much sharing. A middle partition used depth plus incoming
and outgoing role sets without the label vector. It produced 511 blocks and
finished in 354.63 seconds at 4,033,732 KiB, but still left 1,107 extras (1,324
upper versus 217 lower). Role position explains 141 of the original extras but
is not discriminating enough. The next partition retains role position and only
those labels that can trigger NF1, NF2, NF3, NF4, or bottom propagation. It is
designed to prevent the cross-context rule firings introduced by label union
without retaining irrelevant completed-output labels. Every such refinement is
still a sound EL upper quotient: splitting blocks cannot remove a fact from the
corresponding coarser abstraction, while unioning labels and edges within each
remaining block continues to overapproximate positive consequences.

## Decision

None of these routes closes ontology 1194. Automatic coverage remains 591/592.
The next QO change must reduce the actual predecessor-local NF3/NF4 closure
volume, now localized to the late virtual-inheritance wave of hard seeds such
as `CL_0000071`, while retaining the productive node-major schedule. Container
swaps and the existing residue brancher do not address the blocker.
