# Can the bulk cover repairs be made symbolic? A negative result

The repair rounds on ORE 1194 spend themselves on six clause indices, 120, 127,
134, 145, 152 and 165, each violated at roughly 366,000 nodes and each repaired
one node at a time. The question is whether that admits a symbolic repair that
satisfies the clause without materializing a concept membership per node.

It does not, and the reason is structural rather than an implementation limit.
This document records the characterization, the soundness conditions a symbolic
repair would have to meet, which of them fail and why, and what the optimization
would have been worth if it had worked.

## Characterization of the six clauses

`KM_ELC_DUMP_RESIDUAL=1` names the family of every compiled residual index. The
six are exactly the six top-level covering disjunctions:

```
residual[120] top_cover<2> nvars=1 pins=0 body=[] head=[CC]
residual[127] top_cover<2> nvars=1 pins=0 body=[] head=[CC]
residual[134] top_cover<2> nvars=1 pins=0 body=[] head=[CC]
residual[145] top_cover<2> nvars=1 pins=0 body=[] head=[CC]
residual[152] top_cover<2> nvars=1 pins=0 body=[] head=[CC]
residual[165] top_cover<2> nvars=1 pins=0 body=[] head=[CC]
```

Each is `⊤ → A ∨ B` over one variable with an empty body, so it is violated at
every alive node that carries neither disjunct. Each is also immediately
preceded by its own qualified at-most clause:

```
residual[119] at_most<=(2) role=259437 fillers=1 nvars=4 body=[CCCCRRR] head=[===]
residual[126] at_most<=(2) role=259437 fillers=1 nvars=4 body=[CCCCRRR] head=[===]
residual[133] at_most<=(2) role=259437 fillers=1 nvars=4 body=[CCCCRRR] head=[===]
residual[144] at_most<=(2) role=259437 fillers=1 nvars=4 body=[CCCCRRR] head=[===]
residual[151] at_most<=(2) role=259437 fillers=1 nvars=4 body=[CCCCRRR] head=[===]
residual[164] at_most<=(2) role=259308 fillers=1 nvars=4 body=[CCCCRRR] head=[===]
```

That adjacency is the partition itself: one disjunct is the guard of a
`≤2 R.C` bound, the other is the guard of the `≥3` witness-distinctness clauses.
The residual also holds 14 inverse role bridges at the contiguous indices 177
through 190.

The per-round model deltas confirm the covers are pure concept additions. Every
round dominated by one of the six adds about 100,000 subsumptions and zero
edges:

| round | dominating clause | violations | Δ subsumptions | Δ edges |
| --- | --- | --- | --- | --- |
| 2 | 120 | 100,000 | 100,002 | 0 |
| 3 | 120 | 100,000 | 100,000 | 0 |
| 6 | 127 | 100,000 | 100,000 | 0 |
| 10 | 134 | 100,000 | 100,002 | 0 |
| 13 | 145 | 100,000 | 100,004 | 0 |
| 17 | 152 | 100,000 | 100,012 | 0 |
| 21 | 165 | 100,000 | 100,005 | 0 |

## What a symbolic repair would have to satisfy

A cover `⊤ → A ∨ B` with an empty body is the one shape where a constant
assignment is conceivable: pick a single disjunct and declare it true across the
whole domain, recording that as one fact the residual check consults instead of
366,000 memberships. For that to preserve exact repair semantics, the chosen
disjunct `A` has to meet three conditions.

1. **EL-inert.** `A` occurs in no EL rule body. Otherwise asserting it at every
   node fires those rules at every node and the consequences are materialized
   anyway, so the symbolic form saves the storage of `A` and nothing else.
2. **Residually inert.** `A` guards no other residual clause. Otherwise the
   assertion activates that clause across the whole domain, and evaluating it is
   per-node work that the symbolic form does not avoid.
3. **Clash-free.** `A` is disjoint with nothing derivable at any node.
   Otherwise the assignment drives some nodes to `⊥`, and which ones is per-node
   information that a constant cannot carry.

Condition 3 also has a monotonicity consequence worth stating separately. The
repair's soundness argument is that a pass only ever adds, which is what makes
each pass model an upper bound on the base saturation. Today a per-node choice
is decided against the state at the moment it is applied, and a clash that
appears later drives that node to `⊥`, which removes it from the certificate
domain without invalidating anything. A constant assignment made before those
labels exist would have to be revised at the nodes that later clash. Revision is
retraction, and retraction breaks the add-only invariant the upper-bound
argument rests on. A symbolic scheme that needs it would need a new soundness
argument, and that argument is the whole value of the certificate.

## Why it fails on this residual

Condition 2 fails for **both** disjuncts of **all six** partitions. This is
measured, not inferred from the index adjacency. The dump annotates each cover
disjunct with what asserting it would activate:

```
residual[120] top_cover<2> sides=[guards{at_most},guards{pin}] nvars=1 body=[] head=[CC]
residual[127] top_cover<2> sides=[guards{at_most},guards{pin}] nvars=1 body=[] head=[CC]
residual[134] top_cover<2> sides=[guards{at_most},guards{pin}] nvars=1 body=[] head=[CC]
residual[145] top_cover<2> sides=[guards{at_most},guards{pin}] nvars=1 body=[] head=[CC]
residual[152] top_cover<2> sides=[guards{at_most},guards{pin}] nvars=1 body=[] head=[CC]
residual[165] top_cover<2> sides=[guards{at_most},guards{pin}] nvars=1 body=[] head=[CC]
```

Twelve disjuncts across six covers, and **not one is inert**. One side of each
cover guards a qualified at-most bound: asserting it everywhere activates that
bound at every node, and whether the bound is then violated depends on that
node's qualifying successor count. The other side guards the `≥3`
witness-distinctness clauses, of which the residual holds 27: asserting it
everywhere activates those everywhere.

A recogniser for symbolic partition repair would look for a cover with an inert
disjunct. On this residual it would match nothing, so no recogniser can
intercept these six clauses. The gap is in the residual's structure, not in the
recognition.

So neither side is inert, and the consequences of either choice are per-node in
both directions. This is not incidental to 1194. A cardinality partition is
precisely a pair of concepts whose whole content is the cardinality constraint
each one activates. A cover whose disjuncts were inert would not be a partition,
and the exhaustive disjoint qualified-cardinality partition this work targets is
by definition the case where the symbolic collapse is unavailable.

The condition is generic and cheaply checkable from `nfs` plus the compiled
residual, so a symbolic path could be added for covers that do pass all three
tests. On 1194 it would fire on none of the six.

## What it would have been worth

Bounded, and well short of the gate. The six covers and their at-most bounds
account for rounds 1 through 22, which cost 42.3 s of the 240 s budget, and the
apply phase inside them is 3.3 s of that. Setting the entire cover repair to
zero cost leaves:

| item | wall |
| --- | --- |
| parse, normalise, EL saturation, residual compile | 96.2 s |
| fork of the saturated structure | 1.8 s |
| six covers and their at-most bounds | 42.3 s, the symbolic target |
| first inverse role bridge, residual[177] | over 100 s, did not complete |

The first of the 14 bridges alone exceeds the whole cover budget, and 13 more
sit behind it at indices 178 through 190. A bridge `R(x,y) → S(y,x)` is violated
once per edge over a 45M-edge structure, so repairing one mirrors the role graph
and each mirrored edge fires qualified existential eliminations across it. No
amount of cover-side saving reaches that.

An extended diagnostic bounds it from below. Running the same binary to 900 s
under the same 20 GiB ceiling completes the same 22 rounds and then stays inside
round 23: the bridge repair had still not finished after more than 850 s, and
the run produced no taxonomy. That run is a cost probe, not a gate. The gate is
the 240 s row, which 1194 fails.

## Smallest next architectural step

**Sound, small, and worth doing now: cost-ordered residual scheduling.** The
search processes clauses in compiled index order, so it spends 42.3 s clearing
six covers before it reaches the bridge that decides the outcome. Ordering the
residual by an a-priori cost class, once-per-edge families before once-per-node
families, would surface the deciding clause within seconds. That does not close
1194; it converts a 240 s timeout into an early decline, which returns the
budget to the CB engine. It carries the same soundness argument as the scan
rotation already in this branch, namely that a cycle visits every clause so the
accepting verdict is independent of order, and it reuses the same cursor. It is
also testable by the equivalence property already asserted for rotation.

**What would actually close it, and is not small: per-source witnesses.** The
binding constraint is that the certificate model keeps one canonical node per
skolem function, shared across every source element. That sharing is what makes
a bridge repair mirror the entire role graph, and it is also what makes an
at-most merge contradict a `≥n` clause model-wide, which is the pathology the
partition assignment in this branch works around. Giving each source its own
witness would localize both. It changes the model construction the completeness
argument is built on, so it needs that argument redone before any measurement.
Note also that declaring the mirror edges inert is not available as a shortcut:
a separate investigation on this corpus found mirroring the relevant role
unsound over the shared-witness model.

Independently of either, the certified-EL route is not reachable on 1194 today.
`km classify` selects `nominals`, whose settings include `KM_NO_ELC=1`, and
running it with `KM_ELC_DEBUG=1` emits zero `KM_ELC_CERT` lines. Any path that
closes 1194 through this certificate needs a routing change as well.
