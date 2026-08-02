# ORE 1194 under the CB engine: where the time actually goes

Host `leechuck-office`, single-threaded (`KM_THREADS=1`), `systemd-run
MemoryMax=24G`, payload `/tmp/1194.clauses.json` (1,062,240 clauses, 70,231
named classes, 65,019 of which the engine takes as query roots).

## The premise this cycle started from was wrong

The brief attributed 1194's CB wall to root seeding (300 s for 2,850 of 70,231
roots). A profile of this HEAD does not reproduce that. Seeding runs at roughly
330 roots/s: a 320 s run reaches 57,050 of 65,019 roots and 8.9 M pending
messages at 9.3 GB, i.e. seeding alone would finish in about 195 s.

The decisive measurement is the opposite one. With **zero** query roots
(`KM_QUERIES=__none__`, so `run_for` seeds only the mandatory ⊤ context) the run
still does not converge:

| wall budget | contexts | Succ msgs | Pred msgs | peak RSS |
| --- | --- | --- | --- | --- |
| 150 s | 1,317 | 214,946 | 5,785,053 | 2.2 GB |
| 900 s | 1,874 | 1,033,246 | 17,746,753 | 6.7 GB |

No query-side strategy — shared multi-query saturation, root-context reuse,
query batching, told-subsumer equivalence, or an EL lower closure handed to the
roots — can close 1194, because classifying nothing at all already exceeds the
240 s budget by more than 4x. The cost is the successor-graph message fixpoint,
not the roots.

## What drives the successor fixpoint

The frontend emits six top-level covering disjunctions (`⊤ ⊑ Q_a ⊔ Q_b` with
`Q_a ⊓ Q_b ⊑ ⊥`), the excluded-middle pairs of six qualified max-cardinality
restrictions. They are ontology *facts*, so every context derives them, every
context derives the disjunctive existential trigger on the `≥n` side, and every
context therefore becomes a predecessor of the same six successor contexts.

`pred-hub-senders.txt` (`KM_MSGPROF`) shows those six contexts, ids 1–6, as the
senders of **56.5 %** of all Pred traffic, each with 2,010–2,660 predecessor
edges and a 545–885 entry pred pool.

`hyper-cardinality-products.txt` (`KM_TRACE_HYPER_PRODUCT=1000000`) shows the
other half of the shape: the `≤2 R.C` clause normalises to a seven-atom body
with three neighbour variables,

    C(z1) ∧ C(z2) ∧ C(z3) ∧ D(x) ∧ R(x,z1) ∧ R(x,z2) ∧ R(x,z3) → z2≈z1 ∨ z3≈z1 ∨ z3≈z2

whose premise candidate widths reach `[1, 20, 20, 3, 3, 58, 58]` — 12.1 M
selections for a single firing. 585 firings with a product of at least 1e6 occur
in one 190 s run.

## Attribution of the message-fixpoint time

`KM_PROF_TIME` with the added `add_clause` split, at the identical fixpoint
point `guard=4,000,000`:

| phase | ms |
| --- | --- |
| Pred arrival (join + insert) | 77,625 |
| ↳ `add_clause` | 70,256 |
| ↳↳ **forward subsumption** | **65,392** |
| ↳↳ index maintenance | 1,963 |
| ↳↳ arena intern lookup | 892 |
| ↳↳ back subsumption | 530 |
| Pred payload (sender half) | 570 |
| propagate | 2,036 |

Forward subsumption was 84 % of clause insertion and 79 % of the whole
message-fixpoint time. The payload half is 0.7 %, so memoising the
receiver-independent `pred_payload` — an obvious-looking candidate — is worth
nothing here and was rejected on this evidence.

The other structural number: 5.87 M Pred conclusions land in only **189,541**
distinct interned clauses across 6,322,632 per-context clause slots, a 33x
content replication factor between contexts.

## What landed

### 1. Dense subsumption screen (`ClauseSig`)

Both subsumption directions ask two set inclusions. `ClauseSig` stores, in a
flat array parallel to the clause arena, the two multiset sizes and a 64-bit
Bloom signature per component. `a ⊆ b` implies `|a| ≤ |b|` and
`sig(a) & !sig(b) == 0`, so a candidate failing either test provably cannot
subsume and is skipped without touching the clause. Surviving candidates still
run the exact `strengthens` check, so the accepted set is unchanged.

The win is memory locality: a long posting-list scan reads 24 dense bytes per
candidate instead of chasing a `ContextClause`'s two heap vectors.

Measured at `guard=4,000,000`, same run, same state:

| phase | before | after | factor |
| --- | --- | --- | --- |
| forward subsumption | 65,392 ms | 11,968 ms | **5.47x** |
| `add_clause` | 70,256 ms | 16,154 ms | 4.35x |
| Pred arrival | 77,625 ms | 22,723 ms | 3.42x |

### 2. Left-deep antichain join in local Pred

`pred_from_neighbor` already computed Sequoia's Pred antichain as a left-deep
join, dropping redundant partial unions after each premise. `pred_local_inner`
still enumerated the whole premise product and pushed every element through the
redundancy trie. Stack sampling of the stalled run put three of five samples
inside `RedundancyTrie::remove_supersets_from` under `pred_local_inner`, in a
single call that ran for over 100 s without returning.

Local Pred now uses the same staged join, with the same justification: if
partial `P` strengthens `Q` then `P ∪ R` strengthens `Q ∪ R` for every choice
`R` from the remaining premises, so every pruned extension has a stronger
extension in the full product. Products of at most 64 selections keep the direct
enumeration (staging costs more than it saves there), and `KM_SPLIT`'s
Direction-B mode keeps it too because its disjunctive-premise count is a
property of a whole selection.

At equal 900 s budget and the identical fixpoint point (`guard=18,780,000`,
1,874 contexts, 17,746,753 Pred messages in both):

| phase | product enumeration | staged join |
| --- | --- | --- |
| local Pred | 161,688 ms | 135,469 ms |
| saturate (total) | 277,922 ms | 253,706 ms |

## Fixpoint equivalence evidence

Both changes are scheduling/redundancy-filtering changes, not calculus changes,
so no Lean re-certification applies. Empirically, on this 1.06 M-clause
ontology, the derived state is identical before and after at the same message
count:

| counter | baseline | after both changes |
| --- | --- | --- |
| Pred conclusions | 3,991,898 | 3,991,898 |
| new-in-receiver | 3,956,671 | 3,956,671 |
| arena (successor domain) | 89,318 | 89,318 |
| arena (root domain) | 14,436 | 14,436 |
| interned Pred clauses | 65,994 | 65,994 |
| context clause slots | 4,480,407 | 4,480,407 |
| contexts / Succ / Pred msgs | 1,317 / 94,205 / 3,905,794 | identical |

Unit-level guards are in `engine.rs`: the screen has a no-false-negative
property test, a selectivity test, oracle-equality tests against unscreened
forward and backward subsumption, and an arena/mirror drift test; the join has
an oracle-equality test against a retained full-product reference implementation
over 40 randomised premise populations plus the wide-premise shape.

## Files

- `zeroq-baseline.err` — zero-query profile before the screen (150 s cap).
- `zeroq-screened.err` — same run after both changes.
- `pred-hub-senders.txt` — `KM_MSGPROF` top Pred senders.
- `hyper-cardinality-products.txt` — `KM_TRACE_HYPER_PRODUCT` firings.
- `900s-no-join-port.txt`, `900s-with-join-port.txt` — the 900 s A/B.

## Standing conclusion for 1194

1194 stays out of reach of the CB engine at 240 s / 20 GiB, and the reason is
now measured rather than assumed: six global covering disjunctions from
qualified cardinality restrictions make every context a predecessor of the same
six successor hubs, and the resulting Pred fixpoint is tens of millions of
messages over a context graph whose clause content is 33x replicated. The next
lever that could change the order of magnitude is structural sharing of that
replicated content between contexts (a base-plus-delta context clause set), not
another query-scheduling strategy.
