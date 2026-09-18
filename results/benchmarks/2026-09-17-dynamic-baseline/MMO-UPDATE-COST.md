# MMO source-session update cost

The observed slowdown is consistent with the conservative replacement algorithm
paying maintenance costs while recomputing nearly the entire closure. Existing
evidence does not identify a correctness bug or prove which allocation dominates.
No Rust changes, additional main runs, or profiling runs were made for this review.

The analysis uses all five measured repetitions from the completed final-KM
mmo-n1, mmo-n10 and mmo-n100 histories. Warmups are excluded. Full independent
HermiT/JFact validation passed all 24 histories for mmo-n10 in audit 51985480.
The n1/n100 figures below are operational timing/receipt observations, not a
substitute for their pending independent matrix validation.

| Changes per revision | Session wall median s | Fresh wall median s | Session request/response median s | Fresh request/response median s | Paired request overhead median [min–max] s |
|---|---:|---:|---:|---:|---:|
| 1 | 21.234 | 18.266 | 8.111 | 5.667 | 2.783 [0.669–4.275] |
| 10 | 17.874 | 15.570 | 8.068 | 5.409 | 2.635 [2.576–2.725] |
| 100 | 18.085 | 15.456 | 8.129 | 5.464 | 2.696 [2.502–2.734] |

Each history has 250 updates plus its initial classification. The roughly
2.6-second request overhead is about 10.5 ms per update. Request/response time
includes frontend normalization, reasoner work and result serialization; it
cannot identify their individual CPU shares. Source canonicalization separately
costs roughly 7.5–8.5 seconds per history in both arms. It dominates a substantial
part of whole-process wall time but does not explain most of the request gap.
The broad n1 range cautions against attributing every wall-time difference to
reasoner code, especially across the recorded scheduling amendments.

All 250 updates in the examined first repetitions report el_delta. Their median
retained-fact fractions are approximately 5.6%, 5.0% and 0.6% for n1/n10/n100.
For n100, exactly 32 facts are retained in every update, while a median of 5,324.5
facts are derived beyond that retained state. These counters include internal
reflexive/top facts; they do not establish that every retained fact is a
nontrivial published subsumption or that retaining it saves time.

The receipt field invalidated_states maps to new_subsumptions + new_edges in
source_incremental.rs:1334. It therefore counts facts derived after retention,
not an independently measured count of old facts invalidated by the edit.
The review's JSON calls this quantity rederived to avoid overstating the metric.
Meaningful_incremental_update is a strategy flag, not evidence of a speedup.

Code explains why the retention fraction is small. elcomplete.rs:7325 rebuilds
an undirected symbol-dependency graph from both old and new clause snapshots,
then marks the entire connected component touched by any changed clause. The
replacement path reparses the candidate normal forms, copies only disconnected
closed rows, initializes affected rows and saturates them again
(elcomplete.rs:7533–7636). A connected class hierarchy can therefore lose most
reusable work after even one deletion. source_incremental.rs:891 also computes
stable clause deltas and reconstructs retained clause ordering. A fresh arm
needs none of this update bookkeeping.

There are concrete, broadly applicable constant-factor opportunities, but their
benefits have not been measured:

1. Precompute affected-concept/role flags once. The current membership closure
   at elcomplete.rs:7575 allocates a tagged string with format! on each lookup,
   including repeated lookups while copying and initializing rows. A table of
   identical membership results could avoid that repeated allocation without
   changing which rows are retained.
2. Avoid visiting unchanged clauses twice when constructing the dependency
   graph. The current old.iter().chain(new) scan processes the common snapshot
   portion twice. A new-snapshot plus removed-clause scan would build the same
   union only after establishing the caller's exact change-set invariant.
3. The global-change fallback normalizes the candidate before calling
   Self::new(candidate), which normalizes it again. This redundancy does not
   explain the observed all-el_delta MMO updates and should be evaluated on
   global-change controls rather than credited as an MMO improvement.

Finer dependency invalidation could retain more work, but changes the algorithm
and its proof obligations; it is not a minor representation cleanup. No special
rule keyed to MMO or to a chosen change count is justified.

If performance work is pursued, first profile identical replacement histories
on MMO and a different panel size such as HAO under Slurm, separating dependency
construction/copying from normalization and saturation. Then test a generic
representation change across all three change sizes and held-out controls,
followed by Lean certification and the release regressions. The current evidence
supports this hypothesis, not a promised optimization benefit.

Detailed five-repetition timings, receipts, paired differences and inspected
source hashes are in mmo-update-cost-diagnosis.json. Original raw evidence was
copied read-only to .work/artifacts/dynamic-mmo-update-diagnosis/.
