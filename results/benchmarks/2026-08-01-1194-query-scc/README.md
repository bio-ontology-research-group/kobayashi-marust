# ORE 1194 unit-SCC query scheduling

This experiment extends KM's exact query-equivalence scheduler from direct
opposite named unit implications to complete strongly connected components of
the named unit-implication graph. If `A` reaches `B` and `B` reaches `A` through
unit subclass clauses, both concepts have equal interpretations in every model.
KM can classify one representative and reconstruct the non-reflexive output row
for each member. This changes scheduling only; the calculus and clause set are
unchanged.

The implementation uses iterative Kosaraju passes to avoid recursion on large
taxonomy chains. Synthetic tests cover a three-edge cycle with no directly
opposite edge, one-way paths that must not collapse, reconstructed output rows,
and the existing direct-equivalence case. The complete release suite passed:
1,834 tests passed, 0 failed, and 8 were ignored, plus all integration suites.

## 1194 measurement

Input: `/tmp/ore_ont_1194.owl`, SHA-256
`72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2`.
The frontend emitted 1,062,240 clauses. A 16-thread nominal engine diagnostic
found:

- 65,019 representative roots;
- 5,212 aliases in 3,425 nontrivial SCCs; and
- eight more aliases than the direct-opposite scheduler's 5,204.

This is exact but too small to close 1194 by itself. A separate round-robin
static partition was tested and rejected: after 90 seconds its workers reached
at most 300 roots, versus 1,150 with contiguous chunks, while peak RSS rose from
about 2.38 to 2.54 GiB. Contiguous signature locality is therefore retained.
A clause-occurrence-weighted contiguous partition was also rejected. It formed
highly uneven slices of 1,985 to 12,629 roots and reached at most 1,050 roots in
90 seconds, versus 1,150 for equal contiguous slices. Clause occurrence is not
a useful root-cost proxy here. None of these timed diagnostics completed
classification, and none is a closure or benchmark result.

Periodic `KM_QUERY_BATCH=64` fixpoints were also much worse. In 90 seconds,
workers drained 420,000 to 480,000 inter-context messages after only 64 roots
and did not progress beyond the next small batch. Deferring the message phase
until the full static slice has been seeded is essential for amortization on
this ontology, so the one-shot schedule remains unchanged.

A shared query-independent engine-base experiment was also rejected. The
prepared 1194 clause set has no CB `ground_facts` context to reuse. Calling
`run_for(&[])` therefore began the expensive empty-core top closure before any
query roots; after 55.54 seconds it had not reached query seeding and consumed
1,670,236 KiB peak RSS. The ordinary static workers had already seeded hundreds
of roots at the same point. The diagnostic gate and implementation were
removed, leaving the production scheduler unchanged.

## Residual-repair ordering candidate

The certified-EL repair previously collected every violated residual against a
round-start model and repaired the entire stale list. It could first add a
forced singleton cardinality consequence and later add the opposite side of a
covering disjunction that the singleton had already satisfied. The corrected
search processes forced heads first and rechecks each collected head before
choosing. The final closure and all-residual model checks are unchanged.

The complete release suite passes 1,835 tests, zero failures and eight
intentional ignores, plus all integration targets. A 1194 run with
`KM_ELC_CERT=repair` reached the 252-clause repair phase and progressed beyond
the formerly immediate `Q_118720`/`Q_118721` loop to later qualified-cardinality
partitions. It did not complete: timeout was 240.22 seconds and peak RSS was
5,443,724 KiB. This candidate improves the repair trajectory but does not close
1194 under the benchmark contract.

Cluster-native build job `49724345` compiled commit `ceb6f16`; binary SHA-256
was `299a4c1231f0ee9f1de5d8ecb8072908309ef9b33632b02a002dc9e85d520d2b`
for `km` and
`84fc9e2a259b8e0e8ce50dad99fd115fd7d58f0177bab61a5262549aead55a68`
for `elc`. Focus array `49725035` confirmed exact `elc_cert` signatures for
1034 and 2237 in 0.0542 and 0.0569 seconds. Forced `elc_cert` correctly deferred
on 6999; this was a poor choice of exactness control, not a default-route
regression. The source-bound 1194 row timed out after 240.0628 seconds at
5,354.42 MiB with terminal checkpointing.

Two follow-up diagnostics were rejected and removed. Preferring discretionary
cover choices during conflict attribution reproduced the same conflict order
and rebuild rate. Allowing the death-tolerant pass to empty a conflicting
canonical witness also failed to complete in 240.44 seconds and raised peak RSS
to 11,890,776 KiB. The retained implementation is therefore only the stale-head
recheck in `ceb6f16`.

A TBox/ABox decomposition probe removed all 221,086 source `ClassAssertion`
axioms, reducing the functional-syntax input from 75 MiB to 39 MiB. This tests
the first half of a possible exact class-only-ABox route: classify the TBox,
then separately certify every individual's asserted class-expression
conjunction satisfiable. The TBox-only automatic race still timed out after
240.16 seconds and reached 18,877,480 KiB combined process-tree RSS; its CB and
certified-EL workers both remained active without an answer. Stripping the ABox
alone therefore does not put 1194 within contract, so no decomposition route
was implemented.
