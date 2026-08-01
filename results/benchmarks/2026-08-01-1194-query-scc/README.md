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
