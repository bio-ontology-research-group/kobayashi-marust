# Compact nominal HT routing

The v1.1 automatic route sent a generated compact nominal family to the exact
nominal CB mechanism. Frontend work took about 0.08 seconds, while nominal
materialization took 8–11 seconds and roughly 1.4–2.6 GiB on the largest family
members. The existing `ht_general` mechanism independently validates complete
converted-input coverage and either returns a complete result or defers to the
unchanged nominal fallback.

A full profile census identified 25 related candidates. Paired local runs used
the frozen IBEX v5 binary
`e9f06cda45e0e9256984167b650ec6664754b81a837628d3ff63bcd0a6d06620`.
All 25 `ht_general` outputs were byte-identical to their established automatic
outputs. Four profiles were deliberately excluded because HT was slower:
ORE1340, ORE14450, and ORE3905 have more than 100 disjunctive clauses;
ORE15615 has no disjunction and fewer than 400 role assertions. ORE9014 was an
additional production-route control with no role assertions; it was exact but
slower and is also excluded.

The resulting profile gate selects these 20 ontologies:

`148, 960, 1790, 3050, 3795, 4834, 5943, 6060, 6765, 7025, 7320, 7474,
8322, 8999, 9668, 10242, 10594, 13621, 14194, 14896`.

Across those 20 order-unbalanced diagnostic pairs, automatic routing used
106.40 seconds and summed process peaks of 20,675.8 MiB. Isolated
`ht_general` used 18.76 seconds and 2,475.6 MiB, saving 87.64 seconds and
18,200.2 MiB of summed peak RSS. The most important six SHOIN(D) family
members fell from 8.8–11.3 seconds to 0.5–0.6 seconds each.

The gate is feature-based rather than ontology-based:

- 6,000–8,000 source logical axioms;
- 1,500–2,500 ABox axioms;
- no complements and at most two unions;
- a non-empty object-role ABox; and
- either at least one union or at least 400 role assertions.

Imports and rules are excluded. A source false positive cannot authorize an
answer: the normalized HT certificate remains authoritative, and a refusal
runs the exact nominal fallback. A source-bound IBEX pair panel and complete
592-ontology sweep remain required before release.
