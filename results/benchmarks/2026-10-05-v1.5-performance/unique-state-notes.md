# Reuse classifier snapshots within one analysis call

The instrumented slow-case run 53332023 attributes about six seconds to possible-state collection on each of 13276 and 16680 before their timeouts. Those instrumented timings include overhead and do not prove an optimization speedup. Source inspection shows that the same immutable classifier item can be resolved repeatedly from labels on different visited nodes, cloning and sorting the same candidate vector before overwriting the same map entry.

The candidate retains the first successfully resolved state for each eligible concept within collect_possible_subsumption_states_from_classifier_references_for_snapshots. It does not retain state across analysis calls or revisions. Negated, unnamed, top, and testing-concept labels still follow the original candidate filter. Failed reference lookups are not cached.

All resolver inputs are immutable shared references during this call. The resolver reads the concept reference and testing item, clones its candidate concepts and sorts them by the same fixed concept tags. Replacing an existing result therefore writes an equal value. Skipping that replacement preserves every returned key and state, including candidate order, and changes no derivation or publication rule.

The regression covers initialized and uninitialized maps, a negative occurrence before a positive occurrence, missing references, duplicate traversal seeds, repeated labels on 32 nodes, and a successor cycle. Existing classification analyser integration tests remain required. All four exact-source production certification gates passed without sorryAx. All twelve paired diagnostic runs are independently verified. The experiment is complete, with mixed timing changes and no established isolated speedup or solved-count gain. The production-profile build completed and its full sweep is job 53334551.

| Ontology | Baseline mean (s), two repetitions | Reuse mean (s), two repetitions |
|---|---:|---:|
| ore_ont_13242 | 141.655 | 146.361 |
| ore_ont_13276 | 191.837 | 192.766 |
| ore_ont_16680 | 192.686 | 185.298 |
