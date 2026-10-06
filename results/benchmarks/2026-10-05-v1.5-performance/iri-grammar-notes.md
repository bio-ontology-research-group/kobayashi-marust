# Cached full-IRI validation experiment

Production validation remains unchanged unless `KM_FAST_IRI_GRAMMAR` is set. This candidate validates every distinct full-IRI spelling with the original grammar and caches only successful checks within one document. Structural parsing still traverses the complete input. Any structural failure, invalid IRI, or description-graph construct invokes the original validator, preserving its exact refusal text.

The copied grammar differs only in FullIRI token recognition; a unit test enforces that restriction. The cache does not change normalization, inference rules, or publication. Whole-corpus equivalence and exact-source production certification remain required before promotion.

## Local diagnostic evidence

The direct grammar probe uses four alternating repetitions per source. All twelve paired results agree exactly. Grammar time falls by approximately 60–70% on these three sources. The earlier validation-cost probe identified grammar validation as the main conformance cost on two of these sources. These are bounded workstation diagnostics, not release benchmark results.

The classification comparison uses the same pinned binary with the flag off/on, two repetitions in alternating order, one CPU, 30 seconds and 20 GiB per attempt. All twelve answers agree with an independently retained full-DL result.

| Ontology | Original wall times (s) | Cached wall times (s) |
|---|---|---|
| ore_ont_236 | 0.4127, 0.2584 | 0.1932, 0.1934 |
| ore_ont_11896 | 0.2395, 0.2543 | 0.1751, 0.1746 |
| ore_ont_3250 | 0.2404, 0.2335 | 0.2406, 0.2375 |

The first original run on 236 includes a substantial cold-run effect. Both repetitions improve on 236 and 11896; 3250 has no established end-to-end gain. No full-corpus mean, median, or solved-count improvement is claimed.

## Pending corpus check

IBEX Slurm job 53332675 checks all 1,920 frozen inputs, including the 212 refused inputs. Each grammar arm has 240 seconds and 20 GiB, one CPU. Exact result text, including errors, must agree; timeouts and process failures remain unresolved evidence. This check concerns grammar equivalence, not complete OWL admission, taxonomy correctness, or Lean certification.
