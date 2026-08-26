# Source-filtered certified ABox parsing

The existing route-independent ABox theorem proves that a positive, consistent,
nominal-free ABox cannot change named TBox subsumptions. The v1.1 frontend used
that certificate only after constructing every ABox axiom as rich SROIQ syntax.
On the twenty large certified ORE inputs, this representation was immediately
discarded before normalization.

The candidate exposes every source node to the unchanged profile and side-data
observers but speculatively omits ABox nodes from the rich ontology. It proceeds
with that projection only when the completed existing certificate accepts. A
decline reparses the full source before normalization. A cheap source screen
excludes every known large non-separable ORE ABox before speculation; it is a
performance screen, not a semantic admission condition.

Local release-mode paired measurements produced byte-identical classification
JSON:

| ontology | ordinary wall | filtered wall | ordinary peak | filtered peak |
|---:|---:|---:|---:|---:|
| 15280 | 6.84–7.14 s | 3.49–3.81 s | 760–761 MiB | 477 MiB |
| 13482 | 7.71–8.77 s | 4.24–4.63 s | 802–803 MiB | 555 MiB |

ORE9499 is a large non-separable control. The source screen rejected
speculation; order-balanced runs were 7.76–7.98 seconds with the optimization
enabled and 7.81–7.98 seconds with it disabled, with byte-identical output.

The complete retained profile census contains 37 ontologies of at least 32 MiB
with an ABox. Exactly 20 carry the existing positive-separation certificate.
The source screen admits those 20 and rejects all 17 non-separable controls
before speculation, so no known ORE input pays for a fallback reparse.

The focused frontend suite passes 147/147 tests. Source-bound IBEX build
`50861590` completed from manifest `c0d42693844a...` and installed binary
`f4e53b0946a4...`.

Functional pair array `50861798` completed 22/22 byte-identical v5/v6 output
comparisons: all 20 certified large ABox inputs plus non-separable controls
ORE9499 and ORE10073. The 20 admitted pairs fell from 66.97 to 42.13 summed
seconds. Including the controls, the panel fell from 85.41 to 61.45 seconds;
summed per-process peak RSS fell from 10,166.66 to 8,225.86 MiB. The controls
were effectively unchanged (ORE9499 7.35/7.37 seconds, ORE10073 11.09/10.86
seconds), confirming that their complete parser path remained active.

A complete source-bound 592-ontology sweep remains required. These functional
measurements establish exactness and effect size, not the release aggregate.

The queued v6 sweep sanity task `50862184` was cancelled without allocation
after the source-bound v9 candidate subsumed this parser unchanged. The v9
full sweep is the aggregate publication gate; running both arrays would provide
no additional parser isolation beyond the completed 22-pair v6 panel.
