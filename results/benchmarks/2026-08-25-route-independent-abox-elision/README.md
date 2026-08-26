# Route-independent certified ABox elision

This candidate operationalizes the existing
`positive_abox_tbox_separable` source theorem before worker selection. During
automatic taxonomy classification, KM removes only an ABox that the theorem
proves consistent and unable to change any public TBox subsumption. It then
admits the atomic ELC worker only if the retained normalized TBox passes both
the exact EL clause-shape screen and the RBox safety screen. Otherwise the
original complete route remains selected.

The candidate is disabled with `KM_NO_SEPARABLE_ABOX_ELISION=1` for
same-binary differential measurements. Release evidence requires exact
full-IRI signatures, consistency, unsatisfiable classes, selected-route traces,
and lower wall/RSS measurements on the affected panel, followed by a complete
592-ontology regression sweep.

The source archive SHA-256 is
`597d50ce56ba3295c5a6d8ac616af95d0e8b3f8b229685bd4ff3c38a3cd5ac32`.
Focused local and IBEX tests pass all four elision cases. IBEX-native build job
`50839889` completed with binary SHA-256
`bc0cc1c846101ad2e195cb03c7e65b07a8730a8096a6c01f31725ded740760f6`.
Focused gate array `50844598` is queued on exclusive Gold-6248 nodes. It covers
all twenty functionally confirmed inputs; superseded ten-input job `50840197`
was cancelled before allocation. No
Gold-6248 release comparison is claimed yet.

## Hardware-independent functional gate

Array `50842877` ran same-binary baseline/candidate pairs on the original ten
target ontologies. Every arm was checkpointed, returned `status=ok`, and matched the
retained full-IRI gold signature. Every candidate used less wall time and less
process-tree peak RSS. These measurements establish functional impact but do
not replace the pending exclusive Gold-6248 repetitions.

| ontology | baseline s | candidate s | baseline MiB | candidate MiB |
|---:|---:|---:|---:|---:|
| 1012 | 32.4493 | 6.0720 | 3028.83 | 694.17 |
| 1306 | 22.0790 | 4.0289 | 2231.07 | 464.51 |
| 3164 | 5.4327 | 3.4027 | 969.98 | 463.08 |
| 3658 | 6.2774 | 4.2713 | 1169.88 | 568.67 |
| 4187 | 7.3318 | 4.3767 | 1380.32 | 668.65 |
| 9958 | 6.1655 | 3.9666 | 1275.76 | 575.75 |
| 10750 | 30.4100 | 5.7841 | 2937.14 | 657.29 |
| 13482 | 35.6990 | 6.6823 | 3637.90 | 801.53 |
| 15280 | 33.6563 | 5.9741 | 3511.41 | 763.27 |
| 15725 | 2.5271 | 1.5040 | 589.91 | 250.20 |

The panel saves 135.9654 wall-seconds and 14,825.08 MiB of summed peak RSS.
Over 591 successful corpus rows, that wall saving corresponds to a
0.23006-second reduction in the arithmetic mean.

Source audit `50844190` identified ten additional large ontologies whose
top-level forms suggest the same certificate may apply. Exact same-binary
differential array `50844429` tests those inputs rather than assuming that the
profile accepts them. Each arm requires a checkpointed gold-signature match and
records the selected route, wall time, and process-tree peak RSS.

Array `50844429` completed all ten extended pairs. Every arm was checkpointed,
returned `status=ok`, matched the retained full-IRI gold signature, and used
the same candidate binary. Candidate wall sum fell from 90.2675 to 18.0060
seconds, saving 72.2615 seconds; summed peak RSS fell from 9,569.18 to 2,123.83
MiB, saving 7,445.35 MiB. Combined with the original panel, the functionally
confirmed ABox elision saves 208.2269 wall-seconds across twenty ontologies.
