# ORE14817 production worker-count panel

This experiment compares the unchanged `production_all` portfolio with 16 and
eight workers on ORE14817. All runs use the v0.2.13 implementation binary
`31ecdbc74174e371f1f55805af8de382f517b0ab1960ed81553f6fa249c4bea5`,
one exclusive Intel Xeon Gold 6248 node, 240 seconds, and 20 GiB.

Job `50442525` ran three alternating pairs. Every result is a checkpointed
exact match with the frozen Konclude full-IRI signature.

| Route | Mean wall | Mean peak RSS |
|---|---:|---:|
| `production_all` (16 workers) | 98.3611 s | 5,209.64 MiB |
| `production_all8` | 97.6929 s | 5,206.61 MiB |

Eight workers improve mean wall by 0.68% and mean memory by 3.03 MiB. Applying
the proposed source predicate to all 592 v0.2.13 profiles selects only
ORE14817. The change is scheduling-only and leaves the exact route and all
reasoning mechanisms unchanged.

The automatic candidate gate (`50442923`) then compared v0.2.13 with the
source-bound candidate binary `c2947579daf2…` in three alternating pairs. All
six results again matched gold. Candidate mean wall was 98.5933 seconds versus
98.7509 seconds for v0.2.13, a 0.16% reduction. Candidate mean peak RSS was
5,210.34 MiB versus 5,209.55 MiB, a 0.015% increase.

Strict sweep `50443229` produced exactly 592 terminal results using the
candidate binary, with profile, route-trace, checkpoint, binary-hash, and
collision-safe full-IRI checks. It reports 591 successful classifications,
ORE1194 as the sole fail-closed error, and zero behavioral regressions against
v0.2.13. Corpus mean wall falls from 4.5871 to 4.5758 seconds, mean peak RSS
falls from 499.60 to 499.38 MiB, and median wall falls from 0.2491 to 0.2469
seconds. Median peak RSS moves from 41.45 to 41.64 MiB. The latter 0.19 MiB
increase is reported without adjustment.

The directory includes all six paired-gate rows, the 592-row automatic result
table, the strict audit, and the release comparison. The source archive and
candidate binary hashes are respectively `2ec58ba65fe6…` and
`c2947579daf2…`.
