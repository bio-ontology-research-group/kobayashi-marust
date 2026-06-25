# KM_HT_SHOQ promotion sweep — 2026-06-25 (unimatrix job 7399)

Full-corpus (587) validation of the gated SHOQ->fast-Ht production route
(commit `3789368`, `KM_HT_SHOQ`). Driver: the Rust `km classify` orchestrator
(`bench/km/km-shoq`, built from payg-strategy HEAD), group-safe per-ont runner
(`kmshoq_runone.py`), production defaults (fallback mode, `KM_HT_BUDGET_S=225`,
240s wall cap, 18 GB par-mem), `KM_HT_SHOQ=1`. Canonicalised + compared to the
Konclude gold sigs exactly as the gold was made (`ore_canon.canonicalize`).

Config note: this sweep set **only** `KM_HT_SHOQ=1`; it did NOT enable
`KM_HT_QO_ROUTER`, so the QO-router onts 7581 / 16444 show as timeouts here even
though that arm recovers them. Production = both flags together.

## Result

| metric | value |
|--------|------:|
| ok | 572 |
| timeout | 15 |
| gold MATCH | 571 |
| **UNSOUND** | **0** |
| incomplete-only | 1 (10702, 23 missing) |
| time (ok) | median 0.9 s, avg 10.8 s, max 226 s |
| mem (ok) | median 157 MB, avg 1124 MB, max 18.6 GB |

### The named wins (new — these time out on CB without the route)
- **10908** -> MATCH 6001/6001 (0 unsound / 0 incomplete), 225 s* / 18.5 GB
- **15672** -> MATCH 142/142, 225 s* / 18.5 GB
- canaries 10242 -> 23033/23033 (0.9 s), 10594 -> 29929/29929 (0.9 s)

\* 225 s = the fallback budget waiting out the doomed CB; the fast Ht itself
decides these in 0.2-3 s. A short SHOQ-arm budget is the speed follow-up.

### Timeouts (15) — all known-hard, none a SHOQ regression
- throughput giants (lever C): 14817, 3215, 7499, 7914, 9663, 9724
- disjunction family (inverse/card): 1603, 9540, 12653, 541
- contested gold: 10621, 15516, 2669
- QO-router onts not enabled in this sweep: 7581, 16444

## Verdict

The SHOQ route is **promotion-safe**: **0 unsoundness across all 587**, and it
recovers 10908 + 15672 (CB times out on both). The single DIFF it introduces
(10702: timeout -> incomplete-23) is a partial improvement, not a regression and
not unsound. Promote `KM_HT_SHOQ` to default-on alongside `KM_HT_QO_ROUTER`;
add a short SHOQ-arm budget so the wins land in ~3 s instead of ~225 s.

Raw per-ont records: `2026-06-25-shoq-route-sweep.jsonl`.
