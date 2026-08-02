# ORE 1194 linked worked-off mutation profile

This instrumentation-only run explains why insertion-order unlinking improves
saturation throughput but still does not close ontology 1194 within the
benchmark cap. O(1) unlinking removes the historical whole-list scan cost, but
append-only dead slots increase memory and reduce locality as the run proceeds.

## Provenance

- Representation commit: `4a34d3cebf005b380dfd6b721ecbdb83fe5366e3`
- Instrumentation commit: `6dab8e70dca5aacd8554ade8f4700fefdb3d28e5`
- Source archive SHA-256:
  `d717a5c529cbc5523761d5192682a815b69e99d47dfb91412ce0de778c6672c4`
- IBEX build job: `49861846`, with `BUILD_COMPLETE`
- Binary SHA-256:
  `b2930702584d21fb1593a5a1a83ef9df926d5100eceed82c88a1e006a6fd63ac`
- Exclusive Gold 6248 profile task: `49862362_1`
- Result: failed closed after 236.0718 seconds at 14,882.34 MB

The task used the exact manual two-thread CB route with a 225-second central
cap. It produced a checkpoint, route trace, JSON result, and `TASK_COMPLETE`.
The complete captured trace and result JSON are in `evidence/`.

## Cumulative linked-store phases

| Workoffs | select (ms) | filter (ms) | mutate (ms) | head unindex (ms) | slots | live | dead |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 200,000 | 142.1 | 56.7 | 1,093.8 | 1,851.1 | 199,999 | 6,402 | 193,597 |
| 400,000 | 324.4 | 124.1 | 4,812.2 | 4,253.4 | 399,999 | 8,177 | 391,822 |
| 600,000 | 446.6 | 172.5 | 6,300.4 | 6,669.9 | 599,999 | 10,203 | 589,796 |
| 800,000 | 623.1 | 252.6 | 10,656.1 | 11,240.3 | 799,999 | 30,269 | 769,730 |

At 600,000 workoffs, these linked-store phases total 13.59 seconds. The prior
retain-based profile spent 75.27 seconds in the corresponding backward-
subsumption phases and only reached 600,000 workoffs before the cap. The linked
run reached 800,000, so unlinking materially increases throughput even though
the ontology remains unfinished.

## Next candidate

Compact the append-only linked slot arrays only when dead slots outnumber live
slots. Compaction follows the live links, preserves their exact order, rebuilds
the position map and links, and discards dead storage. This keeps normal
iteration live-only and should bound the memory and locality penalty visible at
800,000 workoffs.

