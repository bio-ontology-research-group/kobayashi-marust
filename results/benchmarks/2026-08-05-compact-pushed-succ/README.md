# Rejected compact `pushed_succ` set

This local candidate replaced each CB context's `HashSet<Pred>` successor-push
deduplication set with a sorted `Vec<Pred>`. Binary-search membership and
insertion preserved the exact set and deterministic predicate order. The
candidate remained isolated on branch `codex/compact-pushed-succ`; it is not
enabled or merged.

## ORE4669 paired gate

Both alternating single-thread pairs produced byte-identical 16,886,076-byte
output with SHA-256
`055cb5f2481c778e5ed137dddccd2201e04d45c05a472b42eb54119cdc331ac2`.

| order | compact-trigger baseline | compact `pushed_succ` |
|---|---:|---:|
| baseline then candidate | 20.90 s / 1,774,256 KiB | 21.12 s / 1,762,276 KiB |
| candidate then baseline | 21.09 s / 1,775,088 KiB | 21.39 s / 1,757,740 KiB |

The vector saved 11.7–16.9 MiB but consistently slowed this high-volume CB
case by 1.1–1.4%. Sorted insertion shifts enough predicates to offset the
smaller representation.

## Equal-progress ORE1194 gate

At the 60-second cutoff both binaries reached exactly the same query count,
context count, pending-message count, saturation-call count, and detailed
200,000-iteration checkpoint. Peak RSS fell from 4,710,016 to 4,656,008 KiB,
52.7 MiB or 1.15%. Neither run emitted output.

## Decision

Reject the candidate. Its memory reduction is modest after compact central
trigger sets, while the completed ORE4669 workload shows a repeatable wall-time
regression. No IBEX panel or corpus sweep is warranted. Keep hash-based
`pushed_succ` membership in the default route and target a larger retained
allocation category without insertion shifting in the next iteration.
