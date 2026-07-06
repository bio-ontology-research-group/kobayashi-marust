# ORE-2015 km vs Konclude — after in-process elc (2026-07-06)

Paired `konclude + km` panel (IBEX job 48107467) after the in-process elc
fast path (commit on payg-strategy). Compare to the morning baseline
`../2026-07-06-ore-reasoner-cmp/`.

| metric | baseline | in-process elc | Δ |
|--------|----------|----------------|---|
| **faster AND lighter (goal)** | 213/576 (37%) | **318/576 (55%)** | **+105** |
| km faster than Konclude | 214 | 318 | +104 |
| km lighter than Konclude | 366 | 425 | +59 |
| km median wall | 0.386 s (1.30×) | **0.200 s (0.97× — faster)** | halved |
| km median peak | 109 MB (0.63×) | **27 MB (0.21×)** | 4× lighter |
| sound + complete | 572 MATCH, 0 DIFF | **572 MATCH, 0 DIFF** | unchanged |
| unsolved | 8 | 8 (same) | — |

The change eliminates the portfolio-race worker forks for small EL-safe onts
(runs `elcomplete::classify` in-process, skips the race when it certifies).
Byte-identical to the subprocess elc; the gain is ~4× the ±25 noise band.
km now beats Konclude on both axes on the median ORE ontology.

Remaining gap: ~258 slower onts (non-EL near-tie band + the hard tail) and
the 8 timeouts + 45 GB disjunction memory — the konclude_ht route.
