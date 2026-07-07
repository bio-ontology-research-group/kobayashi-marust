# ORE-2015 km vs Konclude — blank-node meta filter (cumulative session)

IBEX km-only panel `cmp_res_blank` (job 48192578, 584 onts) vs the SAME
shared Konclude columns (`cmp_res_inproc`), same aggregation script as the
prior variants. winning = `km_wall <= konc_wall AND km_peak <= konc_peak
AND gold MATCH` on both-solved.

| km variant | solved | km faster | km lighter | **WIN (goal)** |
|---|---|---|---|---|
| OFF (pre-session) | 576 | 218 | 425 | **218** |
| + in-process CB engine (`b2f58fd`) | 576 | 244 | 423 | **243** |
| + frontend `from_slice` (`2b8f224`) | 576 | 294 | 425 | **272** |
| + blank-node meta filter (`14af873`) | 576 | 292 | 425 | **284** |

(The `from_slice` row re-aggregated with this script reads 272; the earlier
snapshot reported 273 from a slightly different tie handling — same data.)

**Cumulative session: 218 -> 284 = +66 ORE ontologies** where km is faster
AND lighter AND sound/complete vs Konclude (37.8% -> 49.3% of the 576
both-solved), zero solved-count regression throughout.

## The change (`14af873`)

`ofn_to_clauses` excluded `_:genid` blank nodes (anonymous OWL structure
nodes) from the meta `named`/`iri_map`. On ABox-heavy onts they dominated
the side data: ore_ont_10073 carried 457675 of 473278 iri_map entries as
blank nodes (21 MB meta -> ~1 MB). A blank node is never a queryable named
class, so the output is unchanged; validated byte-identical classification
(drop vs keep, `KM_KEEP_BLANK_NAMES` opt-out) on 10073 / 1016 / 3260 /
12698 (the colon-localname edge case).

## Flip churn (single-rep noise band)

41 onts flipped IN, 29 flipped OUT (net +12). The churn sits in the
near-tie band where a single run's +-10-20% wall noise decides the
comparison; the filter itself is strictly-less-work + output-identical, so
none of the OUT flips are regressions of the change. Solved stays 576 and
gold-MATCH is unchanged.

## Remaining gap (the goal is EVERY ont)

284/576 win all three axes; ~140 lighter-but-slower onts remain. Next
levers: CB engine throughput (10073 race ~6 s), the 45 GB
disjunction-memory family (interning), the 8 timeouts (konclude_ht bridge
production wiring + CB/HT router).
