# ORE-2015 km vs Konclude — frontend from_slice fix (cumulative session)

Three-way IBEX comparison, all km variants vs the SAME shared Konclude run
(`cmp_res_inproc` konclude columns), same nodes/config, winning =
`km_wall <= konc_wall AND km_peak <= konc_peak` on both-solved, sound =
gold MATCH.

| km variant | solved | km faster | km lighter | **WIN (goal)** |
|---|---|---|---|---|
| OFF (pre-session: no in-process engine) | 576 | 218 | 425 | **218** |
| + in-process CB engine (`b2f58fd`) | 576 | 244 | 423 | **243** |
| + frontend `from_slice` (`2b8f224`) | 576 | 294 | 425 | **273** |

**Cumulative this session: 218 → 273 = +55 ORE ontologies** where km is
provably faster AND lighter AND sound/complete than Konclude
(37.8% → 47.4% of the 576 both-solved), with **zero solved-count
regression** (576 throughout) and both changes A/B-verified same-conditions.

## The two levers

1. **In-process CB engine** (`b2f58fd`, +25): small non-EL onts run
   `Reasoner::{new,saturate,subsumptions}` as a library call, skipping the
   engine-worker fork + clause-JSON stdin round-trip. Byte-identical.
   Gated on `!has_internal_definer_disjunction()` (the CB memory-blowup
   signature) so a budgeted-detach worker can never OOM the fallthrough —
   this gate is what kept solved at 576 (an earlier ungated version had
   +54 winning but −2 solved from OOM on 9635/12698). See
   `../2026-07-07-inproc-engine-safe/`.

2. **Frontend `from_slice`** (`2b8f224`, +30): the frontend parsed its
   `--meta` file with `serde_json::from_reader(File::open(...))` — the
   classic unbuffered-reader trap. On a large ont (ore_ont_10073: 21 MB
   meta, 473k iri_map entries) that took ~14 s vs <1 s from a read buffer
   with `from_slice`. Semantically identical (same deserialization), pure
   performance: 10073 frontend 19 s → 5 s, total 27 s → 13 s, peak
   unchanged. Because every large ont carried this overhead, the earlier
   panels understated km's standing; the fix both improves and corrects.

## Remaining gap (the goal is EVERY ont)

273/576 win all three axes. km is already lighter on 425/576 (74%); the
binding constraint stays SPEED (faster on 294). ~150 onts remain
lighter-but-slower — the flip targets. Next throughput levers:
- the ofn subprocess is still ~5 s producing a 21 MB meta (473k entries) —
  the meta may be reducible (does the pipeline need all IRIs or just
  declared/named classes?) and the clausification may over-expand;
- the CB engine race is ~8 s on 10073 — engine throughput;
- the 45 GB disjunction-memory family (interning) and the 8 timeouts stay
  the hard tail. Konclude's 0.05-0.5 s bar on most onts keeps "beat on
  every ont" a very high bar.
