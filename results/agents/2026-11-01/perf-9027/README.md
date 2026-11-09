# perf-9027: ore_ont_9027 lost against v1.5.3 (v1.5.5 S1 blocker)

Agent `perf-9027`, branch `fix/v155-perf-9027` from `development/v1.5.5` at
775223bf. All runs on ws, release flags (`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1
KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1
KM_FAST_IRI_GRAMMAR=1`), `KM_THREADS=1`, one CPU per run with `taskset`,
`classify --lines` (`scripts/run.sh`).

## Binaries

| Name | What | sha256 / origin |
|---|---|---|
| v1.5.3 | `.work/v153-release-assets-b5abf83a/km-v1.5.3-linux-x86_64` | release asset |
| v1.5.4 | `.work/v154-release-assets-80c8f82a/km-v1.5.4-linux-x86_64` | release asset |
| RC | `.work/pgo-v155-preview/km-v1.5.5-rc-pgo` (775223bf, PGO) | `5cd65bba…` |
| fix | `km.pgo.fix2`: a2307f7d built like the RC (LTO, one codegen unit, `mimalloc`, the RC's `merged.profdata`; `scripts/pgo-build.sh`) | `d472be8b…` |

The fix binary uses the RC's profile, which is stale for the changed
functions; the release pipeline re-collects it.

## Cause

Two v1.5.4/v1.5.5 changes, both found by phase timing (`KM_TIMING`,
`KM_BRIDGE_PHASE_TIMING`, `KM_OFN_TIMING`) and bisection over the agents'
binaries (`forced-nominal-data-misses/km.base` fast, `km.fix2` slow):

1. **Bridge, 0520da9d (forced-nominal-data-misses), the timeout.** The
   satisfiable expander cache is not installed when the bridge consumes a value
   singleton. 9027 has two (the `xsd:boolean` cover of its data property
   ranges) but no construct that creates a data successor. Its 105,658 bridge
   subjects ran without the cache: 0.17 s per subject against 1.5 ms (v1.5.4),
   250 s timeout. Fix: `konclude_ht/value_singletons.rs` proves by a least
   fixpoint over the bridge input that no singleton can enter any label; then
   the cache stays (bfef97f3). Exactness and the run-time audit:
   docs/DATATYPES.md, "Inert value singletons keep the satisfiable expander
   cache".
2. **Frontend, v1.5.4 object/data sorts (`frontend/sorts.rs`), 4 s.** The
   sort pass added 138,121 clauses in 4.05 s (RC) on 9027, against 2.7 s for
   the whole v1.5.3 frontend. Fix: the same passes over interned ids, 0.91 s
   (a2307f7d). Output unchanged: docs/NOMINALS-CB.md section 6,
   "Implementation note".

The 138k sort clauses themselves stay (306,558 to 444,464 HT clauses); with
the cache back the bridge takes 27.2 s against 27.6 s for v1.5.3.

## 9027 times (s, wall)

| Placement | v1.5.3 | fix |
|---|---|---|
| fix on CPU 14, v1.5.3 on 13 (5 pairs) | 32.0, 32.1, 31.8, 31.5, 32.6 | 36.2, 32.5, 34.6, 32.3, 32.0 |
| fix on CPU 13, v1.5.3 on 14 (2 pairs) | 33.2, 33.0 | 30.1, 30.2 |

Mean 32.3 s (v1.5.3) against 32.6 s (fix), ratio 1.01; worst pair 1.13 with
the fix on the slower CPU. Same 667,615 subsumptions, `CONSISTENT 1 DROPPED
0`, sorted outputs byte-identical to v1.5.3 in every run. RC: 250 s timeout;
non-PGO head build 260 s timeout. Phase split (one pair): frontend 2.93 s
against 2.14 s, bridge 27.2 s against 27.6 s, total 32.3 s against 31.5 s.

CPU 14 is slower than CPU 13 on this host: swapping the placement of the
non-PGO head and fix builds on ore_ont_5289 swapped which of them was faster
(29.0/28.9 against 31.7/34.0, then 35.1/33.4 against 30.3/30.7).

## ore_ont_15687

Not slower on ws: v1.5.3 111.2 s, fix 104.9 s (same answer); the preview
cert run had RC 100.7 s against v1.5.3 110.2 s. Its Ibex timeout is not
reproduced on ws; standalone `km ofn` under `KM_NOMINALS=1` exceeds 120 s for
both RC and fix.

## Thirty slowest held-out inputs

`timing/slow30.txt`: the 30 held-out inputs of the preview with the largest
answered wall time (v1.5.3 same day or candidate), plus the two other lost
inputs 13077 and 13584. `timing/slow30-v153-vs-fix.tsv` (`scripts/pair30.sh`:
v1.5.3 on CPU 13, fix on CPU 14, 240 s; columns input, v1.5.3 rc, wall, fix rc,
wall, sorted output equal). Every input slower than 1.10 of v1.5.3 was rerun
against the RC with the fix on the faster CPU (`timing/flagged-rc-vs-fix.tsv`,
`scripts/pairrc.sh`):

| Input | v1.5.3 | fix (CPU 14) | RC / fix, fix on CPU 13 |
|---|---:|---:|---|
| 12898 | 34.1 | 50.9 | 53.0 / 48.6 |
| 1673 | 70.2 | 124.2 | 124.7 / 115.3 |
| 14572 | 33.9 | 43.6 | 37.0 / 28.6 |
| 9240 | 41.4 | 52.8 | 53.1 / 49.2 |
| 205 | 53.1 | 88.9 | 84.4 / 79.2 |
| 1938 | 39.1 | 67.2 | 73.3 / 63.9 |
| 12567 | 20.4 | 30.7 | 30.6 / 28.2 |
| 13928 | 15.1 | 26.7 | 25.4 / 24.4 |
| 5218 | 9.1 | 11.3 | 9.6 / 9.6 |
| 5289 | 18.9 | 31.8 | 24.5 / 23.0 |
| 762 | 2.6 | 3.1 | 3.1 / 2.9 |
| 10754 | 8.4 | 24.8 | 25.4 / 24.5 |
| 15226 | 13.7 | 22.8 | 21.4 / 21.3 |

None of these is slower because of this change: the RC is as slow or slower
in every case (base regressions of v1.5.4/v1.5.5, most already in the
preview's largest-delta table; 1673 moved from `ht_bridge` in v1.5.3 to a
`certified_nominals` race with the CB stack, 121.9 s RC against 75.4 s). The
remaining inputs are within 1.10 of v1.5.3 or faster (7345 0.48, 7610 0.06).
No input lost its answer: every input v1.5.3 answers, the fix answers with the
same sorted output, except 13077 and 13584, where v1.5.5 (RC and fix alike)
prints `DROPPED 1` and `DROPPED 18` against `DROPPED 0` (a separate base
regression, `timing/attribution-rc-runs.txt` and the 13077/13584 runs in the
report). 4567, 3917 and 8148 time out on v1.5.3 and answer on the fix.

## Exactness checks

- `frontend-identity/heldout-ofn-nominals.txt`: `km ofn` under
  `KM_NOMINALS=1`, RC against fix, clause and meta files byte-identical on
  584 of the 585 held-out inputs; 15687 exceeds 120 s on both.
- `differential/*.tsv` (`scripts/drive.sh`, `diff_run.py` of data-values-3,
  cached HermiT answers, fix with `KM_HT_SINGLETON_INERT_AUDIT=1`, so an audit
  violation would show as ERR): probes 103 ok 11 timeout; fixtures 42 ok;
  tnd-sorts 6 ok; tnd-fresh2 152 ok 19 timeout; tnd-fresh3 66 ok 18 timeout;
  nomdata-auto 380 ok 20 timeout; r3data-auto 281 ok 19 timeout; r1600-auto
  381 ok 19 timeout. No WRONG, no ERR. Against the forced-nominal-data-misses
  `fix2` tables every verdict is unchanged except r1600 `fr56` (timeout to ok).
- `differential/singleton-gate-survey.tsv` (`scripts/survey.sh`, auto,
  `KM_HT_STATS`): of 569 inputs, 296 reach the bridge with a consumed
  singleton; 12 (nominal-coverage seeds m2010, m2036, m2093, m2100, m2128,
  m2179, m2215, m2217, m2275, m2299, m2314, m2387) are proved inert and run
  with the cache, all ok against HermiT under the audit; 284 keep the gate of
  0520da9d, among them every native_data_values fixture with singletons.
- 9027 under the audit: no violation, same answer.

## Tests (`tests/summary.txt`, release, `--test-threads=3`)

lib `value_singletons` 6, `frontend::sorts` 12 (two new: the indexed pass
against the reference on 3,000 random clause sets and on the fixture),
`frontend::` 426, `konclude_ht::bridge` 181 (7 ignored), `konclude_ht::completion`
679, `konclude_ht::` 1520 (7 ignored), all pass. Integration:
native_data_values 30, nominal_inert_sorts 4, top_nominal_data_successors 16,
forced_route_fail_closed 5, nominal_ground_body 3 pass;
universal_role_and_top_data_range 12 pass, 1 fails:
`data_value_singleton_next_to_nominal_successors` (case "object value instead
of data value" on route `nominals` exceeds 10 s). It fails on the base too:
`tests/base-failure/objval.ofn` times out at 30 s on `KM_ROUTE=nominals` with
the non-PGO 775223bf build, the RC, and both fix builds.

## Reproduce

`scripts/run.sh BIN INPUT OUTPREFIX [timeout] [cpu]`; `scripts/pair30.sh`,
`scripts/pairrc.sh`, `scripts/ofn_ident.sh OLD NEW LIST OUTDIR CPU`,
`scripts/drive.sh POOL…`, `scripts/survey.sh OUT FILE…`. The scratch copy of
the fix binary is `.work/agent-scratch/perf-9027/km.pgo.fix2`.
