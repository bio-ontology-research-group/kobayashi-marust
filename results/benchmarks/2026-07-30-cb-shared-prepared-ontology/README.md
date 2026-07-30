# Shared prepared ontology across parallel CB workers (ore_ont_1194)

Date: 2026-07-30. Host: `leechuck-office` (56 logical cores, 125 GB RAM).
Ontology: `ore_ont_1194.owl` (78,422,379 bytes), copied from the IBEX corpus at
`/ibex/scratch/hohndor/km/corpus/`.

## What changed

Every query-parallel CB worker used to build its own `Engine` with
`Engine::new(sig0.clone(), clauses0.clone(), dropped)`. That gave each worker a
private copy of the normalized clause arena, the Hyper candidate indexes, the
trigger-analysed signature and the nominal-enumeration certificates. On 1194
those structures hold 1,062,241 clauses, 88,440 interned concept names and
221,086 class assertions, so the copies alone scaled to tens of GB.

The engine now separates the finalized ontology (`Engine::prepare` ->
`PreparedOntology`) from the per-engine saturation state
(`Engine::from_prepared`). `Reasoner::saturate` prepares once and hands the same
`Arc`-shared signature, clause arena and nominal certificates to the sequential
run, to every static chunk and to every work-stealing worker. Retained
insertion, the one writer, goes through `Arc::make_mut`, so an engine that still
shares a prepared ontology copies before it mutates. Preparing once also
replaces the throw-away engine that existed only to enumerate the named
queries, and the `KM_SPLIT` search reuses one prepared ontology across its
branch engines instead of re-indexing per search node.

## Frontend (unchanged, for context)

```bash
km ofn ore_ont_1194.owl --meta 1194.meta > 1194.clauses
```

17.4 s, 1.19 GiB peak. 270,431,799 bytes of clause JSON, 1,062,241 clauses,
70,231 declared classes.

## Engine peak RSS, `km engine < 1194.clauses`

Each run is `systemd-run --user --scope -p MemoryMax=24G -p MemorySwapMax=0`
around `/usr/bin/time -v /usr/bin/timeout 240 env KM_THREADS=<t> km engine`.
No run reaches a fixpoint inside 240 s, so each row compares the peak RSS of
the same 240 s of saturation.

TBox saturation (individual clauses dropped, `KM_NOMINALS` unset):

| threads | HEAD peak | shared peak | reduction |
|---:|---:|---:|---:|
| 1 | 1.59 GiB | 1.59 GiB | none (one engine) |
| 8 | 4.90 GiB | 2.75 GiB | 1.8x |
| 16 | 7.78 GiB | 3.87 GiB | 2.0x |
| 56 | 19.67 GiB | 4.97 GiB | 4.0x |

Nominal mode (`KM_NOMINALS=1`, the configuration the production CB route uses
on this ontology), 56 threads:

| build | wall | peak RSS |
|---|---:|---:|
| HEAD | 240 s cap | 19.58 GiB |
| shared | 240 s cap | 4.15 GiB |

Marginal cost per extra worker at 56 threads falls from about 335 MB to about
62 MB. The remaining per-worker cost is the private saturation state (contexts,
clause arenas, shared closures), which is not shareable.

Same measurement with the query set pinned to the first 40 named concepts
(`KM_QUERIES`, `KM_NOMINALS=1`, `KM_THREADS=56`, 280 s cap), which fixes the
per-worker workload instead of letting the schedule drift: HEAD 13.79 GiB,
shared 2.24 GiB. Neither build finishes those 40 queries inside the cap, so this
compares 280 s of identical work, not a completed classification.

## Production route on 1194

```bash
km classify ore_ont_1194.owl
```

Both builds fail the same way and at the same point, at about 33 s:

```text
worker engine exited 101:
thread panicked at src/calc.rs:114:5:
nominal mode: f(o) term space exhausted (f id 124950, individual 18055)
```

Peak RSS for that route drops from 7.73 GiB (HEAD) to 2.59 GiB (shared). The
blocker is the packed `f(o)` term encoding, not memory: `COMP_IND_BITS = 17`
leaves about 32,767 Skolem-function ids in the composite range, and the
absorbed nominal route introduces 124,950 of them. That limit is reported, not
approximated, and this change does not address it.

## Where 1194 stands after this change

- The 20 GiB wall that the retained evidence records for the parallel CB
  attempt is gone: the same saturation now peaks at 4.15 GiB with 56 workers.
- 1194 is not closed. It is wall-clock bound well past the contract: the shared
  build at 56 threads in nominal mode reaches no fixpoint in 1,800 s, at a peak
  of 8.13 GiB (`MemoryMax=30G`, `nice -n 10`). Per-worker saturation state keeps
  growing with time, so a longer run on this ontology would eventually reach the
  20 GiB cap on its own; the parallel clone no longer gets there in 240 s.
- The default classify route needs the `f(o)` term-space limit lifted before any
  route-level 1194 result is possible.

## Correctness

- Byte-identical engine output, HEAD vs shared, on 10 ORE ontologies
  (`ore_ont_{3106,4578,7195,8329,9020,10389,10608,10991,13124,15615}`) at
  `KM_THREADS` 1, 4 and 8, and identical frontend output on the same files.
- Byte-identical output in nominal mode (`KM_NOMINALS=1`) on the five of those
  with an ABox (10608, 10991, 13124, 15615, 7195) at 1 and 8 threads.
- `cargo test --release`: 1779 passed, 0 failed, 8 ignored, plus the integration
  suites (2 + 3 + 4 + 6 + 11 + 5 + 1 passed, 0 failed).
- No wall-time regression on the completing ontologies at 8 threads (two
  repetitions each of 10389, 13124, 8329, 7195: within run-to-run noise).

Preparation is a pure function of the input clause set and is unchanged by this
split (`Engine::new` is now `prepare` followed by `from_prepared`), the shared
state is immutable during saturation, and the per-worker partition of queries is
untouched. The derived set is therefore identical and no Lean re-certification
applies.

## Caveats

The workstation was running sibling jobs during these measurements, so wall
times are not benchmark-grade. Peak RSS comparisons are between runs of equal
wall budget on the same host, and the memory result is a factor of 4, well
outside that noise.
