# HT version matrix — FULL ORE-2015 corpus (587 onts)

- Date: 2026-06-17
- Binary: committed `190fe53` (HT path, `tableau_cli`), built on IBEX.
- Harness: `hteval.sbatch` (240 s timeout, 22 GB), `ht_runone.py`; gold =
  Konclude per-ont `.sig.gz`. One arm per `KM_HT_*` config, one binary.
- Reporting per standing rule: passrate (ok) + MATCH + sound/complete split +
  avg AND median wall/mem. Non-ok statuses broken out below.
- Routability: every ont runs; non-ALC(H) inputs (inverse/number/nominal) and
  RBox-fenced inputs are surfaced and excluded from the HT verdict by the
  harness. This panel is HT-in-isolation, NOT the production CB/HT router.

## Panel

| arm            |   N |  ok | MATCH | snd | cmpl | unsnd | incmp | wall_avg | wall_med | mem_avg | mem_med |
|----------------|----:|----:|------:|----:|-----:|------:|------:|---------:|---------:|--------:|--------:|
| ht-default     | 587 | 454 |   453 | 454 |  453 |     0 |     1 |   15.343 |    0.169 |  48.322 |     5.1 |
| ht-incr7       | 587 | 452 |   451 | 452 |  451 |     0 |     1 |   14.335 |    0.191 |  55.449 |     5.9 |
| ht-learn       | 587 | 450 |   449 | 450 |  449 |     0 |     1 |   15.486 |    0.183 |  50.091 |     5.6 |
| ht-naive       | 587 | 237 |   236 | 237 |  236 |     0 |     1 |   18.419 |    0.594 |   3.341 |     2.2 |
| ht-nowatch     | 587 | 452 |   451 | 452 |  451 |     0 |     1 |   13.796 |    0.158 |  56.024 |    5.55 |
| ht-notold      | 587 | 442 |   441 | 442 |  441 |     0 |     1 |   13.311 |    0.217 |   30.98 |     5.3 |
| ht-coreblock   | 587 | 414 |   414 | 414 |  414 |     0 |     0 |   11.252 |    0.153 |  42.452 |     4.5 |
| ht-eqblock     | 587 | 415 |   415 | 415 |  415 |     0 |     0 |   11.618 |    0.156 |  43.199 |     4.7 |
| ht-ancestor    | 587 | 423 |   422 | 423 |  422 |     0 |     1 |    10.02 |    0.162 |  42.464 |     4.6 |
| ht-modelprune  | 587 | 447 |   446 | 447 |  446 |     0 |     1 |   13.08  |    0.176 |  54.813 |    5.55 |

(ht-modelprune deduped to 587 unique onts / 447 ok — the raw aggregate showed
N=588 from one duplicated chunk row.)

Non-ok status breakdown (ht-default): timeout=116, DIFF_consistency=6,
no_owl=3, wrap_fail=8.

## Findings

- **Best HT arm = `ht-default`** (anywhere-SUBSET blocking, watch, told-subsumers,
  no search heuristics): 454 ok, **0 unsound**, 1 incomplete, median 0.169 s /
  5.1 MB.
- **Soundness invariant holds across every arm: unsound = 0.** The only
  incompleteness is **ont 7216** (48962 missing subsumptions, disj=0, trans=False
  — a large near-Horn taxonomy gap, NOT the disjunction family; identical in all
  arms that finish it). `coreblock`/`eqblock` show incmp=0 only because they
  time out on 7216.
- **`ht-modelprune` is a NET LOSS on the full corpus: 447 vs 454 (−7).**
  Per-ont (deduped): recovers 2 (10689, 14216) but regresses 9 (10778, 3795,
  4834, 5943, 6060, 7025, 7993, 868, 9400 — 8 → timeout, 868 → wrap_fail). The
  per-Phase-2-test `root_pos_label` intersection costs more wall time than the
  tests it saves on mid-size ontologies, tipping them over the 240 s wall.
  - This OVERTURNS the earlier "+1 on the 27-ont sample" reading: the sample was
    unrepresentative. Per the standing rule, the full panel governs.
  - `KM_HT_MODELPRUNE` stays **gated OFF** (committed `190fe53`, inert by
    default). Do not promote it. Production (CB/HT router) is unaffected.
- `ht-naive` (no model pruning, O(n²) classify) collapses to 237 ok — confirms
  the told-subsumer + single-model read-off in `ht-default` is load-bearing.
- Blocking-mode ablation: anywhere-subset (default, 454) > ancestor-only (423) >
  core-eq (414/415). Subset blocking folds the most while staying sound.

## Context

This is HT measured alone. In production KM routes EL→elc, then CB, with HT as a
sound fallback on CB-failures (the disjunction family); the HT timeouts here
(116) include the live-∀+⊔ family that no current HT config closes (see
[[project_km_family_diagnosis]] and the BLOCKSKIP investigation in
docs/ht-search-debug.md).
