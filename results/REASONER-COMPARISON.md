# ORE-2015 side-by-side: KM (live config) vs Konclude / ELK / HermiT

IBEX job **47559562** (`km_cmp_new.sbatch`), 584 gold onts (587 minus the 3
giants absent on IBEX). All four reasoners run **sequentially on the same node
per ontology**, 600 s / 56 GB, 16 cores, so wall/peak are directly comparable.

KM = the post-integration **live config**: rebuilt `new` binary (clauses_cand +
SmallVec) + `KM_ABSORB` + `KM_ABSORB_PORTFOLIO` + seq auto-route, **no
`KM_TAB_RACE`** (dropped as the avg-time loser; see `docs/PERF-LEDGER.md`).

## Status

| reasoner | ok | timeout | error |
|----------|---:|--------:|------:|
| konclude | 582 | 0 | 2 |
| elk      | 584 | 0 | 0 |
| hermit   | 561 | 23 | 0 |
| km       | 558 | 26 | 0 |

## Correctness vs Konclude-gold (byte-identical sig.gz)

| reasoner | MATCH | DIFF | NOSIG |
|----------|------:|-----:|------:|
| konclude | 582 | 0 | 2 |
| elk      | 527 | **57** | 0 |
| hermit   | 553 | **8** | 23 |
| km       | **558** | **0** | 26 |

KM is the only reasoner besides the gold reasoner (Konclude) with **zero**
disagreements. ELK's 584 "ok" is misleading: 57 are wrong (it is EL-only and
unsound/incomplete on the non-EL onts). HermiT has 8 wrong answers.

## Mean / median over the 543 ontologies all four reasoners solve

| reasoner | mean wall (s) | med wall (s) | mean RSS (MB) | med RSS (MB) |
|----------|--------------:|-------------:|--------------:|-------------:|
| konclude | 1.47 | 0.29 | 394 | 124 |
| elk      | 1.25 | 0.78 | 458 | 236 |
| hermit   | 16.43 | 1.84 | 1939 | 722 |
| km       | 4.02 | 0.35 | 440 | **36** |

## Wall / peak percentiles over each reasoner's OK runs

| reasoner | n_ok | wall p50 | wall p90 | wall p99 | peak p50 | peak p90 | peak max |
|----------|-----:|---------:|---------:|---------:|---------:|---------:|---------:|
| konclude | 582 | 0.29 | 5.01 | 30.7 | 133 | 1264 | 15415 |
| elk      | 584 | 0.81 | 2.47 | 15.6 | 246 | 1290 | 6775 |
| hermit   | 561 | 1.84 | 40.97 | 268.7 | 718 | 4752 | 28588 |
| km       | 558 | 0.38 | 7.55 | 73.3 | 39 | 665 | 45192 |

## Reading

- **Memory:** KM has the lowest median (36 MB) and p90 (665 MB) peak RSS of all
  four by a wide margin (HermiT's median is 20x larger). One ont blows KM's tail
  to 45 GB (the central core-growth case, ORE_16444-class).
- **Speed:** KM's median wall (0.38 s) is second only to Konclude and beats ELK
  and HermiT. KM's mean (4.02 s) is inflated by its slow-but-correct hard-ont
  tail, yet is 4x lower than HermiT's mean (16.43 s).
- **Coverage:** KM solves 558. Its 26 misses are
  541,1603,2669,3215,4604,5303,6934,7246,7499,7581,7914,9024,9540,9635,9663,
  9724,10621,10702,11460,12141,12653,14817,15491,15516,15672,15803.
  - 2669, 15516 are SWRL/DLSafeRule onts (Konclude also errors on these).
  - HermiT solves 18 of KM's 26 misses (the live ∀+⊔ disjunction family +
    throughput onts); Konclude solves 24 of 26.
  - ELK "solves" all 26 but is unsound/incomplete on them (part of its 57 DIFF).
- **No ontology is solved by none** (584/584 solved by ≥1 reasoner). No reasoner
  has a unique solve in this set.

## Bottom line

KM trails Konclude by 24 onts and HermiT by 3, but it is the leanest reasoner in
the field (lowest median + p90 memory), competitive on median speed, and tied
with Konclude as the only fully gold-clean reasoner (0 wrong vs ELK's 57 and
HermiT's 8). The residual misses are the known hard set: the live ∀+⊔
disjunction family, the central core-growth/context-explosion throughput onts,
and the two SWRL ontologies.
