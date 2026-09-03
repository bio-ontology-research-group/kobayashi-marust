# EL context-parallel validation panel (2026-09-03)

This panel evaluates the opt-in, fixpoint-preserving context-parallel EL
completion candidate. It does not report these results as default-route wins.
Automatic feature selection and a post-integration sweep remain separate gates.

## Provenance

- Candidate commits: `88be4b8`, `fd39d2f`
- Source archive SHA-256:
  `9135fdd300669c488faaccb07f3e4ee1cdb55c457895d85d573e2348bae53a81`
- Binary SHA-256:
  `06215e49a03249992718cb77df6084fc0870ad4e0a7962d995b65e217d745661`
- IBEX build job: `51250839` (`COMPLETED`, exit `0:0`)
- IBEX panel job: `51251013`
- Hardware constraint: Intel Xeon Gold 6248 at 2.50 GHz
- Limits per run: 480 seconds and 20 GiB
- Design: 18 ontologies, four arms, three repetitions, 216 runs
- Arms: serial EL completion and `KM_ELC_PAR_CTX=2`, `4`, or `8`
- Result archive SHA-256:
  `2836d1582849d83d4ab082977136ae7f6c566ebd7008cf59739512395f5accde`

Every task pinned and checked the binary hash and CPU model. The harness also
required an `ok` status, gold signature match, `elc` route trace, checkpoint,
and terminal completion marker before accepting a result.

## Validation outcome

- Final result records: 216/216
- Checkpoints: 216/216
- Terminal task markers: 216/216
- Gold signature matches: 216/216
- `elc` route traces: 216/216
- Failure artifacts: 0

Across the 18 ontologies, the geometric-mean wall-time ratios relative to the
serial arm were 0.976 for two workers, 0.892 for four workers, and 0.858 for
eight workers. The corresponding peak-memory ratios were 1.137, 1.177, and
1.233. Eight workers reduced median wall time on all 18 panel ontologies, but
usually consumed more memory than serial completion.

## Prospective strict recoveries

The following medians beat both external strict thresholds while remaining
correct. These are candidate results, not yet automatic-route claims.

| Ontology | Arm | Median wall (s) | Wall target (s) | Median peak (MiB) | Peak target (MiB) |
|---|---:|---:|---:|---:|---:|
| `ore_ont_15929.owl` | ctx8 | 1.5748 | 1.6922 | 266.62 | 581.16 |
| `ore_ont_2828.owl` | ctx8 | 2.6597 | 2.7197 | 431.11 | 818.41 |
| `ore_ont_5612.owl` | ctx8 | 1.6887 | 1.8041 | 271.63 | 591.73 |
| `ore_ont_795.owl` | ctx8 | 1.5080 | 1.8461 | 253.68 | 624.48 |

## Confirmation panel

IBEX job `51251710` added seven serial and seven ctx8 repetitions for each of
the four prospective recoveries. All 56 tasks completed with matching gold
signatures, checkpoints, terminal markers, the expected route and binary hash,
and zero failure artifacts. The result archive SHA-256 is
`c661fbf7ed9141eb3c0785107cbbb4a4eac8dfd91483a5c43a2632a8e0ad09cd`.

Combining jobs `51251013` and `51251710` gives ten observations per arm:

| Ontology | Arm | Runs | Median wall (s) | Wall range (s) | Median peak (MiB) | Wall margin |
|---|---:|---:|---:|---:|---:|---:|
| `ore_ont_15929.owl` | ctx8 | 10 | 1.5757 | 1.5661–1.8641 | 265.57 | 7.39% |
| `ore_ont_2828.owl` | ctx8 | 10 | 2.6113 | 2.5032–2.9187 | 431.23 | 4.15% |
| `ore_ont_5612.owl` | ctx8 | 10 | 1.6365 | 1.6116–1.7421 | 271.42 | 10.24% |
| `ore_ont_795.owl` | ctx8 | 10 | 1.5222 | 1.4601–1.7939 | 253.53 | 21.28% |

All four ten-run medians beat both external strict thresholds. Individual
observations can exceed a wall threshold, so the release claim remains based
on the preregistered median aggregation rather than best-case timing.

Any automatic selector must use ontology features, never ontology identity,
and must be projected over all 592 retained profiles before an IBEX validation
panel and full strict sweep.

## Semantic scope

The implementation partitions EL contexts among workers and exchanges derived
facts in batches. It preserves the same monotone finite completion fixpoint;
it does not add, remove, or weaken inference rules. Certificate and unsupported
execution modes decline the parallel path and retain serial behavior. This is
a scheduling optimization and does not change the Lean-certified calculus.
