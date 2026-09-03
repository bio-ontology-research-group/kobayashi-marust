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

The wall-time margin for `ore_ont_2828.owl` is about 2.2 percent, so it needs
additional repetitions before it can support an automatic-route claim. Any
automatic selector must use ontology features, never ontology identity, and
must be projected over all 592 retained profiles before an IBEX validation
panel and full strict sweep.

## Semantic scope

The implementation partitions EL contexts among workers and exchanges derived
facts in batches. It preserves the same monotone finite completion fixpoint;
it does not add, remove, or weaken inference rules. Certificate and unsupported
execution modes decline the parallel path and retain serial behavior. This is
a scheduling optimization and does not change the Lean-certified calculus.
