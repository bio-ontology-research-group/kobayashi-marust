# Correctness scoring schema v2

Schema v2 re-adjudicates the retained 39,072 measurements. It does not rerun a
reasoner and does not alter status, time, memory, command, taxonomy, binary, or
Slurm provenance.

Run these commands from the repository root:

```sh
python3 -m unittest results/benchmarks/test_full_panel_correctness.py

python3 results/benchmarks/audit_full_panel_route_coverage.py \
  --ledger results/benchmarks/2026-07-22-reproduced-route-performance/ontology-route-performance.pre-panel.tsv \
  --contract results/benchmarks/2026-07-22-reproduced-route-performance/full_panel_contract.py \
  --output results/benchmarks/2026-07-22-reproduced-route-performance/route-coverage-audit.scoring-v2.json

python3 results/benchmarks/rescore_full_panel.py \
  --input results/benchmarks/2026-07-22-reproduced-route-performance/full-panel-results.tsv.gz \
  --wide results/benchmarks/2026-07-22-reproduced-route-performance/ontology-route-performance.tsv \
  --output-dir results/benchmarks/2026-07-22-reproduced-route-performance
```

The route audit fails unless the ledger has 592 rows, exactly 589 sound and
complete historical claims, and every distinct accepted environment is present
as either a public route or an exact documented environment in the panel
contract. The retained contract passes with 35 public routes, eight documented
environments, and no missing historical environment.

The rescorer fails unless it reads exactly 592 ontologies and 66 procedures and
repairs the eight original KM-auto regression cases. It treats two trusted
answers that both report inconsistency as the same complete classical OWL
answer. It also permits exact same-job full-IRI comparison for the allowlisted
3524 and 15703 wrappers, whose local-name projection is known to be
non-injective.

The expected headline sound-and-complete totals are:

| procedure | both yes |
|---|---:|
| KM, documented selection | 583 |
| KM, best current route | 587 |
| KM, automatic route | 570 |
| Konclude | 587 |
| HermiT | 557 |
| ELK | 531 |
| RustDL, complete mode | 530 |
| Sequoia, strict mode | 339 |

[`scoring-v2-receipt.json`](scoring-v2-receipt.json) binds the v1 input, v1
wide table, scorer, rescore driver, and every v2 output by SHA-256.
