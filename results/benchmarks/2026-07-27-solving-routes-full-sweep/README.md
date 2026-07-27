# 2026-07-27 successful-route full sweep

This sweep runs all current-main KM public and documented routes that recorded
at least one sound-and-complete result in the hash-bound 2026-07-22 panel. It
adds the exact full-completion route used to solve ORE ontology 9540. The only
comparison reasoners are Konclude, HermiT, and ELK.

The frozen contract contains 44 KM procedures and 3 baselines. Every procedure
receives 240 seconds and 20 GiB per ontology. The 592 ontologies are balanced
across 50 Slurm array tasks: 42 tasks contain 12 ontologies and 8 contain 11.

The sweep completed as Slurm array `49486147`; all 50 chunks and 592
ontologies completed without a failed chunk. Aggregate job `49486148` produced
27,824 procedure rows. `full-benchmark-table.tsv` contains the procedure-level
soundness, completeness, runtime, and memory results. `full-results.jsonl.gz`
contains the row-level evidence, and `receipt.json` binds both files by SHA-256.

Headline sound-and-complete counts are 580 for the best KM route, 587 for
Konclude, 557 for HermiT, and 531 for ELK. The exact 9540 full-completion route
is deliberately narrow and records 362 sound-and-complete classifications when
replayed over the complete corpus.
