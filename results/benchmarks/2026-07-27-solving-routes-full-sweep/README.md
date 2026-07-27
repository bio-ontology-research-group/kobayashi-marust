# 2026-07-27 successful-route full sweep

This sweep runs all current-main KM public and documented routes that recorded
at least one sound-and-complete result in the hash-bound 2026-07-22 panel. It
adds the exact full-completion route used to solve ORE ontology 9540. The only
comparison reasoners are Konclude, HermiT, and ELK.

The frozen contract contains 44 KM procedures and 3 baselines. Every procedure
receives 240 seconds and 20 GiB per ontology. The 592 ontologies are balanced
across 50 Slurm array tasks: 42 tasks contain 12 ontologies and 8 contain 11.

`full-benchmark-table.tsv`, the compressed row-level evidence, and the receipt
are populated from the completed IBEX aggregation and committed after audit.
