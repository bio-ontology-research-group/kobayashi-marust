# Gold adjudication for ORE 10621, 10860, and 1194

This directory records the independent adjudication requested on 2026-07-16.
The governing status vocabulary and historical closure audit are in
`docs/HARD-RESIDUAL-AUDIT.md`.

## Cross-reasoner job

`reasoner_crosscheck.sbatch` runs three independent reasoners with a three-hour,
110 GB per-process budget:

- full `ore_ont_1194.owl`: Konclude, HermiT, and Sequoia;
- rule-free `ore_ont_10860_norules.owl`: Konclude, HermiT, and Sequoia.

The `10860` rule-free input is obtained by deleting the 17 one-line
`DLSafeRule(...)` axioms from the original functional-syntax ontology. This is
not the final adjudicated ontology. It isolates the OWL 2 DL base before the
finite DL-safe rule grounding is checked and added back.

Results are retained on IBEX under:

```text
/ibex/scratch/hohndor/km/gold_adjudication_20260716/
```

Do not promote any generated signature to gold until this README records the
semantic checks, signature comparisons, and confidence assessment.
