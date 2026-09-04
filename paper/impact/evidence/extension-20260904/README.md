# Enablement extension evidence

This compact bundle records the bounded IBEX experiment rooted at
`/ibex/scratch/hohndor/km/v14-paper-impact-extension-20260904`.

`summary.json` is the fail-closed semantic result. `FINAL_RECEIPT.tsv` binds it
to validator and Slurm-script hashes and records terminal validation job
`51326594`. The projection receipts bind source, output, removed-axiom, tool,
and OWL 2 EL profile checks. KM receipts bind binary, input, output, resources,
and array tasks. HermiT and ELK result records bind their runtime jars and raw
taxonomy outputs.

Large GALEN raw outputs remain on IBEX and are identified by their receipts and
semantic digests. The compact bundle retains both reasoners' fingerprints, the
projection receipt, counts, subset result, and twenty deterministic full-only
samples. The original full GALEN result remains in the earlier impact root and
is independently bound by the pre-existing compact evidence.

Validation job `51326537` failed before publishing a summary because the first
validator compared KM default-prefixed synthetic names with HermiT expanded
IRIs. `logs/final-51326537.out` preserves that failure. The corrected validator
canonicalizes the equivalent identifiers; job `51326594` passed. No reasoner
task or ontology output was rerun.

Run the copied validator against the remote raw root to reproduce the semantic
checks:

```bash
python3 paper/benchmark/impact/validate_enablement_extension.py \
  --root /ibex/scratch/hohndor/km/v14-paper-impact-extension-20260904 \
  --old-impact-root /ibex/scratch/hohndor/km/v1.4-paper-impact-20260903 \
  --output /ibex/scratch/hohndor/km/v14-paper-impact-extension-20260904/summary.recheck.json
```

This validation loads the 56 MiB full and projected GALEN JSON outputs and must
run as a bounded Slurm job, not on an IBEX login node.

