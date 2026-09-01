#!/bin/bash
# Exact pair differences for provisional JFact/HermiT current-corpus splits.
# These diagnostics do not modify or replace benchmark result records.
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --array=0-11%6
#SBATCH --job-name=km-paper-jfact-diff
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/jfact-diff-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
ontologies=(chmo cvdo fideo ino kisao obcs obib proco psdo stato txpo uo)
ontology=${ontologies[$SLURM_ARRAY_TASK_ID]}
script=$root/runner-tools/compare_taxonomy_tsv.py
script_sha256=0c064c0719adc35d822e0c7272ea43c5add0305df059f259a9b43402938e7608
test "$(sha256sum "$script" | awk '{print $1}')" = "$script_sha256"
python3 "$script" \
  --left "$root/current-results/jfact/$ontology.taxonomy.tsv" \
  --right "$root/current-results/hermit/$ontology.taxonomy.tsv" \
  --left-label jfact --right-label hermit --sample-limit 20 \
  --output "$root/diagnostics/jfact-hermit/$ontology.json"
