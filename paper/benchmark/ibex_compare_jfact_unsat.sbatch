#!/bin/bash
# Exact named-unsatisfiable differences for provisional JFact/HermiT splits.
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --array=0-11%6
#SBATCH --job-name=km-paper-jfact-unsat
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/jfact-unsat-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
ontologies=(chmo cvdo fideo ino kisao obcs obib proco psdo stato txpo uo)
ontology=${ontologies[$SLURM_ARRAY_TASK_ID]}
script=$root/runner-tools/compare_unsat_tsv.py
script_sha256=1b7b002f4c341f5a14ba9144f3f36d21840b5eea8b8622431204a53f9af34ef4
test "$(sha256sum "$script" | awk '{print $1}')" = "$script_sha256"
python3 "$script" \
  --left "$root/current-results/jfact/$ontology.taxonomy.tsv" \
  --right "$root/current-results/hermit/$ontology.taxonomy.tsv" \
  --left-label jfact --right-label hermit --sample-limit 20 \
  --output "$root/diagnostics/jfact-hermit-unsat/$ontology.json"
