#!/bin/bash
# Exact streaming relation differences for disagreements first visible in the
# complete eight-reasoner aggregate.
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --array=0-4%5
#SBATCH --job-name=km-paper-final-diffs
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/final-diffs-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
results=$root/current-results
out=$root/diagnostics/final-five-diffs
comparator=$root/runner-tools/compare_taxonomy_tsv.py
mkdir -p "$out"

case "$SLURM_ARRAY_TASK_ID" in
  0) ontology=cdao; left=more; right=hermit ;;
  1) ontology=cheminf; left=konclude; right=hermit ;;
  2) ontology=foodon; left=more; right=hermit ;;
  3) ontology=miapa; left=more; right=hermit ;;
  4) ontology=pbpko; left=jfact; right=konclude ;;
  *) exit 2 ;;
esac

left_path=$results/$left/$ontology.taxonomy.tsv
right_path=$results/$right/$ontology.taxonomy.tsv
test -s "$left_path"
test -s "$right_path"
/usr/bin/python3 "$comparator" \
  --left "$left_path" --right "$right_path" \
  --left-label "$left" --right-label "$right" --sample-limit 25 \
  --output "$out/$ontology.json"
