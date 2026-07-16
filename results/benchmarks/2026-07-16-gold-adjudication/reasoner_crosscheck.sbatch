#!/bin/bash
#SBATCH --job-name=km-gold-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=03:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=120G
#SBATCH --array=0-5
#SBATCH --output=/ibex/scratch/hohndor/km/gold_adjudication_20260716/slurm-%A_%a.out

set -u

root=/ibex/scratch/hohndor/km
out=$root/gold_adjudication_20260716/results
runner=$root/harness/ore_runone.py
mkdir -p "$out"

onts=(
  "$root/corpus/ore_ont_1194.owl"
  "$root/corpus/ore_ont_1194.owl"
  "$root/corpus/ore_ont_1194.owl"
  "$root/gold_adjudication_20260716/ore_ont_10860_norules.owl"
  "$root/gold_adjudication_20260716/ore_ont_10860_norules.owl"
  "$root/gold_adjudication_20260716/ore_ont_10860_norules.owl"
)
reasoners=(konclude hermit sequoia konclude hermit sequoia)

i=${SLURM_ARRAY_TASK_ID:-0}
reasoner=${reasoners[$i]}
ont=${onts[$i]}

export BENCH_XMX=-Xmx100g
/usr/bin/python3 "$runner" \
  --reasoner "$reasoner" \
  --ont "$ont" \
  --outdir "$out" \
  --timeout 10000 \
  --memcap-mb 110000 \
  > "$out/${reasoner}__$(basename "$ont").json"
