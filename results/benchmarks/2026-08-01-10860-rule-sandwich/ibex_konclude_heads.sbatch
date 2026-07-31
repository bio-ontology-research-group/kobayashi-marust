#!/bin/bash
#SBATCH --job-name=km-10860-heads
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --array=0-15%4
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/10860-rule-sandwich/head-slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715/10860-rule-sandwich
runner=/ibex/scratch/hohndor/km/harness/ore_runone.py
i=$(printf '%02d' "$SLURM_ARRAY_TASK_ID")
ont=$root/heads/head-$i.owl
out=$root/head-results
mkdir -p "$out"

/usr/bin/python3 "$runner" \
  --reasoner konclude \
  --ont "$ont" \
  --outdir "$out" \
  --timeout 600 \
  --memcap-mb 7500 \
  > "$out/head-$i.json"

test -s "$out/head-$i.json"
