#!/bin/bash
#SBATCH --job-name=km-10860-sandwich2
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/10860-rule-sandwich/except-zero-slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715/10860-rule-sandwich
runner=/ibex/scratch/hohndor/km/harness/ore_runone.py
name=ore_ont_10860_allheads_except_r2rzero.owl
mkdir -p "$root/results"
/usr/bin/python3 "$runner" --reasoner konclude --ont "$root/$name" \
  --outdir "$root/results" --timeout 1200 --memcap-mb 15000 \
  > "$root/results/konclude__$name.json"
test -s "$root/results/konclude__$name.json"
