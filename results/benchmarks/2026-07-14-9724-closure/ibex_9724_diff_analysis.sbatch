#!/bin/bash
#SBATCH --job-name=km-9724-diff
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/diff-analysis-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
mkdir -p "$root/diff" "$root/slurm"

/usr/bin/python3 \
  "$km_root/9663_closure_20260714/analyze_9663_diff.py" \
  "$km_root/9663_closure_20260714/final-gate/9724/9724.json" \
  "$km_root/gold/konclude__ore_ont_9724.owl.sig.gz" \
  "$root/diff"
