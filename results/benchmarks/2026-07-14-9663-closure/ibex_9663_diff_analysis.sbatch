#!/bin/bash
#SBATCH --job-name=9663-diff
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --output=/ibex/scratch/hohndor/km/9663_closure_20260714/slurm/diff-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km
run=$root/9663_closure_20260714
/usr/bin/python3 "$run/analyze_9663_diff.py" \
  "$run/km-baseline/9663.json" \
  "$root/gold/konclude__ore_ont_9663.owl.sig.gz" \
  "$run/analysis"
