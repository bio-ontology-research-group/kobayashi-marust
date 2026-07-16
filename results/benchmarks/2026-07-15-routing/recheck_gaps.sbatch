#!/bin/bash
# Submit after the final analysis with:
#   n=$(($(wc -l < gaps-over-20-percent.csv)-1))
#   sbatch --array=0-$((n-1))%36 recheck_gaps.sbatch
#SBATCH --job-name=km-gap-recheck
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/gap-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715
/usr/bin/python3 "$root/recheck_gap.py" \
  --root "$root" --task "${SLURM_ARRAY_TASK_ID:-0}" --replicates 3
