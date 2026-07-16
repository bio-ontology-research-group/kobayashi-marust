#!/bin/bash
# Submit after analyze_auto.sbatch with an array sized to the auto gap CSV.
#SBATCH --job-name=km-auto-gap
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/auto-gap-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715
/usr/bin/python3 "$root/recheck_gap.py" \
  --root "$root" --task "${SLURM_ARRAY_TASK_ID:-0}" --replicates 3 --mode auto
