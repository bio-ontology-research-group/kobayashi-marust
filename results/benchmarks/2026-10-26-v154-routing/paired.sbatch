#!/bin/bash
# Paired v153/general routing measurement; submit with
#   sbatch --export=ALL,KM_HALF=design,KM_TASKS=60 --array=0-59 paired.sbatch
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=12:00:00
#SBATCH --job-name=km154-paired
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026/slurm/paired-%A_%a.out
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026
export TMPDIR="$root/tmp-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
/usr/bin/python3.9 "$root/run_paired.py"
