#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:15:00
#SBATCH --array=0-7%4
#SBATCH --export=NONE
#SBATCH --job-name=km-v150-data-padding-candidate
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/data-padding-candidate-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/data-padding-candidate-tmp-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c data-padding-candidate-files.sha256
/usr/bin/python3.9 "$root/run_data_padding_candidate.py"
