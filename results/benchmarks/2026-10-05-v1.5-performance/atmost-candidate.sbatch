#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:40:00
#SBATCH --array=0-41%8
#SBATCH --export=NONE
#SBATCH --job-name=km-atmost-dependency
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/atmost-candidate-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/atmost-tmp-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c atmost-candidate-files.sha256
/usr/bin/python3.9 "$root/run_atmost_candidate.py"
