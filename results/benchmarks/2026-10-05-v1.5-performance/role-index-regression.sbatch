#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:12:00
#SBATCH --array=0-9%4
#SBATCH --export=NONE
#SBATCH --job-name=km-v150-role-index-regression
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/role-index-regression-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/role-index-regression-tmp-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c role-index-regression-files.sha256
/usr/bin/python3.9 "$root/probe_role_index_regression.py"
