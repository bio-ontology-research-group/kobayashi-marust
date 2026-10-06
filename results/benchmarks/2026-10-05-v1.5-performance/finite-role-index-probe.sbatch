#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:12:00
#SBATCH --array=0-3%2
#SBATCH --export=NONE
#SBATCH --job-name=km-v150-finite-role-index-probe
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/finite-role-index-probe-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/finite-role-index-probe-tmp-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c finite-role-index-probe-files.sha256
/usr/bin/python3.9 "$root/probe_finite_role_index.py"
