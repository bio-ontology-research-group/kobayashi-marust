#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:08:00
#SBATCH --array=0-7%4
#SBATCH --export=NONE
#SBATCH --job-name=km-v150-coverage-tail-profile
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/coverage-tail-profile-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/coverage-tail-profile-tmp-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c coverage-tail-profile-files.sha256
/usr/bin/python3.9 "$root/profile_coverage_tail.py"
