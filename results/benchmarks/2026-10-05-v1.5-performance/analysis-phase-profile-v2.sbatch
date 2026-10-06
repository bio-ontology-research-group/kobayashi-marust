#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:15:00
#SBATCH --array=0-2%3
#SBATCH --export=NONE
#SBATCH --job-name=km-v150-analysis-phase-profile-v2
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/analysis-phase-profile-v2-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/analysis-phase-profile-v2-tmp-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c analysis-phase-profile-v2-files.sha256
/usr/bin/python3.9 "$root/profile_analysis_phases_v2.py"
