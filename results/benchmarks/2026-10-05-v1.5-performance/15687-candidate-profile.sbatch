#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:30:00
#SBATCH --export=NONE
#SBATCH --job-name=km-15687-candidate-profile
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/15687-candidate-profile-%j.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/15687-candidate-profile-tmp-$SLURM_JOB_ID"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c 15687-candidate-profile-files.sha256
/usr/bin/python3.9 "$root/profile_15687_candidates.py"
