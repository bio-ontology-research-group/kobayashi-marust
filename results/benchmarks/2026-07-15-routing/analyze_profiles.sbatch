#!/bin/bash
#SBATCH --job-name=km-profile-analyze
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/profile-analyze-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715
analyzer=${PROFILE_ANALYZER:-$root/analyze_profiles.py}
profiles=${PROFILE_DIR:-$root/profiles}
output_dir=${PROFILE_OUTPUT_DIR:-$root}
/usr/bin/python3 "$analyzer" --root "$root" --profiles "$profiles" --output-dir "$output_dir"
