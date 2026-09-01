#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --job-name=km-paper-hard-fetch
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/hard-fetch-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
test -s "$root/hard-public-candidates.tsv"
python3 "$root/acquire_obo_one.py" \
  "$root/hard-public-candidates.tsv" "$root/hard-cases" --index 0
