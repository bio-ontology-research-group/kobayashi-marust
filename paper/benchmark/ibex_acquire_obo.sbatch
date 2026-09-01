#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --array=0-189%4
#SBATCH --job-name=km-paper-obo-fetch
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/obo-fetch-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
test -s "$root/obo-candidates-20260830.tsv"
test -s "$root/acquire_obo_one.py"
mkdir -p "$root/logs" "$root/obo-snapshot"
python3 "$root/acquire_obo_one.py" \
  "$root/obo-candidates-20260830.tsv" \
  "$root/obo-snapshot"
