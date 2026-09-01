#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --array=0-189%8
#SBATCH --job-name=km-paper-obo-verify
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/obo-verify-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
test -s "$root/obo-candidates-20260830.tsv"
test -s "$root/validate_obo_one.py"
test -s "$root/obo-snapshot/records/$(awk -F '\t' -v n=$((SLURM_ARRAY_TASK_ID + 2)) 'NR == n {print $1}' "$root/obo-candidates-20260830.tsv").json"
python3 "$root/validate_obo_one.py" \
  "$root/obo-candidates-20260830.tsv" "$root/obo-snapshot"
