#!/bin/bash
#SBATCH --job-name=km-routes47-aggregate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes/slurm-%x-%j.out
set -euo pipefail
[[ $# -eq 1 ]]
root=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes
script_dir=$(/usr/bin/readlink -f "${SLURM_SUBMIT_DIR:?}")
export PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0
/usr/bin/python3 "$script_dir/aggregate.py" \
  --run-root "$root/runs/$1" --output "$root/aggregate/$1"
