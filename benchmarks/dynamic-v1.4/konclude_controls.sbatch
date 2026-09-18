#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:05:00
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
python3 konclude_controls.py konclude-controls
python3 konclude_incremental.py /ibex/scratch/hohndor/km/Konclude-official konclude-controls/states.txt konclude-controls/results-v2 --reference konclude-controls/expected
