#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=01:00:00
#SBATCH --job-name=km-just-stream-v4-stage
set -euo pipefail
cd /ibex/scratch/hohndor/km/dynamic-benchmark-20260917/justification-konclude-stream-v4-stage
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
python3 konclude-stream-stage-r2.py
