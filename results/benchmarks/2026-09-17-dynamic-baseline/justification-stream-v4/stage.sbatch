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
cd /ibex/scratch/hohndor/km/dynamic-benchmark-20260917/justification-stream-v4-stage
python3 stage.py
