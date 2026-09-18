#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --job-name=km-v143-3215-pair
set -euo pipefail
/usr/bin/python3 /ibex/scratch/hohndor/km/v143-harness-20260918/pair-3215.py
