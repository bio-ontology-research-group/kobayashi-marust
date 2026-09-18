#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:15:00
set -euo pipefail
python3 /ibex/scratch/hohndor/km/v143-harness-20260918/audit-rustdl.py
