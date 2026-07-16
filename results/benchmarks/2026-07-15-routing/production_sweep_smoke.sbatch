#!/bin/bash
# Validate the production sweep contract on representative EL, CB, nominal,
# cardinality, bridge, and rule inputs before submitting all 592 tasks.
#SBATCH --job-name=km-prod-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-5
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/prod-smoke-%A_%a.out

set -euo pipefail

: "${SWEEP_TAG:?submit with --export=ALL,SWEEP_TAG=...}"
: "${SWEEP_KM:?submit with --export=ALL,SWEEP_KM=...}"

root=/ibex/scratch/hohndor/km/routing_20260715
indices=(0 97 265 397 489 548)
export SLURM_ARRAY_TASK_ID=${indices[${SLURM_ARRAY_TASK_ID:-0}]}
export SWEEP_TAG=$SWEEP_TAG-smoke
exec /bin/bash "$root/production_full_sweep.sbatch"
