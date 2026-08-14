#!/bin/bash
#SBATCH --job-name=km-par-nf4-profile
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814/profile-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814
ids=(8737 16744 7246 6682)
id=${ids[${SLURM_ARRAY_TASK_ID:?}]}
KM_ROUTE=auto KM_ELC_PAR_NF4=1 KM_ELC_PROFILE=1 KM_ELC_TIMING=1 \
  timeout 240 "$root/km" classify \
  "/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl" \
  > "$root/profile-${id}.json" 2> "$root/profile-${id}.stderr"
sha256sum "$root/profile-${id}.json"
grep -E 'KM_ELC_(PROFILE|TIMING)' "$root/profile-${id}.stderr"
