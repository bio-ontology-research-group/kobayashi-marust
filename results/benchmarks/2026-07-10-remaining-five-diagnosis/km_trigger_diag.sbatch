#!/bin/bash
#SBATCH --job-name=km-rem5-trigger
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=40G
#SBATCH --array=0-4%5
#SBATCH --output=/ibex/scratch/hohndor/km/rem5_diag_20260710/trigger-slurm-%A_%a.out

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/rem5_diag_20260710"
KM="$ROOT/engine/target/release/km"
ONTS=(3215 7914 9663 9724 14817)

ont=${ONTS[$SLURM_ARRAY_TASK_ID]}
input="$ROOT/corpus/ore_ont_${ont}.owl"
prefix="$OUT/km_trigger_${ont}"

mkdir -p "$OUT"
echo "BEGIN ont=$ont host=$(hostname) date=$(date -Is)"
/usr/bin/time -v -o "$prefix.time" \
  timeout 300 env \
    KM_TRIGGER_ABSORB=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=3 KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=120 KM_PAR_MEM_GB=36 \
    "$KM" classify "$input" \
    >"$prefix.json" 2>"$prefix.stderr"
rc=$?
echo "END ont=$ont rc=$rc date=$(date -Is)"
