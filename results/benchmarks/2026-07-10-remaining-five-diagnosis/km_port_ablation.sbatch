#!/bin/bash
#SBATCH --job-name=km-rem5-port
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=40G
#SBATCH --array=0-14%10
#SBATCH --output=/ibex/scratch/hohndor/km/rem5_diag_20260710/port-slurm-%A_%a.out

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/rem5_diag_20260710"
KM="$ROOT/engine/target/release/km"
ONTS=(3215 7914 9663 9724 14817)
ARMS=(sat sat_ext sat_ext_cache)

ont=${ONTS[$((SLURM_ARRAY_TASK_ID % 5))]}
arm=${ARMS[$((SLURM_ARRAY_TASK_ID / 5))]}
input="$ROOT/corpus/ore_ont_${ont}.owl"
prefix="$OUT/km_${arm}_${ont}"
extra=(KM_HT_SATURATION=1)
case "$arm" in
  sat_ext) extra+=(KM_HT_SAT_EXT=1) ;;
  sat_ext_cache) extra+=(KM_HT_SAT_EXT=1 KM_HT_SATCACHE=1) ;;
esac

mkdir -p "$OUT"
echo "BEGIN ont=$ont arm=$arm host=$(hostname) date=$(date -Is)"
/usr/bin/time -v -o "$prefix.time" \
  timeout 300 env \
    KM_HT_BRIDGE=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=3 KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=120 KM_PAR_MEM_GB=36 \
    "${extra[@]}" \
    "$KM" classify "$input" \
    >"$prefix.json" 2>"$prefix.stderr"
rc=$?
echo "END ont=$ont arm=$arm rc=$rc date=$(date -Is)"
