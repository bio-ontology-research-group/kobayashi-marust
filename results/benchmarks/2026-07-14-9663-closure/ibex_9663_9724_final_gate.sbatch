#!/bin/bash
#SBATCH --job-name=km-9663-final
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9663_closure_20260714/slurm/final-gate-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/9663_closure_20260714
binary=$root/km-9663-final-bullseye
compare=$km_root/fullsweep/cmp_gold.py
case ${SLURM_ARRAY_TASK_ID:-0} in
  0) ontology=9663 ;;
  1) ontology=9724 ;;
  *) exit 2 ;;
esac

run=$root/final-gate/$ontology
input=$km_root/corpus/ore_ont_$ontology.owl
gold=$km_root/gold/konclude__ore_ont_$ontology.owl.sig.gz
mkdir -p "$run" "$root/slurm"

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN ontology=$ontology host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

/usr/bin/time -v -o "$run/$ontology.time" \
  /usr/bin/timeout -k 5 240 \
  /usr/bin/env \
    KM_TRIGGER_ABSORB=1 \
    KM_KEEP_CHAIN_AXIOMS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=30 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=180 \
    KM_HT_MEM_GB=18 \
    KM_PAR_MEM_GB=18 \
    KM_THREADS=16 \
    KM_HT_STATS=1 \
    KM_BRIDGE_PROGRESS=1 \
    KM_SAT_COUNTERS=1 \
    "$binary" classify "$input" \
    > "$run/$ontology.json" \
    2> "$run/$ontology.stderr"

read -r verdict extra missing < <(
  /usr/bin/python3 "$compare" "$run/$ontology.json" "$gold"
)
echo "RESULT ontology=$ontology verdict=$verdict extra=$extra missing=$missing"
/usr/bin/grep -E \
  'BRIDGE-(SATURATION-SEEDS|SATURATION|CLASSIFY)|Elapsed \(wall clock\)|Maximum resident set size' \
  "$run/$ontology.stderr" "$run/$ontology.time" 2>/dev/null || true
echo "END ontology=$ontology date=$(date -Is)"
