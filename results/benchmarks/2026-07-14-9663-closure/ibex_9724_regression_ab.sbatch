#!/bin/bash
#SBATCH --job-name=km-9724-ab
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9663_closure_20260714/slurm/9724-ab-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/9663_closure_20260714
case ${SLURM_ARRAY_TASK_ID:-0} in
  0)
    label=before
    binary=$km_root/3215_closure_20260713/km-3215-bullseye
    ;;
  1)
    label=after
    binary=$root/km-9663-bullseye
    ;;
  *) exit 2 ;;
esac

run=$root/9724-ab/$label
ontology=$km_root/corpus/ore_ont_9724.owl
gold=$km_root/gold/konclude__ore_ont_9724.owl.sig.gz
compare=$km_root/fullsweep/cmp_gold.py
mkdir -p "$run" "$root/slurm"

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN label=$label host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

/usr/bin/time -v -o "$run/9724.time" \
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
    "$binary" classify "$ontology" \
    > "$run/9724.json" \
    2> "$run/9724.stderr"

read -r verdict extra missing < <(/usr/bin/python3 "$compare" "$run/9724.json" "$gold")
echo "RESULT label=$label verdict=$verdict extra=$extra missing=$missing"
/usr/bin/grep -E \
  'BRIDGE-(SATURATION|CLASSIFY)|Elapsed \(wall clock\)|Maximum resident set size' \
  "$run/9724.stderr" "$run/9724.time" 2>/dev/null || true
echo "END label=$label date=$(date -Is)"
