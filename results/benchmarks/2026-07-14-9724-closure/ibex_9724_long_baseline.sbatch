#!/bin/bash
#SBATCH --job-name=km-9724-long
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=64G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/long-baseline-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
binary=$km_root/9663_closure_20260714/km-9663-final-bullseye
ontology=$km_root/corpus/ore_ont_9724.owl
gold=$km_root/gold/konclude__ore_ont_9724.owl.sig.gz
compare=$km_root/fullsweep/cmp_gold.py
run=$root/long-baseline
mkdir -p "$run" "$root/slurm"

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

/usr/bin/time -v -o "$run/9724.time" \
  /usr/bin/timeout -k 10 1800 \
  /usr/bin/env \
    KM_TRIGGER_ABSORB=1 \
    KM_KEEP_CHAIN_AXIOMS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=300 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=1200 \
    KM_HT_MEM_GB=60 \
    KM_PAR_MEM_GB=60 \
    KM_THREADS=16 \
    KM_HT_STATS=1 \
    KM_BRIDGE_PROGRESS=1 \
    KM_SAT_COUNTERS=1 \
    "$binary" classify "$ontology" \
    > "$run/9724.json" \
    2> "$run/9724.stderr"

read -r verdict extra missing < <(
  /usr/bin/python3 "$compare" "$run/9724.json" "$gold"
)
echo "RESULT verdict=$verdict extra=$extra missing=$missing"
/usr/bin/grep -E \
  '^BRIDGE-(SATURATION-SEEDS|SATURATION(-COUNTERS|-ARENAS|-UNKNOWN|-PARTIAL|:)|CLASSIFY)|Elapsed \(wall clock\)|Maximum resident set size' \
  "$run/9724.stderr" "$run/9724.time" 2>/dev/null || true
echo "END date=$(date -Is)"
