#!/bin/bash
#SBATCH --job-name=km-9663-cand
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9663_closure_20260714/slurm/km-candidate-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km
run=$root/9663_closure_20260714/km-candidate
binary=$root/9663_closure_20260714/km-9663-bullseye
ontology=$root/corpus/ore_ont_9663.owl
gold=$root/gold/konclude__ore_ont_9663.owl.sig.gz
compare=$root/fullsweep/cmp_gold.py

mkdir -p "$run" "$root/9663_closure_20260714/slurm"
sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

/usr/bin/time -v -o "$run/9663.time" \
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
    KM_BRIDGE_PHASES=1 \
    KM_SAT_COUNTERS=1 \
    "$binary" classify "$ontology" \
    > "$run/9663.json" \
    2> "$run/9663.stderr"

read -r verdict extra missing < <(/usr/bin/python3 "$compare" "$run/9663.json" "$gold")
echo "RESULT verdict=$verdict extra=$extra missing=$missing"
/usr/bin/grep -E \
  'BRIDGE-(PHASE|SATURATION|CLASSIFY)|KM_SAT_DEBUG|SAT-(STATS|COUNTERS)' \
  "$run/9663.stderr" || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Maximum resident set size' \
  "$run/9663.time" || true
echo "END date=$(date -Is)"
