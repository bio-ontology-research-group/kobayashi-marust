#!/bin/bash
#SBATCH --job-name=km-14817-ge-full
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/km-ge-full-%j.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
binary=$root/km-14817-atleast
ontology=$km_root/corpus/ore_ont_14817.owl
gold=$km_root/gold/konclude__ore_ont_14817.owl.sig.gz
compare=$km_root/fullsweep/cmp_gold.py
run=$root/km-atleast-port-full
mkdir -p "$run" "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
set +e
/usr/bin/time -v -o "$run/14817.time" \
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
    KM_HT_SATEXP_STATS=1 \
    KM_SAT_COUNTERS=1 \
    "$binary" classify "$ontology" \
    > "$run/14817.json" \
    2> "$run/14817.stderr"
status=$?
set -e

if [ "$status" -eq 0 ]; then
  read -r verdict extra missing < <(
    /usr/bin/python3 "$compare" "$run/14817.json" "$gold"
  )
else
  verdict=timeout-or-error
  extra=0
  missing=0
fi
echo "RESULT exit=$status verdict=$verdict extra=$extra missing=$missing"
/usr/bin/grep -E \
  '^(SATEXP-STATS|BRIDGE-(PHASE|SATURATION|DEFER|PREPARE|VERIFY|CLASSIFY)|PROGRESS-SAT|HT-STATS)' \
  "$run/14817.stderr" | tail -n 360 || true
/usr/bin/grep -E 'Elapsed \(wall clock\)|Maximum resident set size' "$run/14817.time" || true
echo "END date=$(date -Is)"
