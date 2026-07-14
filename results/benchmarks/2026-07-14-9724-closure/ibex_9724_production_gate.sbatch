#!/bin/bash
#SBATCH --job-name=km-9724-prod
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/production-gate-%j.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
binary=$root/km-9724-freelist-candidate
ontology=$km_root/corpus/ore_ont_9724.owl
gold=$km_root/gold/konclude__ore_ont_9724.owl.sig.gz
compare=$km_root/fullsweep/cmp_gold.py
run=$root/production-gate
mkdir -p "$run" "$root/slurm"

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

set +e
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
    KM_BRIDGE_PHASES=1 \
    KM_SAT_COUNTERS=1 \
    "$binary" classify "$ontology" \
    > "$run/9724.json" \
    2> "$run/9724.stderr"
status=$?
set -e

if [ "$status" -eq 0 ]; then
  read -r verdict extra missing < <(
    /usr/bin/python3 "$compare" "$run/9724.json" "$gold"
  )
else
  verdict=error
  extra=0
  missing=0
fi
echo "RESULT exit=$status verdict=$verdict extra=$extra missing=$missing"
/usr/bin/grep -E \
  '^BRIDGE-(PHASE|SATURATION-SEEDS|SATURATION(-TIMEOUT|-COUNTERS|-ARENAS|-UNKNOWN|-PARTIAL|:)|CLASSIFY)' \
  "$run/9724.stderr" 2>/dev/null || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Maximum resident set size' \
  "$run/9724.time" 2>/dev/null || true
echo "END date=$(date -Is)"
