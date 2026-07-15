#!/bin/bash
#SBATCH --job-name=km-14817-nbo0042-trace
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:02:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/km-nbo0042-trace-%j.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
binary=$km_root/9724_closure_20260714/km-9724-freelist-candidate
tin=$root/standalone/14817.tin.json
run=$root/km-nbo0042-trace
mkdir -p "$run" "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
set +e
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 55 \
  /usr/bin/env \
    KM_HT=1 \
    KM_HT_BRIDGE=1 \
    KM_HT_BRIDGE_ONLY=1 \
    KM_HT_FORCE=1 \
    KM_HT_CARD=1 \
    KM_HT_PAR=1 \
    KM_HT_QO_SHIQ=1 \
    KM_HT_BLOCK=5 \
    KM_HT_EAGER=1 \
    KM_HT_NEGTRIED=1 \
    KM_HT_ORD=1 \
    KM_HT_INCRBLOCK2=1 \
    KM_HT_INCROBLIG=1 \
    KM_TRIGGER_ABSORB=1 \
    KM_KEEP_CHAIN_AXIOMS=1 \
    KM_HT_SATURATION=1 \
    KM_HT_SATCACHE=1 \
    KM_BRIDGE_ONLY_SUBJECT=73652 \
    KM_HT_SATURATION_BUDGET_S=45 \
    KM_BRIDGE_PROBE_BUDGET_S=45 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_STATS=1 \
    KM_BRIDGE_PROGRESS=1 \
    KM_SAT_COUNTERS=1 \
    KM_SAT_ABSORB_DEBUG=1 \
    "$binary" tableau \
    < "$tin" \
    > "$run/14817.json" \
    2> "$run/14817.stderr"
status=$?
set -e

echo "RESULT exit=$status bytes=$(/usr/bin/stat -c %s "$run/14817.json")"
/usr/bin/grep -E \
  '^(SAT-(ROOT|SUCCESSOR|CACHE)|BRIDGE-(SATURATION|DEFER|PREPARE)|PROGRESS-SAT)' \
  "$run/14817.stderr" | head -n 240 || true
/usr/bin/grep -E 'Elapsed \(wall clock\)|Maximum resident set size' "$run/14817.time" || true
echo "END date=$(date -Is)"
