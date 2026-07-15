#!/bin/bash
#SBATCH --job-name=km-14817-s73652
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --array=0-3
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/subject-73652-%A_%a.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
binary=$km_root/9724_closure_20260714/km-9724-freelist-candidate
tin=$root/standalone/14817.tin.json
subject=73652
case "$SLURM_ARRAY_TASK_ID" in
  0) variant=production; extra=() ;;
  1) variant=no-assoc-exp-cache; extra=(KM_HT_NO_ASSOC_EXP_CACHE=1) ;;
  2) variant=no-satcache; extra=(KM_HT_NO_SATCACHE=1) ;;
  3) variant=no-saturation; extra=(KM_HT_NO_SATURATION=1) ;;
esac
run=$root/subject-73652/$variant
mkdir -p "$run" "$root/slurm"

echo "BEGIN variant=$variant host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
set +e
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 180 \
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
    KM_BRIDGE_ONLY_SUBJECT="$subject" \
    KM_HT_SATURATION_BUDGET_S=120 \
    KM_BRIDGE_PROBE_BUDGET_S=120 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_STATS=1 \
    KM_BRIDGE_PROGRESS=1 \
    KM_SAT_COUNTERS=1 \
    "${extra[@]}" \
    "$binary" tableau \
    < "$tin" \
    > "$run/14817.json" \
    2> "$run/14817.stderr"
status=$?
set -e

echo "RESULT variant=$variant exit=$status bytes=$(/usr/bin/stat -c %s "$run/14817.json")"
/usr/bin/grep -E \
  '^(BRIDGE-(SATURATION|DEFER|PREPARE|KPSET|CLASSIFY)|PROGRESS-SAT)|Elapsed \(wall clock\)|Maximum resident set size' \
  "$run/14817.stderr" "$run/14817.time" 2>/dev/null | tail -n 80 || true
echo "END date=$(date -Is)"
