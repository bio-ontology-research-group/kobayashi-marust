#!/bin/bash
#SBATCH --job-name=km-9724-stack
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/stack-samples-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
binary=$km_root/9663_closure_20260714/km-9663-final-bullseye
tin=$root/standalone/9724.tin.json
run=$root/stack-samples
mkdir -p "$run" "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is)"
set +e
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
  KM_HT_SATURATION_BUDGET_S=150 \
  KM_BRIDGE_PROBE_BUDGET_S=1 \
  KM_BRIDGE_RETRY_ROUNDS=0 \
  KM_BRIDGE_PROGRESS=1 \
  KM_SAT_COUNTERS=1 \
  "$binary" tableau \
  < "$tin" \
  > "$run/9724.json" \
  2> "$run/9724.stderr" &
pid=$!
echo "PID $pid"

sample=0
for delay in 15 15 30 30 30; do
  /usr/bin/sleep "$delay"
  if /usr/bin/kill -0 "$pid" 2>/dev/null; then
    sample=$((sample + 1))
    echo "SAMPLE $sample date=$(date -Is)"
    /usr/bin/pstack "$pid" > "$run/stack-$sample.txt" 2>&1
  fi
done

wait "$pid"
status=$?
set -e
echo "RESULT exit=$status samples=$sample"
for stack in "$run"/stack-*.txt; do
  echo "STACK $stack"
  /usr/bin/sed -n '1,100p' "$stack"
done
echo "END date=$(date -Is)"
