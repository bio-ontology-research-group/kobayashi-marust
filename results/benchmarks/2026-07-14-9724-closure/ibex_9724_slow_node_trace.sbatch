#!/bin/bash
#SBATCH --job-name=km-9724-slow
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/slow-node-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
binary=$root/km-9724-slow-debug
tin=$root/standalone/9724.tin.json
run=$root/slow-node
mkdir -p "$run" "$root/slurm"

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

set +e
/usr/bin/time -v -o "$run/9724.time" \
  /usr/bin/timeout -k 5 240 \
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
    KM_BRIDGE_DUMP_UNSUP=20 \
    KM_BRIDGE_PHASES=1 \
    KM_HT_SATURATION_BUDGET_S=180 \
    KM_BRIDGE_PROBE_BUDGET_S=1 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_STATS=1 \
    KM_BRIDGE_PROGRESS=1 \
    KM_SAT_COUNTERS=1 \
    KM_SAT_SLOW_NODE_MS=100 \
    "$binary" tableau \
    < "$tin" \
    > "$run/9724.json" \
    2> "$run/9724.stderr"
status=$?
set -e

echo "RESULT exit=$status"
/usr/bin/grep -E \
  '^BRIDGE-SATURATION-(SLOW-NODE|SEEDS|TIMEOUT|COUNTERS|ARENAS|UNKNOWN|PARTIAL)|Elapsed \(wall clock\)|Maximum resident set size' \
  "$run/9724.stderr" "$run/9724.time" 2>/dev/null || true
echo "END date=$(date -Is)"
