#!/bin/bash
#SBATCH --job-name=km-9724-eustack
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:07:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/eustack-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/9724_closure_20260714
binary=$root/km-9724-cursor-candidate
tin=$root/standalone/9724.tin.json
run=$root/eustack
mkdir -p "$run" "$root/slurm"
rm -f "$run"/stack-*.txt "$run"/9724.json "$run"/9724.stderr

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"

export KM_HT=1
export KM_HT_BRIDGE=1
export KM_HT_BRIDGE_ONLY=1
export KM_HT_FORCE=1
export KM_HT_CARD=1
export KM_HT_PAR=1
export KM_HT_QO_SHIQ=1
export KM_HT_BLOCK=5
export KM_HT_EAGER=1
export KM_HT_NEGTRIED=1
export KM_HT_ORD=1
export KM_HT_INCRBLOCK2=1
export KM_HT_INCROBLIG=1
export KM_TRIGGER_ABSORB=1
export KM_KEEP_CHAIN_AXIOMS=1
export KM_HT_SATURATION=1
export KM_HT_SATCACHE=1
export KM_BRIDGE_DUMP_UNSUP=20
export KM_HT_SATURATION_BUDGET_S=240
export KM_BRIDGE_PROBE_BUDGET_S=1
export KM_BRIDGE_RETRY_ROUNDS=0
export KM_HT_STATS=1
export KM_BRIDGE_PROGRESS=1
export KM_SAT_COUNTERS=1

"$binary" tableau < "$tin" > "$run/9724.json" 2> "$run/9724.stderr" &
pid=$!
echo "PID $pid"

sample_stack() {
    local elapsed=$1
    if kill -0 "$pid" 2>/dev/null; then
        echo "SAMPLE elapsed=$elapsed date=$(date -Is)"
        /usr/bin/eu-stack -p "$pid" > "$run/stack-$elapsed.txt" 2>&1 || true
    fi
}

sleep 30
sample_stack 30
sleep 60
sample_stack 90
sleep 70
sample_stack 160
sleep 60
sample_stack 220

set +e
wait "$pid"
status=$?
set -e

echo "RESULT exit=$status"
for stack in "$run"/stack-*.txt; do
    echo "STACK $stack"
    /usr/bin/sed -n '1,120p' "$stack"
done
/usr/bin/grep -E '^BRIDGE-SATURATION-(TIMEOUT|COUNTERS|ARENAS|PARTIAL)' "$run/9724.stderr" || true
echo "END date=$(date -Is)"
