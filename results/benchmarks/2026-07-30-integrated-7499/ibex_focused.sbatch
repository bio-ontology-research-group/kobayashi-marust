#!/bin/bash
# Source-bound acceptance gate for the integrated feature router plus the
# measurement-only cardinality route restored for ore_ont_7499.
# Every listed case is required to finish and match the Konclude signature.
#SBATCH --job-name=km-int7499-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/integrated-7499-20260730/slurm-%x-%j.out

set -uo pipefail
root=/ibex/scratch/hohndor/km/integrated-7499-20260730
km_root=/ibex/scratch/hohndor/km
bin=$root/km
out=$root/focused-$SLURM_JOB_ID
mkdir -p "$out"

sha256sum "$bin"
fail=0

run_case() {
  local id=$1
  local route=$2
  local ont=$km_root/corpus/ore_ont_$id.owl
  local gold=$km_root/gold/konclude__ore_ont_$id.owl.sig.gz
  local stem=$id-$route

  env KM_THREADS=16 KM_ROUTE="$route" \
    /usr/bin/time -f "%e %M" -o "$out/$stem.time" \
    timeout 240 "$bin" classify "$ont" \
    > "$out/$stem.json" 2> "$out/$stem.err"
  local rc=$?
  local stats
  stats=$(/usr/bin/tail -1 "$out/$stem.time" 2>/dev/null)
  if [[ $rc -ne 0 ]]; then
    echo "GATE ont=$id route=$route rc=$rc stats=[$stats] FAIL"
    fail=1
    return
  fi

  local verdict
  verdict=$(/usr/bin/python3 "$root/kmsig.py" "$out/$stem.json" "$gold" |
    /usr/bin/tr '\n' ' ')
  echo "GATE ont=$id route=$route rc=0 stats=[$stats] $verdict"
  if [[ $verdict != *EXACT_MATCH* ]]; then
    fail=1
  fi
  rm -f "$out/$stem.json"
}

for id in 148 3215 3560 4054 4755 6477 7127 7581 7914 8068 8864 9540 \
          9663 9724 10621 11315 11745 12414 14817; do
  run_case "$id" auto
done
run_case 7499 certified_card_proxy_abox

if [[ $fail -ne 0 ]]; then
  echo "INTEGRATED_7499_GATE_FAILED job=$SLURM_JOB_ID"
  exit 1
fi
echo "INTEGRATED_7499_GATE_COMPLETE job=$SLURM_JOB_ID"
