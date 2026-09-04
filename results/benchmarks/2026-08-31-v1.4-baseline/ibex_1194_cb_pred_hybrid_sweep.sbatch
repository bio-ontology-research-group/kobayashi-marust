#!/bin/bash
#SBATCH --job-name=km-v14-1194-pred-hybrid-sweep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:06:00
#SBATCH --array=0-3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-sweep-20260901/gate/slurm-%A_%a.out
set -euo pipefail

root=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-sweep-20260901
binary=$root/km
expected=03e2b50cac439cf239f71983bd1f25d07854f92264923772cf59dc8aa839ec52
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
thresholds=(64 256 1024 1000000)
threshold=${thresholds[$SLURM_ARRAY_TASK_ID]}
out=$root/gate/threshold-$threshold
mkdir -p "$out"

[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(stat -c %s "$clauses") -gt 200000000 ]]
rm -f "$out/classification.json" "$out/classification.json.tmp"

set +e
timeout --signal=TERM --kill-after=5 240 \
  env KM_ABSORB=1 KM_THREADS=1 KM_QUERIES=CL_0000071 \
      KM_FWD_HEAD_SUBSET_MAX=8 KM_PRED_TRIE_MIN_LIVE="$threshold" \
      KM_PROF=1 KM_PROF_TIME=1 KM_CTXSPLIT=1 \
  /usr/bin/time -v -o "$out/time.txt.tmp" "$binary" engine < "$clauses" \
  > "$out/classification.json.tmp" 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
mv "$out/time.txt.tmp" "$out/time.txt"

if [[ $rc -eq 0 ]]; then
  [[ -s "$out/classification.json.tmp" ]]
  grep -q 'CL_0000071' "$out/classification.json.tmp"
  mv "$out/classification.json.tmp" "$out/classification.json"
else
  rm -f "$out/classification.json.tmp"
fi

echo "threshold=$threshold rc=$rc"
if [[ $rc -eq 0 ]]; then
  sha256sum "$out/classification.json"
  wc -c "$out/classification.json"
fi
grep -E 'KM_CTXSPLIT|KM_PROF msgloop|KM_PROF\[time-ms\] msgloop' "$out/stderr.txt" | tail -8 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$out/time.txt" || true
exit "$rc"
