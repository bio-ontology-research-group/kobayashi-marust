#!/bin/bash
#SBATCH --job-name=km-v14-1194-pred-hybrid
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:06:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-20260901/gate/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-20260901/gate
binary=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-20260901/km
expected=f5694ff7c90ae00945d004379f2c76e18a88ce8fb2f72d93e4d841bce4cbbeb8
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(stat -c %s "$clauses") -gt 200000000 ]]
set +e
timeout --signal=TERM --kill-after=5 240 \
  env KM_ABSORB=1 KM_THREADS=1 KM_QUERIES=CL_0000071 \
      KM_FWD_HEAD_SUBSET_MAX=8 KM_PROF=1 KM_PROF_TIME=1 KM_CTXSPLIT=1 \
  /usr/bin/time -v -o "$root/time.txt.tmp" "$binary" engine < "$clauses" \
  > "$root/classification.json.tmp" 2> "$root/stderr.txt.tmp"
rc=$?
set -e
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
mv "$root/time.txt.tmp" "$root/time.txt"
if [[ $rc -eq 0 ]]; then
  [[ -s "$root/classification.json.tmp" ]]
  grep -q 'CL_0000071' "$root/classification.json.tmp"
  mv "$root/classification.json.tmp" "$root/classification.json"
else
  rm -f "$root/classification.json.tmp"
fi
echo "rc=$rc"
if [[ $rc -eq 0 ]]; then sha256sum "$root/classification.json"; wc -c "$root/classification.json"; fi
grep -E 'KM_CTXSPLIT|KM_PROF msgloop|KM_PROF\[time-ms\] msgloop' "$root/stderr.txt" | tail -8 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$root/time.txt" || true
exit "$rc"
