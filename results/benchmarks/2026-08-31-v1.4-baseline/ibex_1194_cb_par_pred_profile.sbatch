#!/bin/bash
#SBATCH --job-name=km-v14-1194-par-pred-2e
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-par-pred-20260901/ore1194-2e-full/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-par-pred-20260901/ore1194-2e-full
binary=/ibex/scratch/hohndor/km/v1.4-par-pred-20260901/km
expected=7be7d1965eb5dbbbccca078852d9a1742a7308abd8191efdd3c61efc3d59bfbe
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(stat -c %s "$clauses") -gt 200000000 ]]
set +e
timeout --signal=TERM --kill-after=5 240 \
  env KM_ABSORB=1 KM_THREADS=2 RAYON_NUM_THREADS=4 KM_PAR_PRED_BATCH=1 \
      KM_FWD_HEAD_SUBSET_MAX=8 KM_PROF=1 \
  /usr/bin/time -v -o "$root/time.txt.tmp" "$binary" engine < "$clauses" \
  > "$root/classification.json.tmp" 2> "$root/stderr.txt.tmp"
rc=$?
set -e
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
mv "$root/time.txt.tmp" "$root/time.txt"
if [[ $rc -eq 0 ]]; then
  mv "$root/classification.json.tmp" "$root/classification.json"
  [[ -s "$root/classification.json" ]]
else
  rm -f "$root/classification.json.tmp"
fi
echo "rc=$rc"
grep 'KM_PROF msgloop' "$root/stderr.txt" | tail -4 || true
grep 'KM_PROF seeded all' "$root/stderr.txt" | tail -2 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$root/time.txt" || true
