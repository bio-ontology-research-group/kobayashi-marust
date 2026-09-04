#!/bin/bash
#SBATCH --job-name=km-v14-1194-pred-shape
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:03:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/pred-shape/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/pred-shape
binary=/ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/km
expected=3308d1cc6d76aafa4a6f8db2125545d2ec5e3f86ae4c691b7a79cbb881ad1425
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(stat -c %s "$clauses") -gt 200000000 ]]
set +e
timeout --signal=TERM --kill-after=5 120 \
  env KM_ABSORB=1 KM_THREADS=1 KM_QUERIES=CL_0000071 \
      KM_FWD_HEAD_SUBSET_MAX=8 KM_PRED_PRODUCT=100000 KM_PROF=1 KM_PROF_TIME=1 \
  /usr/bin/time -v -o "$root/time.txt.tmp" "$binary" engine < "$clauses" \
  > "$root/classification.json.tmp" 2> "$root/stderr.txt.tmp"
rc=$?
set -e
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
mv "$root/time.txt.tmp" "$root/time.txt"
rm -f "$root/classification.json.tmp"
echo "rc=$rc"
grep 'KM_PRED_PRODUCT' "$root/stderr.txt" | tail -64 || true
exit "$rc"
