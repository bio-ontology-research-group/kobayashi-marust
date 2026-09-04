#!/bin/bash
#SBATCH --job-name=km-v14-1194-hs-prof
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:05:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-head-subset-profile/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-head-subset-profile
binary=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/km
expected=02c68056c1b01ecb04a6ea98fce1e60b81f4bee547714f303281aded603be533
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(stat -c %s "$clauses") -gt 200000000 ]]
set +e
timeout --signal=TERM --kill-after=5 60 \
  env KM_ABSORB=1 KM_THREADS=2 KM_GUIDED_GRAB_MAX=10000 \
      KM_FWD_HEAD_SUBSET_MAX=8 KM_PROF=1 KM_PROF_TIME=1 \
  /usr/bin/time -v -o "$root/time.txt.tmp" "$binary" engine < "$clauses" \
  > "$root/classification.json.tmp" 2> "$root/stderr.txt.tmp"
rc=$?
set -e
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
mv "$root/time.txt.tmp" "$root/time.txt"
if [[ $rc -eq 0 ]]; then
  mv "$root/classification.json.tmp" "$root/classification.json"
else
  rm -f "$root/classification.json.tmp"
fi
echo "rc=$rc"
if [[ $rc -eq 0 ]]; then
  [[ -s "$root/classification.json" ]]
  sha256sum "$root/classification.json"
  wc -c "$root/classification.json"
fi
grep -E 'Elapsed|Maximum resident|Exit status' "$root/time.txt"
grep -q 'KM_PROF' "$root/stderr.txt"
