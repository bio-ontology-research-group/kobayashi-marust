#!/bin/bash
#SBATCH --job-name=km-v14-1194-grab1536-full
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:05:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-guided-grab-20260901/grab-1536-full/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-guided-grab-20260901/grab-1536-full
binary=/ibex/scratch/hohndor/km/v1.4-guided-grab-20260901/km
expected=73dfb8dacf6e215241f71f721c99d0181a7dcefe83c74ce272b31287af962d95
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(stat -c %s "$clauses") -gt 200000000 ]]
set +e
timeout --signal=TERM --kill-after=5 240 \
  env KM_ABSORB=1 KM_THREADS=2 KM_GUIDED_GRAB_MAX=1536 \
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
grep 'KM_PROF seeded all' "$root/stderr.txt" | tail -4 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$root/time.txt" || true
