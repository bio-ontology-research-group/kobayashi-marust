#!/bin/bash
#SBATCH --job-name=km-v14-1194-eq-msgprof
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:06:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-eq-index-20260901/msgprof/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-eq-index-20260901
out=$root/msgprof
binary=$root/km
expected=6d22d524c80a9d1097c01b8d2bee3f4689ceec5d018dc2e574013b02ddd6b043
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(stat -c %s "$clauses") -gt 200000000 ]]
set +e
/usr/bin/time -v -o "$out/time.txt.tmp" timeout --signal=TERM --kill-after=5 240 \
  env KM_ABSORB=1 KM_THREADS=1 KM_QUERIES=CL_0000071 KM_MSG_CAP=100000000 \
      KM_FWD_HEAD_SUBSET_MAX=8 KM_PRED_TRIE_MIN_LIVE=1000000 \
      KM_PROF=1 KM_PROF_TIME=1 KM_MSGPROF=1 \
  "$binary" engine < "$clauses" > /dev/null 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
mv "$out/time.txt.tmp" "$out/time.txt"
echo "msgprof=1 rc=$rc"
grep -E 'KM_MSGPROF arrivals|KM_MSGPROF sender|KM_PROF msgloop' "$out/stderr.txt" | tail -30 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$out/time.txt" || true
exit "$rc"
