#!/bin/bash
#SBATCH --job-name=km-v14-1194-core-short
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:02:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-msgprof-core-20260901/short/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-msgprof-core-20260901
out=$root/short
binary=$root/km
expected=75adde7f7456a63be3b0635db3545e0d65e9a1f083d45ad5d85ae9010ae08db7
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(stat -c %s "$clauses") -gt 200000000 ]]
set +e
timeout --signal=TERM --kill-after=5 45 \
  env KM_ABSORB=1 KM_THREADS=1 KM_QUERIES=CL_0000071 KM_MSG_CAP=100000000 \
      KM_FWD_HEAD_SUBSET_MAX=8 KM_PRED_TRIE_MIN_LIVE=1000000 KM_PROF=1 KM_MSGPROF=1 \
  "$binary" engine < "$clauses" > /dev/null 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
echo "short_core_profile=1 rc=$rc"
grep -E 'KM_MSGPROF arrivals|KM_MSGPROF sender' "$out/stderr.txt" | tail -18 || true
exit "$rc"
