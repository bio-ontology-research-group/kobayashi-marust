#!/bin/bash
#SBATCH --job-name=km-v14-1194-cl71-prod
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=2
#SBATCH --mem=20G
#SBATCH --time=00:03:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-pred-singleton-20260901/cl0000071-product/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-pred-singleton-20260901/cl0000071-product
binary=/ibex/scratch/hohndor/km/v1.4-pred-singleton-20260901/km
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == 0f8b4fa359db4af14f6bb0dc345302d7ee545bb66d20a329c0eccc18de2a4286 ]]
set +e
timeout --signal=TERM --kill-after=5 90 \
  env KM_ABSORB=1 KM_THREADS=1 KM_QUERIES=CL_0000071 \
      KM_FWD_HEAD_SUBSET_MAX=8 KM_PROF=1 KM_PRED_PRODUCT=100000 \
  /usr/bin/time -v -o "$root/time.txt.tmp" "$binary" engine < "$clauses" \
  > "$root/classification.json.tmp" 2> "$root/stderr.txt.tmp"
rc=$?
set -e
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
mv "$root/time.txt.tmp" "$root/time.txt"
rm -f "$root/classification.json.tmp"
echo "rc=$rc"
grep 'KM_PRED_PRODUCT' "$root/stderr.txt" | tail -64 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$root/time.txt" || true
exit 0
