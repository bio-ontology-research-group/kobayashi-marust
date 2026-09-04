#!/bin/bash
#SBATCH --job-name=km-v14-1194-cb-grab-sweep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:05:00
#SBATCH --array=0-2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-grab-sweep/slurm-%A_%a.out

set -euo pipefail
grab_options=(8 16 32)
grab=${grab_options[$SLURM_ARRAY_TASK_ID]}
threads=8
base=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-grab-sweep
root=$base/grab-$grab
binary=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/km
expected=f194292a2aa8ad7d15f7bde95ab659345cac8a6aa81c38596daee9e46125d6d3
clauses=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/cb-profile-direct/clauses.json
mkdir -p "$base" "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ -s "$clauses" ]]
set +e
timeout --signal=TERM --kill-after=5 240 \
  env KM_ABSORB=1 KM_THREADS="$threads" KM_GUIDED_GRAB_MAX="$grab" \
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
echo "threads=$threads grab=$grab rc=$rc"
if [[ $rc -eq 0 ]]; then
  sha256sum "$root/classification.json"
  wc -c "$root/classification.json"
fi
grep -E 'Elapsed|Maximum resident|Exit status' "$root/time.txt" || true
