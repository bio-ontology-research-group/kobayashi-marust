#!/bin/bash
#SBATCH --job-name=km-v14-1194-cb
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodelist=cn512-15-r
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:05:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/projected-cb8-grab96/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/projected-cb8-grab96
binary=/ibex/scratch/hohndor/km/v1.4.0-batched-candidate-20260901/km
expected=4a297509269f236ef228d220850ef29b41f56f4a6b68e84db0b223bd18f3348d
ontology=/ibex/scratch/hohndor/km/v14-1194-tbox-only-20260901/ore_ont_1194.tbox.owl
mkdir -p "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == 31e6c1893e143e7b356358de52e29c21336229af03bc0ae706da8a9717493903 ]]

set +e
/usr/bin/time -v -o "$root/time.txt.tmp" \
  timeout --signal=TERM --kill-after=5 240 \
  env KM_ROUTE=cb_absorb8 KM_TIMING=1 KM_CENTRAL_TIME_CAP=225 KM_PAR_MEM_GB=19.5 \
  KM_GUIDED_GRAB_MAX=96 \
  "$binary" classify "$ontology" \
  > "$root/classification.json.tmp" 2> "$root/stderr.txt.tmp"
rc=$?
set -e
mv "$root/time.txt.tmp" "$root/time.txt"
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
if [[ $rc -eq 0 ]]; then
  mv "$root/classification.json.tmp" "$root/classification.json"
else
  unlink "$root/classification.json.tmp"
fi
echo "rc=$rc"
if [[ $rc -eq 0 ]]; then
  sha256sum "$root/classification.json"
  wc -c "$root/classification.json"
fi
grep -E 'KM_TIMING' "$root/stderr.txt" || true
grep -E 'Elapsed|Maximum resident|Exit status' "$root/time.txt" || true
