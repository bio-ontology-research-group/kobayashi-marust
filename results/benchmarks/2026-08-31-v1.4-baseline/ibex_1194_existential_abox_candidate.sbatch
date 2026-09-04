#!/bin/bash
#SBATCH --job-name=km-v14-1194-abox
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:05:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-1194-existential-abox-bottom-fix-20260901/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v14-1194-existential-abox-bottom-fix-20260901
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
binary=/ibex/scratch/hohndor/km/v14-existential-abox-bottom-fix-20260901/km-ibex
expected_binary_sha=${KM_CANDIDATE_SHA:?submit with KM_CANDIDATE_SHA}
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary_sha" ]]
mkdir -p "$root"

set +e
/usr/bin/time -v -o "$root/time.txt.tmp" \
  timeout --signal=TERM --kill-after=10 260 \
  env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$ontology" \
  > "$root/classification.json.tmp" 2> "$root/stderr.txt.tmp"
rc=$?
set -e
mv "$root/time.txt.tmp" "$root/time.txt"
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
if [[ $rc -eq 0 ]]; then
  mv "$root/classification.json.tmp" "$root/classification.json"
else
  rm -f "$root/classification.json.tmp"
fi
{
  echo "job=$SLURM_JOB_ID"
  echo "host=$(hostname)"
  echo "ontology_sha256=$ontology_sha"
  echo "binary_sha256=$expected_binary_sha"
  echo "rc=$rc"
  if [[ $rc -eq 0 ]]; then
    echo "output_sha256=$(sha256sum "$root/classification.json" | cut -d' ' -f1)"
    echo "output_bytes=$(wc -c < "$root/classification.json")"
  fi
} > "$root/receipt.txt"
cat "$root/receipt.txt"
grep -E 'KM_TIMING|Elapsed|Maximum resident|Exit status' "$root/stderr.txt" "$root/time.txt" || true
