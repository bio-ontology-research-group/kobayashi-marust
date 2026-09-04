#!/bin/bash
#SBATCH --job-name=km-v14-1194-batch40k
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:12:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-msgprof-core-20260901/batch40k/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-msgprof-core-20260901
out=$root/batch40k
binary=$root/km
expected_binary=75adde7f7456a63be3b0635db3545e0d65e9a1f083d45ad5d85ae9010ae08db7
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary" ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
rm -f "$out/classification.json" "$out/classification.json.tmp"
set +e
/usr/bin/time -v -o "$out/time.txt.tmp" timeout --signal=TERM --kill-after=10 700 \
  env KM_ROUTE=auto KM_TIMING=1 KM_BRIDGE_SUBJECT_BATCH=40000 "$binary" classify "$ontology" \
  > "$out/classification.json.tmp" 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/time.txt.tmp" "$out/time.txt"
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
if [[ $rc -eq 0 ]]; then
  [[ -s "$out/classification.json.tmp" ]]
  mv "$out/classification.json.tmp" "$out/classification.json"
else
  rm -f "$out/classification.json.tmp"
fi
echo "rc=$rc"
if [[ $rc -eq 0 ]]; then sha256sum "$out/classification.json"; wc -c "$out/classification.json"; fi
grep -E 'KM_TIMING|Elapsed|Maximum resident|Exit status' "$out/stderr.txt" "$out/time.txt" || true
exit "$rc"
