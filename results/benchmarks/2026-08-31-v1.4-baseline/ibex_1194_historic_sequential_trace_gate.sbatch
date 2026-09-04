#!/bin/bash
#SBATCH --job-name=km-v14-1194-hist-seq-trace
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-historic-sequential-trace-20260901/gate/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v14-historic-sequential-trace-20260901
out=$root/gate
binary=$root/km
expected_binary=d075a10f3dd337bbfb6ee3711c1fa304381ef2901f5a9443476eb3f18667e04a
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary" ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
rm -f "$out/classification.json" "$out/classification.json.tmp"
set +e
/usr/bin/time -v -o "$out/time.txt.tmp" timeout --signal=TERM --kill-after=10 440 \
  env KM_ROUTE=auto KM_TIMING=1 KM_HT_STATS=1 "$binary" classify "$ontology" \
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
grep -E 'KM_TIMING|BRIDGE-|Elapsed|Maximum resident|Exit status' "$out/stderr.txt" "$out/time.txt" || true
exit "$rc"
