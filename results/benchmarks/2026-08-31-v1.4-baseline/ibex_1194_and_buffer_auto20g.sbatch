#!/bin/bash
#SBATCH --job-name=km-v14-1194-andbuf-auto
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:06:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-and-buffer-20260901/auto/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-and-buffer-20260901
out=$root/auto
binary=$root/km-ibex
expected_binary=9f1a666f16fec0dc761f76b8458912ce88fbcd71cd93b0b79055e4159c39f8c8
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary" ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
rm -f "$out"/{classification.json,classification.json.tmp,stderr.txt.tmp,time.txt.tmp}
set +e
/usr/bin/time -v -o "$out/time.txt.tmp" timeout --signal=TERM --kill-after=10 260 \
  env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$ontology" \
  > "$out/classification.json.tmp" 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/time.txt.tmp" "$out/time.txt"
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
if [[ $rc -eq 0 ]]; then
  [[ -s "$out/classification.json.tmp" ]]
  python3 - "$out/classification.json.tmp" <<'PY'
import json, sys
with open(sys.argv[1]) as handle:
    value = json.load(handle)
assert isinstance(value, dict)
assert isinstance(value.get("subsumptions"), list)
assert isinstance(value.get("unsatisfiable"), list)
PY
  mv "$out/classification.json.tmp" "$out/classification.json"
else
  rm -f "$out/classification.json.tmp"
fi
echo "rc=$rc"
if [[ $rc -eq 0 ]]; then sha256sum "$out/classification.json"; wc -c "$out/classification.json"; fi
grep -E 'KM_TIMING|Elapsed|Maximum resident|Exit status' "$out/stderr.txt" "$out/time.txt" || true
exit "$rc"
