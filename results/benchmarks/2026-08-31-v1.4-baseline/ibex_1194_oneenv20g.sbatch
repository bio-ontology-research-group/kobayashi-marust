#!/bin/bash
#SBATCH --job-name=km-v14-1194-oneenv
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:09:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-bridge-memtrace-20260901/oneenv/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-bridge-memtrace-20260901
out=$root/oneenv
binary=$root/km-ibex
expected_binary=c1426bdf60e57bbdc098c3a2a42ff0081c481c9e11f11889b9ae532a7b48bcd6
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary" ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
rm -f "$out"/{classification.json,classification.json.tmp,stderr.txt.tmp,time.txt.tmp}
set +e
/usr/bin/time -v -o "$out/time.txt.tmp" timeout --signal=TERM --kill-after=10 510 \
  env KM_ROUTE=auto KM_TIMING=1 KM_BRIDGE_MEM=1 KM_BRIDGE_PHASES=1 \
      KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_HT_SATURATION_BUDGET_S=180 \
      "$binary" classify "$ontology" \
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
grep -E 'BRIDGE-PHASE|BRIDGE-MEM|KM_TIMING' "$out/stderr.txt" | tail -100 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$out/time.txt" || true
exit "$rc"
