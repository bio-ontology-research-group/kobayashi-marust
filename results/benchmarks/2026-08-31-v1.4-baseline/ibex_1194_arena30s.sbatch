#!/bin/bash
#SBATCH --job-name=km-v14-1194-arena30s
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:03:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-and-buffer-20260901/arena30/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-and-buffer-20260901
out=$root/arena30
binary=$root/km-ibex
expected_binary=9f1a666f16fec0dc761f76b8458912ce88fbcd71cd93b0b79055e4159c39f8c8
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary" ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
set +e
/usr/bin/time -v -o "$out/time.txt.tmp" timeout --signal=TERM --kill-after=10 150 \
  env KM_ROUTE=manual KM_MECHANISM=portfolio KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18 \
      KM_KEEP_CHAIN_AXIOMS=1 KM_HT_ONLY=certified KM_TRIGGER_ABSORB=1 KM_ABSORB=1 \
      KM_BRIDGE_PROBE_BUDGET_S=30 KM_BRIDGE_RETRY_ROUNDS=0 KM_HT_SATURATION_BUDGET_S=30 \
      KM_HT_BRIDGE_SEQUENTIAL=1 KM_BRIDGE_SUBJECT_WORKERS=1 KM_HT_TRACE=1 \
      KM_BRIDGE_PROGRESS=1 KM_SAT_COUNTERS=1 KM_TIMING=1 \
      "$binary" classify "$ontology" \
  > "$out/classification.json.tmp" 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/time.txt.tmp" "$out/time.txt"
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
rm -f "$out/classification.json.tmp"
echo "rc=$rc"
grep -E 'BRIDGE-SATURATION-(TIMEOUT|COUNTERS|ARENAS|LARGEST-LABEL)|BRIDGE-SAT-PHASE|KM_TIMING sequential' "$out/stderr.txt" | tail -100 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$out/time.txt" || true
exit 0
