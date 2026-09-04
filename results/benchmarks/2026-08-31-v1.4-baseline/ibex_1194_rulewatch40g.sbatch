#!/bin/bash
#SBATCH --job-name=km-v14-1194-rulewatch
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=40G
#SBATCH --time=00:04:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-rulewatch-20260901/run/slurm-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-rulewatch-20260901
out=$root/run
binary=$root/km-ibex
expected_binary=cd822c0e1743524af57831634a21bc45495ea1a1716f1543f615bc90a19ca662
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary" ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
rm -f "$out"/{classification.json.tmp,stderr.txt.tmp,time.txt.tmp}
set +e
/usr/bin/time -v -o "$out/time.txt.tmp" timeout --signal=TERM --kill-after=10 210 \
  env KM_ROUTE=auto KM_TIMING=1 KM_HT_TRACE=1 KM_BRIDGE_MEM=1 \
      KM_BRIDGE_PROGRESS=1 KM_SAT_COUNTERS=1 KM_SAT_RULE_WATCH=1 \
      KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_HT_SATURATION_BUDGET_S=120 \
      "$binary" classify "$ontology" \
  > "$out/classification.json.tmp" 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/time.txt.tmp" "$out/time.txt"
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
rm -f "$out/classification.json.tmp"
echo "rc=$rc"
grep -E 'BRIDGE-SAT-RULE-WATCH|BRIDGE-SATURATION-(TIMEOUT|COUNTERS|ARENAS)|BRIDGE-MEM|KM_TIMING' "$out/stderr.txt" | tail -100 || true
grep -E 'Elapsed|Maximum resident|Exit status' "$out/time.txt" || true
exit "$rc"
