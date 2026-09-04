#!/bin/bash
#SBATCH --job-name=km-v14-1194-seeds
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:06:00
#SBATCH --array=0-15%8
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-seeded-order-20260901/seed-%A_%a.out
set -euo pipefail
seed=$SLURM_ARRAY_TASK_ID
root=/ibex/scratch/hohndor/km/v1.4-seeded-order-20260901
out=$root/seed-$seed
binary=$root/km-ibex
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
ontology_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
mkdir -p "$out"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == $(cut -d' ' -f1 < "$root/km-ibex.sha256") ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == "$ontology_sha" ]]
rm -f "$out"/{classification.json,classification.json.tmp,stderr.txt.tmp,time.txt.tmp,status.tsv.tmp}
start=$(date +%s)
set +e
/usr/bin/time -v -o "$out/time.txt.tmp" timeout --signal=TERM --kill-after=10 260 \
  env KM_ROUTE=auto KM_TIMING=1 KM_SAT_SUCCESSOR_ORDER=seeded \
  KM_SAT_SUCCESSOR_SEED="$seed" "$binary" classify "$ontology" \
  > "$out/classification.json.tmp" 2> "$out/stderr.txt.tmp"
rc=$?
set -e
end=$(date +%s)
mv "$out/time.txt.tmp" "$out/time.txt"
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
valid=0
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
  valid=1
else
  rm -f "$out/classification.json.tmp"
fi
printf 'seed\trc\tvalid\telapsed_s\n%s\t%s\t%s\t%s\n' \
  "$seed" "$rc" "$valid" "$((end-start))" > "$out/status.tsv.tmp"
mv "$out/status.tsv.tmp" "$out/status.tsv"
echo "seed=$seed rc=$rc valid=$valid elapsed_s=$((end-start))"
if [[ $valid -eq 1 ]]; then
  sha256sum "$out/classification.json"
  wc -c "$out/classification.json"
fi
grep -E 'KM_TIMING|Elapsed|Maximum resident|Exit status' "$out/stderr.txt" "$out/time.txt" || true
exit "$rc"
