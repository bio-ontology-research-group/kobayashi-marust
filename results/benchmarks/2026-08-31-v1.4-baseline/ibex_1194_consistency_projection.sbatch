#!/bin/bash
#SBATCH --job-name=km-v14-1194-proj
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --nodes=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --time=00:12:00
#SBATCH --array=0-2%3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-1194-projection-20260831/slurm-%A_%a.out

set -euo pipefail

budgets=(3 60 240)
budget=${budgets[$SLURM_ARRAY_TASK_ID]}
prototype=/ibex/scratch/hohndor/km/v110-empty-query-v9-20260825
binary=$prototype/km
checker=$prototype/ht-rooted-ordinary-production-run-check
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
root=/ibex/scratch/hohndor/km/v14-1194-projection-20260831
out=$root/budget-$budget
mkdir -p "$out"

[[ $(sha256sum "$binary" | cut -d' ' -f1) == b21eda4be9081f0a9850fb54fc14a6a72e3e259b0b3a16141d6eb30ba61bfe3d ]]
[[ $(sha256sum "$checker" | cut -d' ' -f1) == b86a5c40bc31f58b9c82a86149ceee25499d769173c2b26844dfc7a589045d5b ]]
[[ $(sha256sum "$ontology" | cut -d' ' -f1) == 72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2 ]]

set +e
/usr/bin/time -v -o "$out/time.txt" \
  timeout --signal=TERM --kill-after=10 650 \
  env KM_ROUTE=auto \
      KM_TIMING=1 \
      KM_DISJOINT_UNION_TRACE=1 \
      KM_ABOX_DISJOINT_UNION_CHECK=1 \
      KM_ABOX_DISJOINT_UNION_BUDGET_S="$budget" \
      KM_HT_TOTAL_GLOBAL_ROOTED_ORDINARY_RUN_CHECKER="$checker" \
      "$binary" classify "$ontology" \
      > "$out/result.json.tmp" 2> "$out/stderr.txt.tmp"
rc=$?
set -e
mv "$out/stderr.txt.tmp" "$out/stderr.txt"
if [[ -s "$out/result.json.tmp" ]]; then
  /usr/bin/python3 -m json.tool "$out/result.json.tmp" > "$out/result.pretty.json"
  mv "$out/result.json.tmp" "$out/result.json"
else
  rm -f "$out/result.json.tmp"
fi
{
  echo "rc=$rc"
  echo "budget_s=$budget"
  echo "binary_sha256=$(sha256sum "$binary" | cut -d' ' -f1)"
  echo "checker_sha256=$(sha256sum "$checker" | cut -d' ' -f1)"
  echo "ontology_sha256=$(sha256sum "$ontology" | cut -d' ' -f1)"
  echo "result_present=$([[ -s "$out/result.json" ]] && echo true || echo false)"
} > "$out/receipt.txt"
cat "$out/receipt.txt"
grep -E 'KM_DISJOINT_UNION|KM_TIMING|Maximum resident|Elapsed' "$out/stderr.txt" "$out/time.txt" || true
