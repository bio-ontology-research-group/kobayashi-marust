#!/bin/bash
# Profile every ORE 2015 pool input under both routing policies (no
# classification). Produces one JSONL row per input and policy with the
# selected route and every matching general rule (contract G4 admission
# counts). Array index = chunk of 48 inputs.
#SBATCH --job-name=km154-profile
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=04:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --array=0-39
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026/slurm/profile-%A_%a.out
set -euo pipefail
ROOT=/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026
FILES=/ibex/scratch/hohndor/km/v143-harness-20260918/corpus/pool_sample/files
out="$ROOT/profiles/chunk-${SLURM_ARRAY_TASK_ID}.jsonl"
/usr/bin/mkdir -p "$ROOT/profiles"
: > "$out.tmp"
/usr/bin/ls "$FILES" | /usr/bin/sort | /usr/bin/awk -v c="$SLURM_ARRAY_TASK_ID" 'NR % 40 == c' |
while read -r f; do
  for policy in general v153; do
    row=$(KM_ROUTING_POLICY=$policy /usr/bin/timeout -k 5 900 "$ROOT/km" profile "$FILES/$f" 2>/dev/null || true)
    /usr/bin/python3 - "$f" "$policy" "$row" >> "$out.tmp" <<'PY'
import json, sys
name, policy, raw = sys.argv[1:4]
try:
    d = json.loads(raw)
    rec = {"ont": name, "policy": policy, "status": d.get("status"),
           "selected_route": d.get("selected_route"),
           "matched_rules": d.get("matched_rules"),
           "expressivity": (d.get("profile") or {}).get("expressivity", {}).get("code")}
except Exception as e:
    rec = {"ont": name, "policy": policy, "status": "failed", "error": str(e)[:200]}
print(json.dumps(rec))
PY
  done
done
/usr/bin/mv "$out.tmp" "$out"
