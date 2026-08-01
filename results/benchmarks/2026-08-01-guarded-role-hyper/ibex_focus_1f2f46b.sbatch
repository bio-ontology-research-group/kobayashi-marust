#!/bin/bash
#SBATCH --job-name=km-1f2f46b-focus
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --array=0-4%2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/guarded-role-1f2f46b/focus-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715/guarded-role-1f2f46b
km_root=/ibex/scratch/hohndor/km
runner=/ibex/scratch/hohndor/km/routing_20260715/rule-clash-4703045/full_panel_run_one.py
onts=(
  ore_ont_9944.owl
  ore_ont_9944.owl
  ore_ont_12141.owl
  ore_ont_1194.owl
  ore_ont_4669.owl
)
routes=(cb_plain16 cb_plain1 cb_plain16 auto auto)
ont=${onts[${SLURM_ARRAY_TASK_ID:?}]}
route=${routes[$SLURM_ARRAY_TASK_ID]}
label=${ont%.owl}-$route
work=${SLURM_TMPDIR:-/tmp}/km-1f2f46b-${SLURM_JOB_ID}
mkdir -p "$work" "$root/focus-results" "$root/focus-failures"

PYTHONPATH=/ibex/scratch/hohndor/km/routing_20260715/rule-clash-4703045 \
/usr/bin/python3 "$runner" \
  --kind km \
  --arm "guarded_role_1f2f46b_$route" \
  --ontology "$km_root/corpus/$ont" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/focus-failures" \
  --checkpoint "$root/focus-results/$label.checkpoint.json" \
  --capture-km-route \
  --env "KM_ROUTE=$route" \
  > "$root/focus-results/$label.json.tmp"

/usr/bin/python3 - "$root/focus-results/$label.json.tmp" "$ont" "$route" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid status: {row}")
if sys.argv[2] in {"ore_ont_9944.owl", "ore_ont_12141.owl"} and (
    row.get("status") != "ok" or row.get("verdict") != "match"
):
    raise SystemExit(f"exactness control failed: {row}")
print(json.dumps(row, sort_keys=True))
PY
mv "$root/focus-results/$label.json.tmp" "$root/focus-results/$label.json"
