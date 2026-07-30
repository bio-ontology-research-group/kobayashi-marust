#!/bin/bash
# Exact automatic-route retained-control gate; 3524 uses the full-IRI gate.
#SBATCH --job-name=km-adaptive-comp-v8-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v8-20260731/focused/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v8-20260731
km_root=/ibex/scratch/hohndor/km
ontologies=(
  ore_ont_1481.owl
  ore_ont_15672.owl
  ore_ont_15846.owl
  ore_ont_6999.owl
  ore_ont_1034.owl
)
index=${SLURM_ARRAY_TASK_ID:?}
ontology=${ontologies[$index]}
work=${SLURM_TMPDIR:-/tmp}/km-adaptive-comp-v8-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/focused/results" "$root/focused/failures"
PYTHONPATH="$root" /usr/bin/python3 -c \
  'import ore_canon, tree_watchdog; print("HARNESS_IMPORTS_OK")'
observed_route=$("$root/km" profile "$km_root/corpus/$ontology" |
  /usr/bin/python3 -c 'import json,sys; print(json.load(sys.stdin)["selected_route"])')
if [[ $ontology == ore_ont_1481.owl && $observed_route != production_all ]]; then
  echo "UNEXPECTED_ROUTE ontology=$ontology route=$observed_route" >&2
  exit 2
fi

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_auto_adaptive_composite_layout_v8 \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/focused/failures" \
  --checkpoint "$root/focused/results/$ontology.checkpoint.json" \
  --env KM_ROUTE=auto \
  > "$root/focused/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/focused/results/$ontology.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"automatic route failed exactness gate: {row}")
PY
/usr/bin/mv "$root/focused/results/$ontology.json.tmp" \
  "$root/focused/results/$ontology.json"
echo "TASK_COMPLETE ontology=$ontology route=$observed_route"
