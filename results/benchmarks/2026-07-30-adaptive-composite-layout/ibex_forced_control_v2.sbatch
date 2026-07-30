#!/bin/bash
# Known-route regression control for the 17-bit ORE 15846 layout.
#SBATCH --job-name=km-adaptive-comp-v2-15846
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v2-20260731/forced/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v2-20260731
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_15846.owl
work=${SLURM_TMPDIR:-/tmp}/km-adaptive-comp-v2-control-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/forced/results" "$root/forced/failures"
PYTHONPATH="$root" /usr/bin/python3 -c \
  'import ore_canon, tree_watchdog; print("HARNESS_IMPORTS_OK")'

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_production_all_adaptive_composite_layout_v2 \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/forced/failures" \
  --checkpoint "$root/forced/results/$ontology.checkpoint.json" \
  --env KM_ROUTE=production_all \
  > "$root/forced/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/forced/results/$ontology.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"known route failed exactness gate: {row}")
PY
/usr/bin/mv "$root/forced/results/$ontology.json.tmp" \
  "$root/forced/results/$ontology.json"
echo "TASK_COMPLETE ontology=$ontology route=production_all"
