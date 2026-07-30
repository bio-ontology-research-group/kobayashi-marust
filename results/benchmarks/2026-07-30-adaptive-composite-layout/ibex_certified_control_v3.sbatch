#!/bin/bash
# Test the complete-or-defer nominal bridge portfolio on ORE 15846.
#SBATCH --job-name=km-adaptive-comp-v3-certnom
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v3-20260731/certified/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v3-20260731
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_15846.owl
work=${SLURM_TMPDIR:-/tmp}/km-adaptive-comp-v3-cert-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/certified/results" "$root/certified/failures"
PYTHONPATH="$root" /usr/bin/python3 -c \
  'import ore_canon, tree_watchdog; print("HARNESS_IMPORTS_OK")'

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_certified_nominals_adaptive_composite_layout_v3 \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/certified/failures" \
  --checkpoint "$root/certified/results/$ontology.checkpoint.json" \
  --env KM_ROUTE=certified_nominals \
  > "$root/certified/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/certified/results/$ontology.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"certified nominal route failed exactness gate: {row}")
PY
/usr/bin/mv "$root/certified/results/$ontology.json.tmp" \
  "$root/certified/results/$ontology.json"
echo "TASK_COMPLETE ontology=$ontology route=certified_nominals"
