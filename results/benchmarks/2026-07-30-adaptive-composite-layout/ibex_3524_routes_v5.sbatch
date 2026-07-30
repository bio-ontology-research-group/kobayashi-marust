#!/bin/bash
# Current-v5 exact route comparison for the giant flat taxonomy 3524.
#SBATCH --job-name=km-v5-3524-routes
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodelist=cn512-06-r,cn512-07-l
#SBATCH --nodes=1
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v5-20260731/probes/3524/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v5-20260731
km_root=/ibex/scratch/hohndor/km
routes=(elc production_all)
route=${routes[${SLURM_ARRAY_TASK_ID:?}]}
probe=$root/probes/3524
work=${SLURM_TMPDIR:-/tmp}/km-v5-3524-$route-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$probe/results" "$probe/failures"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm "km_route_${route}_v5" \
  --ontology "$km_root/corpus/ore_ont_3524.owl" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__ore_ont_3524.owl.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$probe/failures/$route" \
  --checkpoint "$probe/results/$route.checkpoint.json" \
  --env "KM_ROUTE=$route" \
  > "$probe/results/$route.json.tmp"

/usr/bin/python3 - "$probe/results/$route.json.tmp" "$route" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != "ore_ont_3524.owl" or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row for {sys.argv[2]}: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status for {sys.argv[2]}: {row}")
PY
/usr/bin/mv "$probe/results/$route.json.tmp" "$probe/results/$route.json"
echo "TASK_COMPLETE route=$route"
