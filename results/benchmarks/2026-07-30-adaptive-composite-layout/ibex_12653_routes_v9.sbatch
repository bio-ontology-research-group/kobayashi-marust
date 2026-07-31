#!/bin/bash
# Current-binary specialist search for the 12653 production timeout.
#SBATCH --job-name=km-v9-12653-routes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-3%4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v9-20260731/12653-routes/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v9-20260731
km_root=/ibex/scratch/hohndor/km
routes=(ht_full ht_features elc_cert cb_plain1)
route=${routes[${SLURM_ARRAY_TASK_ID:?}]}
ontology=ore_ont_12653.owl
probe=$root/12653-routes
work=${SLURM_TMPDIR:-/tmp}/km-v9-12653-$route-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$probe/results" "$probe/failures"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm "km_route_${route}_v9" \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$probe/failures/$route" \
  --checkpoint "$probe/results/$route.checkpoint.json" \
  --env "KM_ROUTE=$route" \
  > "$probe/results/$route.json.tmp"

/usr/bin/python3 - "$probe/results/$route.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
PY
/usr/bin/mv "$probe/results/$route.json.tmp" "$probe/results/$route.json"
