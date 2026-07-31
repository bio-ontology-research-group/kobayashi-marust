#!/bin/bash
# Repeated guarded-HT memory stability panel for ORE 9724.
# Submit after the v10 array to avoid benchmark contention.
# Neither route sets KM_HT_FORCE.
#SBATCH --job-name=km-v11-9724-ht-repeat
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodelist=cn512-06-r,cn512-07-l,cn512-02-r,cn512-11-r,cn512-03-r,cn512-08-r,cn512-14-r,cn512-05-l,cn512-03-l,cn512-16-l
#SBATCH --nodes=1
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --array=0-9%10
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-20260731/9724-ht-repeat/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-20260731
km_root=/ibex/scratch/hohndor/km
probe=$root/9724-ht-repeat
index=${SLURM_ARRAY_TASK_ID:?}
routes=(
  ht_bridge ht_bridge ht_bridge ht_bridge ht_bridge
  ht_full ht_full ht_full ht_full ht_full
)
route=${routes[$index]}
ontology=ore_ont_9724.owl
work=${SLURM_TMPDIR:-/tmp}/km-v11-9724-$route-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$probe/results" "$probe/failures"

expected=cb492d92948460671c07cb08029d188b03f0c43809efe837c70918cd4b9f08c5
observed=$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)
test "$observed" = "$expected"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm "km_9724_repeat_${route}_$index" \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$probe/failures/$route/$index" \
  --checkpoint "$probe/results/$index-$route.checkpoint.json" \
  --env "KM_ROUTE=$route" \
  > "$probe/results/$index-$route.json.tmp"

/usr/bin/python3 - "$probe/results/$index-$route.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
PY
/usr/bin/mv "$probe/results/$index-$route.json.tmp" \
  "$probe/results/$index-$route.json"
echo "TASK_COMPLETE index=$index route=$route"
