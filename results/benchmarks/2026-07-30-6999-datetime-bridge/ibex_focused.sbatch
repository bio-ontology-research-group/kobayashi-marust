#!/bin/bash
# Exact automatic-route gate for the dateTime bridge and adjacent controls.
#SBATCH --job-name=km-6999-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --array=0-4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/datetime-bridge-6999-20260730/focused/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/datetime-bridge-6999-20260730
km_root=/ibex/scratch/hohndor/km
ontologies=(
  ore_ont_6999.owl
  ore_ont_9635.owl
  ore_ont_10621.owl
  ore_ont_15672.owl
  ore_ont_9540.owl
)
expected_routes=(
  certified_nominals
  certified_nominals
  certified_nominals
  certified_nominals
  certified_card_nominals
)
index=${SLURM_ARRAY_TASK_ID:?}
ontology=${ontologies[$index]}
expected_route=${expected_routes[$index]}
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
if [[ $cpu_model != *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]; then
  echo "UNEXPECTED_CPU_MODEL model=[$cpu_model]" >&2
  exit 2
fi

work=${SLURM_TMPDIR:-/tmp}/km-6999-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/focused/results" "$root/focused/failures"
observed_route=$("$root/km" profile "$km_root/corpus/$ontology" |
  /usr/bin/python3 -c 'import json,sys; print(json.load(sys.stdin)["selected_route"])')
test "$observed_route" = "$expected_route"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_auto_datetime_bridge_6999 \
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
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"automatic route failed exactness gate: {row}")
PY
/usr/bin/mv "$root/focused/results/$ontology.json.tmp" \
  "$root/focused/results/$ontology.json"
echo "TASK_COMPLETE ontology=$ontology route=$observed_route"
