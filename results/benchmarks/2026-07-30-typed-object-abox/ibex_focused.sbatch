#!/bin/bash
# Exact automatic-route gate plus a fail-closed performance control.
# 5107 and 15672 failed in the preceding automatic sweep. 5184 verifies an
# already-solved member of the same source candidate family. 1481 is retained
# as a resource control: a bridge defer must not publish a partial answer.
#SBATCH --job-name=km-objabox-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --array=0-3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/typed-object-abox-20260730/focused/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/typed-object-abox-20260730
km_root=/ibex/scratch/hohndor/km
ontologies=(
  ore_ont_5107.owl
  ore_ont_15672.owl
  ore_ont_5184.owl
  ore_ont_1481.owl
)
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:?}]}
expected_routes=(
  certified_nominals
  certified_nominals
  certified_nominals
  ""
)
expected_route=${expected_routes[${SLURM_ARRAY_TASK_ID:?}]}
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
if [[ $cpu_model != *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]; then
  echo "UNEXPECTED_CPU_MODEL model=[$cpu_model]" >&2
  exit 2
fi

work=${SLURM_TMPDIR:-/tmp}/km-objabox-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/focused/results" "$root/focused/failures"
PYTHONPATH="$root" /usr/bin/python3 -c \
  'import ore_canon, tree_watchdog; print("HARNESS_IMPORTS_OK")'
observed_route=$("$root/km" profile "$km_root/corpus/$ontology" |
  /usr/bin/python3 -c 'import json,sys; print(json.load(sys.stdin)["selected_route"])')
if [[ -n $expected_route && $observed_route != "$expected_route" ]]; then
  echo "UNEXPECTED_ROUTE ontology=$ontology expected=$expected_route observed=$observed_route" >&2
  exit 3
fi

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_auto_typed_object_abox \
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
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
if sys.argv[2] != "ore_ont_1481.owl":
    if row.get("status") != "ok" or row.get("verdict") != "match":
        raise SystemExit(f"automatic route failed exactness gate: {row}")
PY
/usr/bin/mv "$root/focused/results/$ontology.json.tmp" \
  "$root/focused/results/$ontology.json"
echo "TASK_COMPLETE ontology=$ontology route=$observed_route"
