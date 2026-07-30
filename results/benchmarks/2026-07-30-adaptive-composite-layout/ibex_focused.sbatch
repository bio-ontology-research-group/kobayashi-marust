#!/bin/bash
# Exact automatic-route gate for adaptive composite terms and controls.
#SBATCH --job-name=km-adaptive-comp-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-20260730/focused/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-20260730
km_root=/ibex/scratch/hohndor/km
ontologies=(
  ore_ont_1194.owl
  ore_ont_15846.owl
  ore_ont_6999.owl
  ore_ont_1034.owl
  ore_ont_2237.owl
)
expected_routes=(
  nominals
  certified_nominals
  certified_nominals
  production_all
  production_all
)
index=${SLURM_ARRAY_TASK_ID:?}
ontology=${ontologies[$index]}
expected_route=${expected_routes[$index]}
work=${SLURM_TMPDIR:-/tmp}/km-adaptive-comp-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/focused/results" "$root/focused/failures"
PYTHONPATH="$root" /usr/bin/python3 -c \
  'import ore_canon, tree_watchdog; print("HARNESS_IMPORTS_OK")'
observed_route=$("$root/km" profile "$km_root/corpus/$ontology" |
  /usr/bin/python3 -c 'import json,sys; print(json.load(sys.stdin)["selected_route"])')
test "$observed_route" = "$expected_route"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_auto_adaptive_composite_layout \
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
if row.get("status") != "ok" or not row.get("signature_sha256"):
    raise SystemExit(f"automatic route produced no complete classification: {row}")
if sys.argv[2] != "ore_ont_1194.owl" and row.get("verdict") != "match":
    raise SystemExit(f"automatic route failed exactness gate: {row}")
PY
/usr/bin/mv "$root/focused/results/$ontology.json.tmp" \
  "$root/focused/results/$ontology.json"
echo "TASK_COMPLETE ontology=$ontology route=$observed_route"
