#!/bin/bash
# Complete 592-ontology acceptance sweep for the feature-selected auto route.
# One ontology per task prevents a timeout from hiding later ontologies.
#SBATCH --job-name=km-auto592
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-591%100
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/feature-router-full-20260730/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/feature-router-full-20260730
km_root=/ibex/scratch/hohndor/km
ontology_list=$km_root/routing_20260715/onts.txt
index=${SLURM_ARRAY_TASK_ID:?}
[[ $index =~ ^([0-9]|[1-9][0-9]|[1-5][0-9][0-9])$ ]]
(( index < 592 ))
[[ $(/usr/bin/wc -l < "$ontology_list") -eq 592 ]]
ontology=$(/usr/bin/sed -n "$((index + 1))p" "$ontology_list")
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]

work=${SLURM_TMPDIR:-/tmp}/km-auto592-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/results" "$root/profiles" "$root/failures"
/usr/bin/cp "$km_root/corpus/$ontology" "$work/$ontology"

"$root/km" profile "$work/$ontology" > "$root/profiles/$ontology.json.tmp"
/usr/bin/python3 - "$root/profiles/$ontology.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or row.get("status") != "ok":
    raise SystemExit(f"invalid profile row: {row}")
if not row.get("selected_route"):
    raise SystemExit(f"missing selected route: {row}")
PY
/usr/bin/mv "$root/profiles/$ontology.json.tmp" "$root/profiles/$ontology.json"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_auto_feature_router \
  --ontology "$work/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/failures" \
  --checkpoint "$root/results/$ontology.checkpoint.json" \
  --env KM_ROUTE=auto \
  > "$root/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/results/$ontology.json.tmp" "$ontology" "$index" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology mismatch: {row.get('ont')} != {sys.argv[2]}")
if row.get("slurm_array_task_id") != str(sys.argv[3]):
    raise SystemExit(
        f"task mismatch: {row.get('slurm_array_task_id')} != {sys.argv[3]}"
    )
if not row.get("checkpointed"):
    raise SystemExit(f"runner did not checkpoint terminal state: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
PY
/usr/bin/mv "$root/results/$ontology.json.tmp" "$root/results/$ontology.json"
echo "TASK_COMPLETE index=$index ontology=$ontology"
