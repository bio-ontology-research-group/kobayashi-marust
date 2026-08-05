#!/bin/bash
#SBATCH --job-name=km-2624799-edge-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-11%6
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-2624799-el-edges-20260805/panel/slurm-%A_%a.out

set -euo pipefail
candidate_root=/ibex/scratch/hohndor/km/candidate-2624799-el-edges-20260805
baseline_root=/ibex/scratch/hohndor/km/release-408dee4-auto-20260805
km_root=/ibex/scratch/hohndor/km
candidate_sha=8f4a8ca4617be1039614b85de9a2ebb2c11e49cc14e7f9d9a444c250f88a315a
baseline_sha=4812d656144b4b822523acf97d6500238391aff5912078868535604f1aef22b1
[[ $(sha256sum "$candidate_root/km" | cut -d' ' -f1) == "$candidate_sha" ]]
[[ $(sha256sum "$baseline_root/km" | cut -d' ' -f1) == "$baseline_sha" ]]

cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
ontologies=(
  ore_ont_1194.owl
  ore_ont_3215.owl
  ore_ont_6934.owl
  ore_ont_8737.owl
  ore_ont_16744.owl
  ore_ont_15059.owl
  ore_ont_8486.owl
  ore_ont_9674.owl
  ore_ont_10689.owl
  ore_ont_14459.owl
  ore_ont_14817.owl
  ore_ont_15846.owl
)
index=${SLURM_ARRAY_TASK_ID:?}
(( index >= 0 && index < ${#ontologies[@]} ))
ontology=${ontologies[$index]}
root=$candidate_root/panel
mkdir -p "$root/results" "$root/checkpoints" "$root/failures/baseline" "$root/failures/candidate"
runner=$baseline_root/full_panel_run_one.py
PYTHONPATH=$baseline_root /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, ore_canon, tree_watchdog'

run_arm() {
  local arm=$1
  local binary=$2
  local expected=$3
  local output=$root/results/${arm}__${ontology}.json
  local checkpoint=$root/checkpoints/${arm}__${ontology}.json
  local work=${SLURM_TMPDIR:-/tmp}/km-edge-panel-${SLURM_JOB_ID}-${arm}
  /usr/bin/python3 "$runner" \
    --kind km \
    --arm "$arm" \
    --ontology "$km_root/corpus/$ontology" \
    --binary "$binary" \
    --binary-sha "$expected" \
    --workers 16 \
    --order-index "$index" \
    --timeout 240 \
    --memcap-mb 20480 \
    --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
    --gold-kind konclude \
    --workdir "$work" \
    --failures-dir "$root/failures/$arm" \
    --checkpoint "$checkpoint" \
    --capture-km-route \
    --env KM_ROUTE=auto \
    > "$output.tmp"
  /usr/bin/python3 - "$output.tmp" "$ontology" "$expected" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology mismatch: {row}")
if row.get("binary_sha256") != sys.argv[3]:
    raise SystemExit(f"binary mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid status: {row}")
if not row.get("selected_route_trace"):
    raise SystemExit(f"missing route trace: {row}")
PY
  mv "$output.tmp" "$output"
}

# Alternate execution order to avoid assigning every warm-cache or thermal
# position to the same binary.
if (( index % 2 == 0 )); then
  run_arm baseline "$baseline_root/km" "$baseline_sha"
  run_arm candidate "$candidate_root/km" "$candidate_sha"
else
  run_arm candidate "$candidate_root/km" "$candidate_sha"
  run_arm baseline "$baseline_root/km" "$baseline_sha"
fi

/usr/bin/python3 - \
  "$root/results/baseline__${ontology}.json" \
  "$root/results/candidate__${ontology}.json" <<'PY'
import json
import sys

baseline = json.load(open(sys.argv[1]))
candidate = json.load(open(sys.argv[2]))
semantic_fields = (
    "status", "verdict", "solved", "consistent", "consistency_mismatch",
    "subsumptions", "unsatisfiable", "extra", "missing", "extra_unsat",
    "missing_unsat", "reported_incomplete", "signature_sha256",
)
differences = {
    field: (baseline.get(field), candidate.get(field))
    for field in semantic_fields
    if baseline.get(field) != candidate.get(field)
}
if differences:
    raise SystemExit(f"semantic regression: {differences}")
print(json.dumps({
    "ont": baseline["ont"],
    "baseline_wall_s": baseline.get("wall_s"),
    "candidate_wall_s": candidate.get("wall_s"),
    "baseline_peak_mb": baseline.get("peak_mb"),
    "candidate_peak_mb": candidate.get("peak_mb"),
    "status": candidate.get("status"),
    "verdict": candidate.get("verdict"),
    "route": candidate.get("selected_route_trace"),
}, sort_keys=True))
PY
echo "PAIR_COMPLETE index=$index ontology=$ontology"
