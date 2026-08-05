#!/bin/bash
#SBATCH --job-name=km-3938b30-el-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-17%8
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-3938b30-source-el-20260805/panel/slurm-%A_%a.out

set -euo pipefail
candidate_root=/ibex/scratch/hohndor/km/candidate-3938b30-source-el-20260805
baseline_root=/ibex/scratch/hohndor/km/release-408dee4-auto-20260805
km_root=/ibex/scratch/hohndor/km
candidate_sha=7ac98a33a26579d9a2e3abaf95dfd8fba44e2dc842db1d12ce65144dd1a5c0f1
baseline_sha=4812d656144b4b822523acf97d6500238391aff5912078868535604f1aef22b1
[[ $(sha256sum "$candidate_root/km" | cut -d' ' -f1) == "$candidate_sha" ]]
[[ $(sha256sum "$baseline_root/km" | cut -d' ' -f1) == "$baseline_sha" ]]

cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
ontologies=(
  ore_ont_15059.owl
  ore_ont_11395.owl
  ore_ont_14042.owl
  ore_ont_3836.owl
  ore_ont_9498.owl
  ore_ont_9794.owl
  ore_ont_10445.owl
  ore_ont_4802.owl
  ore_ont_11389.owl
  ore_ont_2243.owl
  ore_ont_10248.owl
  ore_ont_14607.owl
  ore_ont_15929.owl
  ore_ont_11293.owl
  ore_ont_5927.owl
  ore_ont_6198.owl
  ore_ont_8864.owl
  ore_ont_15178.owl
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
  local expected_route=$4
  local output=$root/results/${arm}__${ontology}.json
  local checkpoint=$root/checkpoints/${arm}__${ontology}.json
  local work=${SLURM_TMPDIR:-/tmp}/km-source-el-${SLURM_JOB_ID}-${arm}
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
  /usr/bin/python3 - "$output.tmp" "$ontology" "$expected" "$expected_route" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology mismatch: {row}")
if row.get("binary_sha256") != sys.argv[3]:
    raise SystemExit(f"binary mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"classification failed: {row}")
if row.get("selected_route_trace") != sys.argv[4]:
    raise SystemExit(f"unexpected route: {row}")
PY
  mv "$output.tmp" "$output"
}

if (( index % 2 == 0 )); then
  run_arm baseline "$baseline_root/km" "$baseline_sha" production_all
  run_arm candidate "$candidate_root/km" "$candidate_sha" elc
else
  run_arm candidate "$candidate_root/km" "$candidate_sha" elc
  run_arm baseline "$baseline_root/km" "$baseline_sha" production_all
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
    "baseline_wall_s": baseline["wall_s"],
    "candidate_wall_s": candidate["wall_s"],
    "baseline_peak_mb": baseline["peak_mb"],
    "candidate_peak_mb": candidate["peak_mb"],
}, sort_keys=True))
PY
echo "PAIR_COMPLETE index=$index ontology=$ontology"
