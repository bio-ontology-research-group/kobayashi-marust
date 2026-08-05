#!/bin/bash
#SBATCH --job-name=km-15846-route-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:09:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-2a32741-el-bottom-20260805/15846-route-pair/slurm-%j.out

set -euo pipefail
candidate_root=/ibex/scratch/hohndor/km/candidate-2a32741-el-bottom-20260805
km_root=/ibex/scratch/hohndor/km
root=$candidate_root/15846-route-pair
binary=$candidate_root/km
binary_sha=d8fd398d79e044e1daada75dff9812960de72bf2dca94399bf4836a1c0bab7b6
ontology=ore_ont_15846.owl
runner=$candidate_root/full_panel_run_one.py

mkdir -p "$root/results" "$root/checkpoints" "$root/failures/auto" \
  "$root/failures/production_all"
[[ $(sha256sum "$binary" | cut -d" " -f1) == "$binary_sha" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
PYTHONPATH=$candidate_root /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, ore_canon, tree_watchdog'

run_arm() {
  local arm=$1
  local route=$2
  local expected_route=$3
  local output=$root/results/${arm}.json
  local checkpoint=$root/checkpoints/${arm}.json
  local work=${SLURM_TMPDIR:-/tmp}/km-15846-${SLURM_JOB_ID}-${arm}
  /usr/bin/python3 "$runner" \
    --kind km \
    --arm "km_2a32741_${arm}" \
    --ontology "$km_root/corpus/$ontology" \
    --binary "$binary" \
    --binary-sha "$binary_sha" \
    --workers 16 \
    --order-index -1 \
    --timeout 240 \
    --memcap-mb 20480 \
    --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
    --gold-kind konclude \
    --workdir "$work" \
    --failures-dir "$root/failures/$arm" \
    --checkpoint "$checkpoint" \
    --capture-km-route \
    --env "KM_ROUTE=$route" \
    > "$output.tmp"
  /usr/bin/python3 - "$output.tmp" "$binary_sha" "$expected_route" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != "ore_ont_15846.owl" or row.get("binary_sha256") != sys.argv[2]:
    raise SystemExit(f"identity mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"classification failed: {row}")
if row.get("selected_route_trace") != sys.argv[3]:
    raise SystemExit(f"unexpected route: {row}")
PY
  mv "$output.tmp" "$output"
}

# Run the shorter historic route first so it still yields evidence if the
# current automatic route consumes its full budget.
run_arm production_all production_all production_all
run_arm auto auto certified_nominals

/usr/bin/python3 - "$root/results/auto.json" "$root/results/production_all.json" <<'PY'
import json
import sys

auto = json.load(open(sys.argv[1]))
production = json.load(open(sys.argv[2]))
fields = (
    "status", "verdict", "solved", "consistent", "consistency_mismatch",
    "subsumptions", "unsatisfiable", "extra", "missing", "extra_unsat",
    "missing_unsat", "reported_incomplete", "signature_sha256",
    "fulliri_taxonomy_sha256",
)
differences = {
    field: (auto.get(field), production.get(field))
    for field in fields
    if auto.get(field) != production.get(field)
}
if differences:
    raise SystemExit(f"semantic difference: {differences}")
print(json.dumps({
    "auto": {"wall_s": auto["wall_s"], "peak_mb": auto["peak_mb"]},
    "production_all": {
        "wall_s": production["wall_s"], "peak_mb": production["peak_mb"]
    },
}, indent=2, sort_keys=True))
PY
