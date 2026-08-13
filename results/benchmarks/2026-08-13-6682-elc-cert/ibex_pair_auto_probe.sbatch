#!/bin/bash
#SBATCH --job-name=km-6682-auto-probe
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
baseline_root=/ibex/scratch/hohndor/km/candidate-d725ad2-large-abox-20260805
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_6682.owl
candidate_sha=$(sha256sum "$root/km" | cut -d" " -f1)
baseline_sha=7e0e28e77a0c86d937f814198a0c85ad35ea086c91d5fefa70b5fd0c3dc775b7
[[ $(sha256sum "$baseline_root/km" | cut -d" " -f1) == "$baseline_sha" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
mkdir -p "$root/results" "$root/checkpoints" "$root/failures"
PYTHONPATH=$baseline_root /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, ore_canon, tree_watchdog'

run_arm() {
  local arm=$1 binary=$2 binary_sha=$3 route=$4
  local output=$root/results/${arm}.json
  local checkpoint=$root/checkpoints/${arm}.json
  local work=${SLURM_TMPDIR:-/tmp}/km-6682-${SLURM_JOB_ID}-${arm}
  /usr/bin/python3 "$baseline_root/full_panel_run_one.py" \
    --kind km --arm "$arm" \
    --ontology "$km_root/corpus/$ontology" \
    --binary "$binary" --binary-sha "$binary_sha" \
    --workers 16 --order-index 0 --timeout 240 --memcap-mb 20480 \
    --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
    --gold-kind konclude --workdir "$work" --failures-dir "$root/failures" \
    --checkpoint "$checkpoint" --capture-km-route \
    --env KM_ROUTE="$route" > "$output.tmp"
  /usr/bin/python3 - "$output.tmp" "$ontology" "$binary_sha" <<'PY'
import json, sys
row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or row.get("binary_sha256") != sys.argv[3]:
    raise SystemExit(f"identity mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"classification failed: {row}")
PY
  mv "$output.tmp" "$output"
}

run_arm baseline_production "$baseline_root/km" "$baseline_sha" production_all
run_arm candidate_auto "$root/km" "$candidate_sha" auto

/usr/bin/python3 - "$root/results/baseline_production.json" "$root/results/candidate_auto.json" <<'PY'
import json, sys
baseline = json.load(open(sys.argv[1]))
candidate = json.load(open(sys.argv[2]))
semantic_fields = (
    "status", "verdict", "solved", "consistent", "consistency_mismatch",
    "subsumptions", "unsatisfiable", "extra", "missing", "extra_unsat",
    "missing_unsat", "reported_incomplete", "signature_sha256",
    "fulliri_taxonomy_sha256",
)
differences = {
    field: (baseline.get(field), candidate.get(field))
    for field in semantic_fields if baseline.get(field) != candidate.get(field)
}
if differences:
    raise SystemExit(f"semantic difference: {differences}")
if candidate.get("selected_route_trace") != "certified_el_production":
    raise SystemExit(f"automatic probe did not select certified_el_production: {candidate}")
print(json.dumps({
    "baseline_production": {
        "wall_s": baseline["wall_s"], "peak_mb": baseline["peak_mb"],
        "route": baseline.get("selected_route_trace"),
    },
    "candidate_auto": {
        "wall_s": candidate["wall_s"], "peak_mb": candidate["peak_mb"],
        "route": candidate.get("selected_route_trace"),
    },
    "signature_sha256": candidate["signature_sha256"],
}, indent=2, sort_keys=True))
PY
echo PAIR_COMPLETE
