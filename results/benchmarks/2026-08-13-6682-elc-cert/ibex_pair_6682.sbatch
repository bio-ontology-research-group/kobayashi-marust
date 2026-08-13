#!/bin/bash
#SBATCH --job-name=km-d725-6682-elc-cert
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-d725ad2-large-abox-20260805/6682-elc-cert/slurm-%j.out

set -euo pipefail
source_root=/ibex/scratch/hohndor/km/candidate-d725ad2-large-abox-20260805
root=$source_root/6682-elc-cert
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_6682.owl
expected_binary=7e0e28e77a0c86d937f814198a0c85ad35ea086c91d5fefa70b5fd0c3dc775b7
[[ $(sha256sum "$source_root/km" | cut -d" " -f1) == "$expected_binary" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
mkdir -p "$root/results" "$root/checkpoints" "$root/failures"
PYTHONPATH=$source_root /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, ore_canon, tree_watchdog'

run_arm() {
  local arm=$1
  local route=$2
  local output=$root/results/${arm}.json
  local checkpoint=$root/checkpoints/${arm}.json
  local work=${SLURM_TMPDIR:-/tmp}/km-6682-${SLURM_JOB_ID}-${arm}
  /usr/bin/python3 "$source_root/full_panel_run_one.py" \
    --kind km \
    --arm "$arm" \
    --ontology "$km_root/corpus/$ontology" \
    --binary "$source_root/km" \
    --binary-sha "$expected_binary" \
    --workers 16 \
    --order-index 0 \
    --timeout 240 \
    --memcap-mb 20480 \
    --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
    --gold-kind konclude \
    --workdir "$work" \
    --failures-dir "$root/failures" \
    --checkpoint "$checkpoint" \
    --capture-km-route \
    --env KM_ROUTE="$route" \
    > "$output.tmp"
  /usr/bin/python3 - "$output.tmp" "$ontology" "$expected_binary" "$route" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or row.get("binary_sha256") != sys.argv[3]:
    raise SystemExit(f"identity mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"classification failed: {row}")
if row.get("selected_route_trace") != sys.argv[4]:
    raise SystemExit(f"unexpected route: {row}")
PY
  mv "$output.tmp" "$output"
}

run_arm production_all production_all
run_arm elc_cert elc_cert

/usr/bin/python3 - "$root/results/production_all.json" "$root/results/elc_cert.json" <<'PY'
import json
import sys

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
    for field in semantic_fields
    if baseline.get(field) != candidate.get(field)
}
if differences:
    raise SystemExit(f"semantic difference: {differences}")
print(json.dumps({
    "production_all": {
        "wall_s": baseline["wall_s"], "peak_mb": baseline["peak_mb"],
        "signature_sha256": baseline["signature_sha256"],
    },
    "elc_cert": {
        "wall_s": candidate["wall_s"], "peak_mb": candidate["peak_mb"],
        "signature_sha256": candidate["signature_sha256"],
    },
}, indent=2, sort_keys=True))
PY
echo PAIR_COMPLETE
