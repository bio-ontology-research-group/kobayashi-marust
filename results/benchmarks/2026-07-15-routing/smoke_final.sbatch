#!/bin/bash
# Focused final-binary gate: both source-terminology bridge closures plus paired
# Konclude references. The full 24-arm array is submitted only after this passes.
#SBATCH --job-name=km-route-final-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/smoke-final-%A_%a.out

set -euo pipefail
km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-final3
kon=$km_root/Konclude-official
result_dir=$root/smoke-final3
failure_dir=$root/smoke-final3-failures
mkdir -p "$result_dir" "$failure_dir"

ontologies=(ore_ont_541.owl ore_ont_12653.owl)
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
work=${SLURM_TMPDIR:-/tmp}/km-routing-smoke-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
mkdir -p "$work"
result=$result_dir/$ontology.jsonl
: > "$result"
km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
kon_sha=$(/usr/bin/sha256sum "$kon" | /usr/bin/cut -d' ' -f1)
gold=$km_root/gold/konclude__$ontology.sig.gz

run_km() {
  local arm=$1
  shift
  local argv=(/usr/bin/python3 "$runner" --kind km --arm "$arm"
    --ontology "$local_ontology" --binary "$km" --binary-sha "$km_sha"
    --gold "$gold" --workdir "$work" --failures-dir "$failure_dir"
    --timeout 240 --memcap-mb 20480 --env KM_ROUTE=manual
    --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 --env KM_HT_MEM_GB=18
    --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_HT_ONLY=certified)
  for setting in "$@"; do argv+=(--env "$setting"); done
  "${argv[@]}" >> "$result"
}

run_konclude() {
  local workers=$1
  /usr/bin/python3 "$runner" --kind konclude --arm "konclude_w${workers}" \
    --ontology "$local_ontology" --binary "$kon" --binary-sha "$kon_sha" \
    --workers "$workers" --workdir "$work" --failures-dir "$failure_dir" \
    --timeout 240 --memcap-mb 20480 >> "$result"
}

run_konclude 1
run_km ht_bridge KM_NO_ELC=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 \
  KM_NO_HT_QO_ROUTER=1 KM_NO_HT_SHOQ=1 KM_NO_HT_CARD=1 \
  KM_TRIGGER_ABSORB=1 KM_BRIDGE_PROBE_BUDGET_S=30 \
  KM_BRIDGE_RETRY_ROUNDS=0 KM_HT_SATURATION_BUDGET_S=180 \
  KM_HT_ONLY=bridge KM_HT_MODE=race
run_km production_all KM_TRIGGER_ABSORB=1 KM_BRIDGE_PROBE_BUDGET_S=30 \
  KM_BRIDGE_RETRY_ROUNDS=0 KM_HT_SATURATION_BUDGET_S=180
run_konclude 16

/usr/bin/rm -rf "$work" "$local_ontology"
test "$(/usr/bin/wc -l < "$result")" -eq 4
/usr/bin/python3 - "$result" <<'PY'
import json, sys
rows = {row["arm"]: row for row in map(json.loads, open(sys.argv[1]))}
assert set(rows) == {"konclude_w1", "ht_bridge", "production_all", "konclude_w16"}
assert all(rows[arm].get("status") == "ok" and rows[arm].get("verdict") == "reference"
           for arm in ("konclude_w1", "konclude_w16"))
assert all(rows[arm].get("status") == "ok" and rows[arm].get("verdict") == "match"
           for arm in ("ht_bridge", "production_all"))
PY
/usr/bin/printf 'DONE ontology=%s rows=4 host=%s\n' "$ontology" "$(hostname)"
