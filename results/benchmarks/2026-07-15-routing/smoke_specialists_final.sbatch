#!/bin/bash
# Definitive procedure gate for every named HT specialist. Each typed route and
# the exact manual bundle used by the matrix must both reproduce gold on a
# witness that actually enters that specialist's structural gate. QO, SHOQ, and
# card are measured but deliberately excluded from policy learning; bridge is
# the only eligible complete-answer-or-defer specialist. Nonmatching inputs are
# covered by the Rust specialist-only unit test.
#SBATCH --job-name=km-specialist-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-3
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/specialist-final3-%A_%a.out

set -euo pipefail
km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-final3
kon=$km_root/Konclude-official

case ${SLURM_ARRAY_TASK_ID:-0} in
  0) ontology=ore_ont_7581.owl; route=ht_qo ;;
  1) ontology=ore_ont_10908.owl; route=ht_shoq ;;
  2) ontology=ore_ont_1603.owl; route=ht_card ;;
  3) ontology=ore_ont_541.owl; route=ht_bridge ;;
esac

local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
gold=$km_root/gold/konclude__$ontology.sig.gz
work=${SLURM_TMPDIR:-/tmp}/km-specialist-$SLURM_JOB_ID-$SLURM_ARRAY_TASK_ID
result_dir=$root/smoke-specialists-final3
failure_dir=$root/smoke-specialists-final3-failures
result=$result_dir/$ontology.jsonl
mkdir -p "$work" "$result_dir" "$failure_dir" "$root/slurm"
: > "$result"
km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
kon_sha=$(/usr/bin/sha256sum "$kon" | /usr/bin/cut -d' ' -f1)

run_km() {
  local arm=$1
  shift
  local argv=(
    /usr/bin/python3 "$runner" --kind km --arm "$arm"
    --ontology "$local_ontology" --binary "$km" --binary-sha "$km_sha"
    --gold "$gold" --workdir "$work" --failures-dir "$failure_dir"
    --timeout 240 --memcap-mb 20480
  )
  for setting in "$@"; do argv+=(--env "$setting"); done
  "${argv[@]}" >> "$result"
}

run_konclude() {
  local workers=$1
  /usr/bin/python3 "$runner" --kind konclude --arm "konclude_w$workers" \
    --ontology "$local_ontology" --binary "$kon" --binary-sha "$kon_sha" \
    --workers "$workers" --workdir "$work" --failures-dir "$failure_dir" \
    --timeout 240 --memcap-mb 20480 >> "$result"
}

run_manual() {
  local common=(KM_ROUTE=manual KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18
    KM_KEEP_CHAIN_AXIOMS=1 KM_NO_ELC=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0
    KM_HT_ONLY=certified KM_HT_MODE=race)
  case $route in
    ht_qo)
      run_km manual "${common[@]}" KM_NO_HT_SHOQ=1 KM_NO_HT_CARD=1 KM_HT_ONLY=qo
      ;;
    ht_shoq)
      run_km manual "${common[@]}" KM_NO_HT_QO_ROUTER=1 KM_NO_HT_CARD=1 \
        KM_HT_ONLY=shoq
      ;;
    ht_card)
      run_km manual "${common[@]}" KM_NO_HT_QO_ROUTER=1 KM_NO_HT_SHOQ=1 \
        KM_HT_ONLY=card
      ;;
    ht_bridge)
      run_km manual "${common[@]}" KM_NO_HT_QO_ROUTER=1 KM_NO_HT_SHOQ=1 \
        KM_NO_HT_CARD=1 KM_TRIGGER_ABSORB=1 KM_BRIDGE_PROBE_BUDGET_S=30 \
        KM_BRIDGE_RETRY_ROUNDS=0 KM_HT_SATURATION_BUDGET_S=180 KM_HT_ONLY=bridge
      ;;
  esac
}

run_konclude 1
run_km named KM_ROUTE=$route
run_manual
run_konclude 16

/usr/bin/rm -rf "$work" "$local_ontology"
test "$(/usr/bin/wc -l < "$result")" -eq 4
/usr/bin/python3 - "$result" "$route" <<'PY'
import json, sys
rows = {row["arm"]: row for row in map(json.loads, open(sys.argv[1]))}
assert set(rows) == {"konclude_w1", "named", "manual", "konclude_w16"}
assert all(rows[arm].get("status") == "ok" and rows[arm].get("verdict") == "reference"
           for arm in ("konclude_w1", "konclude_w16"))
contract = ("status", "verdict", "consistent", "missing", "extra",
            "missing_unsat", "extra_unsat", "subsumptions", "unsatisfiable")
assert tuple(rows["named"].get(key) for key in contract) == \
       tuple(rows["manual"].get(key) for key in contract)
if sys.argv[2] == "ht_bridge":
    assert rows["named"].get("status") == "ok" and rows["named"].get("verdict") == "match"
PY
/usr/bin/printf 'DONE ontology=%s route=%s rows=4 km_sha=%s host=%s\n' \
  "$ontology" "$route" "$km_sha" "$(hostname)"
