#!/bin/bash
# Targeted gate for the tableau procedure that the first two matrix attempts
# failed to exercise. Both the typed route and the equivalent manual option
# bundle must close the current in-fragment witness 6246 exactly before another
# full matrix is submitted. 9635 is no longer a valid witness: the modern
# converter deliberately fences its inverse+number (SHIQ) interaction and the
# newer certified HT procedures close it instead.
#SBATCH --job-name=km-tab-route-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/tab-smoke-%j.out

set -euo pipefail
km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-final3
kon=$km_root/Konclude-official
ontology=ore_ont_6246.owl
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
gold=$km_root/gold/konclude__$ontology.sig.gz
work=${SLURM_TMPDIR:-/tmp}/km-tab-smoke-$SLURM_JOB_ID
result=$root/smoke-tab-race-final3.jsonl
failure_dir=$root/smoke-tab-race-failures
mkdir -p "$work" "$failure_dir" "$root/slurm"
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

run_konclude 1
run_km tab_race_named KM_ROUTE=tab_race
run_km tab_race_manual KM_ROUTE=manual KM_THREADS=16 KM_PAR_MEM_GB=18 \
  KM_HT_MEM_GB=18 KM_KEEP_CHAIN_AXIOMS=1 KM_TAB_RACE=1 KM_TAB_FEAT=1 \
  KM_NO_ELC_PORTFOLIO=1 KM_NO_HT_RACE=1
run_konclude 16

/usr/bin/rm -rf "$work" "$local_ontology"
/usr/bin/python3 - "$result" <<'PY'
import json, sys
rows = {row["arm"]: row for row in map(json.loads, open(sys.argv[1]))}
assert set(rows) == {"konclude_w1", "tab_race_named", "tab_race_manual", "konclude_w16"}
assert all(rows[arm].get("status") == "ok" and rows[arm].get("verdict") == "reference"
           for arm in ("konclude_w1", "konclude_w16"))
assert all(rows[arm].get("status") == "ok" and rows[arm].get("verdict") == "match"
           for arm in ("tab_race_named", "tab_race_manual"))
PY
/usr/bin/printf 'DONE rows=%s km_sha=%s host=%s\n' \
  "$(/usr/bin/wc -l < "$result")" "$km_sha" "$(hostname)"
