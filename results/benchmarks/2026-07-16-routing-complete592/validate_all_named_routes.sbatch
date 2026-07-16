#!/bin/bash
# Validate all concrete KM routes for one ontology per array element.
# Each route invocation receives an independent 240 s / 20 GiB watchdog.
#SBATCH --job-name=km-all-route-proof
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=03:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-591%48
#SBATCH --output=/ibex/scratch/hohndor/km/route_proof_20260716/slurm/all-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
proof_root=${PROOF_ROOT:-$km_root/route_proof_20260716}
matrix_root=$km_root/routing_20260715
list=$matrix_root/onts.txt
runner=$matrix_root/bench_one_matrix-3b1d2a87.py
km=$proof_root/km
gold_dir=$km_root/gold
failure_dir=$proof_root/failures

routes=(
  auto
  default default8 default1
  production_all production_all8 production_all1
  cb_plain16 cb_plain8 cb_plain1
  cb_absorb16 cb_absorb8 cb_absorb1
  cb_trigger16 cb_trigger8 cb_trigger1
  cb_absorb_portfolio16
  elc elc_cert lean
  ht_general ht_qo ht_shoq ht_card ht_bridge ht_features ht_full ht_rules
  tableau tab_race card_fn nominals seq_on seq_off
)

mapfile -t ontologies < "$list"
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
source_ontology=$km_root/corpus/$ontology
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
work=${SLURM_TMPDIR:-/tmp}/km-all-route-proof-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}

/usr/bin/mkdir -p "$failure_dir" "$work"
/usr/bin/cp "$source_ontology" "$local_ontology"

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)

# Fail before producing any result row if the deployed binary cannot start on
# this compute node. This catches incompatible GLIBC or loader dependencies.
routes_stdout=$work/km-routes.stdout
routes_stderr=$work/km-routes.stderr
if ! "$km" routes >"$routes_stdout" 2>"$routes_stderr"; then
  /usr/bin/cat "$routes_stderr" >&2
  /usr/bin/printf 'FATAL binary preflight failed sha=%s host=%s\n' \
    "$km_sha" "$(hostname)" >&2
  exit 90
fi
if ! /usr/bin/grep -q '^production_all' "$routes_stdout"; then
  /usr/bin/printf 'FATAL unexpected route-list output: ' >&2
  /usr/bin/cat "$routes_stdout" >&2
  exit 91
fi

case "$ontology" in
  ore_ont_10860.owl|ore_ont_1194.owl|ore_ont_15703.owl|ore_ont_3524.owl|ore_ont_4669.owl)
    gold_args=(--gold-kind none)
    ;;
  *)
    gold_args=(--gold "$gold_dir/konclude__$ontology.sig.gz" --gold-kind konclude)
    ;;
esac

for route in "${routes[@]}"; do
  result_dir=$proof_root/results/$route
  result=$result_dir/$ontology.jsonl
  /usr/bin/mkdir -p "$result_dir"
  /usr/bin/python3 "$runner" \
    --kind km --arm "$route" --ontology "$local_ontology" \
    --binary "$km" --binary-sha "$km_sha" \
    "${gold_args[@]}" --workdir "$work" --failures-dir "$failure_dir/$route" \
    --order-index 0 --timeout 240 --memcap-mb 20480 \
    --env "KM_ROUTE=$route" > "$result"

  /usr/bin/python3 - "$result" "$ontology" "$route" "$km_sha" <<'PY'
import json
import sys

path, ontology, route, binary_sha = sys.argv[1:]
with open(path, encoding="utf-8") as handle:
    lines = [line for line in handle if line.strip()]
if len(lines) != 1:
    raise SystemExit(f"{path}: expected one non-empty JSON row, found {len(lines)}")
row = json.loads(lines[0])
expected = {
    "ont": ontology,
    "arm": route,
    "requested_route": route,
    "binary_sha256": binary_sha,
}
for key, value in expected.items():
    if row.get(key) != value:
        raise SystemExit(f"{path}: {key}={row.get(key)!r}, expected {value!r}")
if row.get("status") == "error":
    raise SystemExit(f"{path}: route execution error, rc={row.get('rc')}")
if row.get("status") == "ok" and not row.get("signature_sha256"):
    raise SystemExit(f"{path}: successful row has no canonical signature")
PY
done

/usr/bin/python3 - "$proof_root/results" "$ontology" "$km_sha" "${routes[@]}" <<'PY'
import json
import os
import sys

root, ontology, binary_sha, *routes = sys.argv[1:]
seen = set()
for route in routes:
    path = os.path.join(root, route, ontology + ".jsonl")
    with open(path, encoding="utf-8") as handle:
        row = json.load(handle)
    if row["arm"] in seen:
        raise SystemExit(f"{ontology}: duplicate route {row['arm']}")
    seen.add(row["arm"])
    if row["binary_sha256"] != binary_sha:
        raise SystemExit(f"{ontology}: binary hash drift in {route}")
if seen != set(routes):
    raise SystemExit(f"{ontology}: route set mismatch")
PY

/usr/bin/rm -rf "$work" "$local_ontology"
/usr/bin/printf 'DONE ontology=%s routes=%s\n' "$ontology" "${#routes[@]}"
