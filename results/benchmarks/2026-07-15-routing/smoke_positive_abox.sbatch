#!/bin/bash
# Portable end-to-end gate for the two positive-ABox recoveries. The frozen
# benchmark runner applies the same 240 s and 20 GiB process-group limits as the
# matrix and compares the automatic route with retained Konclude gold.
#SBATCH --job-name=km-positive-abox-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/positive-abox-smoke-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
km=$root/km-profiled-positiveabox1
expected_sha=fce554cd885b2bd9f7bc37feabb5b929d204af5a23da332eab5f3206d60862d8
runner=$root/bench_one_matrix_frozen.py
case ${SLURM_ARRAY_TASK_ID:-0} in
  0) ontology=ore_ont_10697.owl ;;
  1) ontology=ore_ont_15725.owl ;;
  *) echo "bad array task" >&2; exit 2 ;;
esac

observed_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
[[ "$observed_sha" == "$expected_sha" ]] \
  || { echo "KM hash mismatch: $observed_sha" >&2; exit 2; }
work=${SLURM_TMPDIR:-/tmp}/km-positive-abox-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID:-0}
out_dir=$root/smoke-positiveabox1
/usr/bin/mkdir -p "$work" "$out_dir"
/usr/bin/cp "$km_root/corpus/$ontology" "$work/$ontology"

"$km" profile "$work/$ontology" > "$work/$ontology.profile.json"
/usr/bin/python3 - "$work/$ontology.profile.json" "$ontology" <<'PY'
import json
import sys

profile = json.load(open(sys.argv[1], encoding="utf-8"))
assert profile.get("ont") == sys.argv[2], profile
assert profile.get("status") == "ok", profile
body = profile.get("profile", {})
assert body.get("schema_version") == 2, body
assert body.get("positive_abox_tbox_separable") is True, body
PY

/usr/bin/python3 "$runner" \
  --kind km --arm auto --ontology "$work/$ontology" \
  --binary "$km" --binary-sha "$observed_sha" \
  --gold "$km_root/gold/konclude__$ontology.sig.gz" --gold-kind konclude \
  --workdir "$work/run" --failures-dir "$out_dir/failures" \
  --timeout 240 --memcap-mb 20480 \
  --env KM_ROUTE=auto --env KM_TIMING=1 > "$work/$ontology.result.json"

/usr/bin/python3 - "$work/$ontology.result.json" "$ontology" "$expected_sha" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1], encoding="utf-8"))
assert row.get("ont") == sys.argv[2], row
assert row.get("binary_sha256") == sys.argv[3], row
assert row.get("requested_route") == "auto", row
assert row.get("status") == "ok", row
assert row.get("verdict") == "match", row
assert row.get("solved") is True, row
assert row.get("extra") == row.get("missing") == 0, row
assert row.get("extra_unsat") == row.get("missing_unsat") == 0, row
assert row.get("consistency_mismatch") is False, row
PY

/usr/bin/mv "$work/$ontology.profile.json" "$out_dir/$ontology.profile.json"
/usr/bin/mv "$work/$ontology.result.json" "$out_dir/$ontology.result.json"
/usr/bin/printf 'DONE ontology=%s binary_sha=%s host=%s\n' \
  "$ontology" "$observed_sha" "$(hostname)"
