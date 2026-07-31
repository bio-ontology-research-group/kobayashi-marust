#!/bin/bash
# Source-bound automatic-route gate for the pre-clausification 9724 bridge rule.
#SBATCH --job-name=km-v12-9724-auto-bridge
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-9724-gate-20260731/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-9724-gate-20260731
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_9724.owl
expected_binary=a07dcffe7b509d7cb72794b55f763ec6e72bc1305614d8404fe38acebd4a5ce8
expected_source=b8febb611fd088867960b07fca70e75a1c59ac6922026657f02be682de274239

test "$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)" = "$expected_binary"
test "$(/usr/bin/sha256sum "$root/km-f6b2188-source.tar.gz" | /usr/bin/cut -d' ' -f1)" = "$expected_source"

work=${SLURM_TMPDIR:-/tmp}/km-v12-9724-auto-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work/run" "$root/results" "$root/failures"

# Assert the route used at the real pre-clausification production boundary.
# A post-normalization `km profile` result is insufficient for this gate.
set +e
/usr/bin/timeout 8s /usr/bin/env KM_ROUTE=auto KM_TIMING=1 \
  "$root/km" classify "$km_root/corpus/$ontology" \
  >"$work/route.stdout" 2>"$work/route.stderr"
trace_rc=$?
set -e
test "$trace_rc" -eq 124
/usr/bin/grep -F "route=ht_bridge" "$work/route.stderr"
/usr/bin/cp "$work/route.stderr" "$root/results/route-trace.stderr"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_auto_source_bridge_v12 \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --binary-sha "$expected_binary" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/failures" \
  --checkpoint "$root/results/$ontology.checkpoint.json" \
  --env "KM_ROUTE=auto" \
  >"$root/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/results/$ontology.json.tmp" "$expected_binary" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
expected = sys.argv[2]
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"automatic 9724 gate did not match: {row}")
if row.get("binary_sha256") != expected or not row.get("checkpointed"):
    raise SystemExit(f"automatic 9724 gate provenance failure: {row}")
if row.get("extra") != 0 or row.get("missing") != 0:
    raise SystemExit(f"automatic 9724 taxonomy difference: {row}")
PY
/usr/bin/mv "$root/results/$ontology.json.tmp" "$root/results/$ontology.json"
echo "GATE_COMPLETE ontology=$ontology route=ht_bridge"
