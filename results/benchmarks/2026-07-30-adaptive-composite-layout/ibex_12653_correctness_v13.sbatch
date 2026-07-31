#!/bin/bash
# Source-bound correctness-only gate for the exact numeric datatype bridge.
# Hardware-comparable timing comes from the separate Gold 6248 gate/full sweep.
#SBATCH --job-name=km-v13-12653-correct
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v13-numeric-gate-20260731/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v13-numeric-gate-20260731
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_12653.owl
expected_source=86b40a456258f161d673f6589826bce6ead9830dc360a2e65685578d141a2f95

test "$(/usr/bin/sha256sum "$root/km-dcc4fe7-source.tar.gz" | /usr/bin/cut -d' ' -f1)" = "$expected_source"
expected_binary=$(/usr/bin/cat "$root/km.sha256")
[[ $expected_binary =~ ^[0-9a-f]{64}$ ]]
test "$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)" = "$expected_binary"

work=${SLURM_TMPDIR:-/tmp}/km-v13-12653-correct-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work/run" "$root/correctness-results" "$root/correctness-failures"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_auto_numeric_bridge_v13_correctness \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --binary-sha "$expected_binary" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/correctness-failures" \
  --checkpoint "$root/correctness-results/$ontology.checkpoint.json" \
  --capture-km-route \
  --env "KM_ROUTE=auto" \
  >"$root/correctness-results/$ontology.json.tmp"

/usr/bin/python3 - "$root/correctness-results/$ontology.json.tmp" "$expected_binary" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
expected = sys.argv[2]
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"automatic 12653 correctness gate did not match: {row}")
if row.get("selected_route_trace") != "production_all":
    raise SystemExit(f"automatic 12653 selected the wrong route: {row}")
if row.get("binary_sha256") != expected or not row.get("checkpointed"):
    raise SystemExit(f"automatic 12653 correctness provenance failure: {row}")
if row.get("extra") != 0 or row.get("missing") != 0:
    raise SystemExit(f"automatic 12653 taxonomy difference: {row}")
PY
/usr/bin/mv \
  "$root/correctness-results/$ontology.json.tmp" \
  "$root/correctness-results/$ontology.json"
echo "CORRECTNESS_GATE_COMPLETE ontology=$ontology route=production_all"
