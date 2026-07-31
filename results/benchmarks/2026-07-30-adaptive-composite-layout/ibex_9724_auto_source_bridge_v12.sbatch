#!/bin/bash
# Source-bound automatic-route gate for the pre-clausification 9724 bridge rule.
#SBATCH --job-name=km-v12-9724-auto-bridge
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodelist=cn512-06-r,cn512-07-l,cn512-02-r,cn512-11-r,cn512-03-r,cn512-08-r,cn512-14-r,cn512-05-l,cn512-03-l,cn512-16-l
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
expected_source=b8febb611fd088867960b07fca70e75a1c59ac6922026657f02be682de274239

cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
if [[ $cpu_model != *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]; then
  echo "UNEXPECTED_CPU_MODEL model=[$cpu_model]" >&2
  exit 2
fi
test "$(/usr/bin/sha256sum "$root/km-f6b2188-source.tar.gz" | /usr/bin/cut -d' ' -f1)" = "$expected_source"
expected_binary=$(/usr/bin/cat "$root/km.sha256")
[[ $expected_binary =~ ^[0-9a-f]{64}$ ]]
test "$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)" = "$expected_binary"

work=${SLURM_TMPDIR:-/tmp}/km-v12-9724-auto-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work/run" "$root/results" "$root/failures"

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
  --capture-km-route \
  --env "KM_ROUTE=auto" \
  >"$root/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/results/$ontology.json.tmp" "$expected_binary" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
expected = sys.argv[2]
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"automatic 9724 gate did not match: {row}")
if row.get("selected_route_trace") != "ht_bridge":
    raise SystemExit(f"automatic 9724 selected the wrong route: {row}")
if row.get("binary_sha256") != expected or not row.get("checkpointed"):
    raise SystemExit(f"automatic 9724 gate provenance failure: {row}")
if row.get("extra") != 0 or row.get("missing") != 0:
    raise SystemExit(f"automatic 9724 taxonomy difference: {row}")
PY
/usr/bin/mv "$root/results/$ontology.json.tmp" "$root/results/$ontology.json"
echo "GATE_COMPLETE ontology=$ontology route=ht_bridge"
