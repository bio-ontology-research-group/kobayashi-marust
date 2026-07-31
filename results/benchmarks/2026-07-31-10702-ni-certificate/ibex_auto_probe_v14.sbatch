#!/bin/bash
# Automatic-route gate for the IBEX-native v14 binary.
#SBATCH --job-name=km-v14-10702-auto
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v14-full-20260731/auto-10702-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v14-full-20260731
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_10702.owl
expected_binary=47514b377f31b76284dab43853c6a5a2ac90133472cec37bce567ff0dcd3ca0a
test "$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)" = "$expected_binary"
PYTHONPATH="$root" /usr/bin/python3 -c \
  'import full_panel_run_one, ore_canon, tree_watchdog'

work=${SLURM_TMPDIR:-/tmp}/km-v14-10702-auto-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work/run" "$root/focused" "$root/failures"
"$root/km" profile "$km_root/corpus/$ontology" > "$root/focused/$ontology.profile.tmp"
/usr/bin/python3 - "$root/focused/$ontology.profile.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or row.get("status") != "ok":
    raise SystemExit(f"invalid profile: {row}")
if row.get("selected_route") != "nominal_ni_tbox":
    raise SystemExit(f"wrong automatic route: {row}")
PY
/usr/bin/mv "$root/focused/$ontology.profile.tmp" "$root/focused/$ontology.profile.json"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_v14_10702_auto \
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
  --checkpoint "$root/focused/$ontology.checkpoint.json" \
  --capture-km-route \
  --env KM_ROUTE=auto \
  > "$root/focused/$ontology.json.tmp"

/usr/bin/python3 - "$root/focused/$ontology.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology mismatch: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"automatic route did not match gold: {row}")
if row.get("selected_route_trace") != "nominal_ni_tbox":
    raise SystemExit(f"wrong executed route: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing checkpoint: {row}")
PY
/usr/bin/mv "$root/focused/$ontology.json.tmp" "$root/focused/$ontology.json"
echo "AUTO_GATE_COMPLETE ontology=$ontology"
