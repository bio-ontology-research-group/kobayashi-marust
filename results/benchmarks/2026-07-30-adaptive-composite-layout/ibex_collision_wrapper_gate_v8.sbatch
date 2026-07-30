#!/bin/bash
# Validate the production collision-safe runner before the complete v8 sweep.
#SBATCH --job-name=km-v8-collision-wrapper
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v8-20260731/collision-wrapper/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v8-20260731
km_root=/ibex/scratch/hohndor/km
gate=$root/collision-wrapper
work=${SLURM_TMPDIR:-/tmp}/km-v8-collision-wrapper-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$gate/results" "$gate/failures" "$work"

PYTHONPATH="$root" /usr/bin/python3 "$root/full_panel_run_one_collision_safe.py" \
  --kind km \
  --arm km_route_auto_v8_collision_safe \
  --ontology "$km_root/corpus/ore_ont_3524.owl" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__ore_ont_3524.owl.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$gate/failures" \
  --checkpoint "$gate/results/runner.checkpoint.json" \
  --env KM_ROUTE=auto \
  > "$gate/results/runner.json.tmp"

/usr/bin/python3 - "$gate/results/runner.json.tmp" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
expected = "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a"
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"collision-safe runner failed: {row}")
if row.get("fulliri_taxonomy_sha256") != expected or not row.get("solved"):
    raise SystemExit(f"collision-safe fingerprint mismatch: {row}")
PY
/usr/bin/mv "$gate/results/runner.json.tmp" "$gate/results/runner.json"
echo "COLLISION_WRAPPER_GATE_COMPLETE ontology=ore_ont_3524.owl"
