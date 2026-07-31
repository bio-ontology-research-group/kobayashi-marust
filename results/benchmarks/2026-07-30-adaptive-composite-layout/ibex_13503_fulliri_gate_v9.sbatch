#!/bin/bash
# Verify the full-IRI-safe adjudication for the legal source #Nothing class.
#SBATCH --job-name=km-v9-13503-fulliri
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v9-20260731/13503-fulliri/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v9-20260731
km_root=/ibex/scratch/hohndor/km
gate=$root/13503-fulliri
work=${SLURM_TMPDIR:-/tmp}/km-v9-13503-fulliri-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$gate/failures" "$work"

PYTHONPATH="$root" /usr/bin/python3 "$root/full_panel_run_one_collision_safe.py" \
  --kind km \
  --arm km_route_auto_v9_fulliri_safe \
  --ontology "$km_root/corpus/ore_ont_13503.owl" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__ore_ont_13503.owl.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$gate/failures" \
  --checkpoint "$gate/result.checkpoint.json" \
  --env KM_ROUTE=auto \
  > "$gate/result.json.tmp"

/usr/bin/python3 - "$gate/result.json.tmp" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
expected = "1b8fdf730b9cdce8afed1c69c13e782c6c2dde70c42e5f1d2273dcbdb6b1282b"
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"full-IRI-safe runner failed: {row}")
if row.get("fulliri_taxonomy_sha256") != expected or not row.get("solved"):
    raise SystemExit(f"full-IRI fingerprint mismatch: {row}")
PY
/usr/bin/mv "$gate/result.json.tmp" "$gate/result.json"
