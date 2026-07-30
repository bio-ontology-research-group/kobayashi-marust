#!/bin/bash
# Isolate the current frontend stage responsible for 3524's memory regression.
#SBATCH --job-name=km-v7-3524-ofn-stages
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=128G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731/diagnostic-3524-ofn/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731
out=$root/diagnostic-3524-ofn
work=${SLURM_TMPDIR:-/tmp}/km-v7-3524-ofn-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$out" "$work"
export KM_ROUTE=elc
export KM_NO_BOTTOM_PREPASS=1
export KM_OFN_TIMING=1

timeout 540 /usr/bin/time -v \
  "$root/km" ofn \
  /ibex/scratch/hohndor/km/corpus/ore_ont_3524.owl \
  --meta "$work/meta.json" \
  > "$work/clauses.json" \
  2> "$out/timing.log"
/usr/bin/python3 - "$work/meta.json" "$work/clauses.json" > "$out/receipt.json.tmp" <<'PY'
import hashlib
import json
import pathlib
import sys

meta = pathlib.Path(sys.argv[1])
clauses = pathlib.Path(sys.argv[2])
row = json.load(meta.open())
print(json.dumps({
    "status": "ok",
    "selected_route": row.get("route"),
    "meta_bytes": meta.stat().st_size,
    "clauses_bytes": clauses.stat().st_size,
    "clauses_sha256": hashlib.file_digest(clauses.open("rb"), "sha256").hexdigest(),
}, sort_keys=True))
PY
/usr/bin/mv "$out/receipt.json.tmp" "$out/receipt.json"
echo "FRONTEND_STAGE_DIAGNOSTIC_COMPLETE"
