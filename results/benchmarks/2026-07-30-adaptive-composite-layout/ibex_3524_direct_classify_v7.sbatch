#!/bin/bash
# Separate KM classification from the Python benchmark canonicalizer on 3524.
#SBATCH --job-name=km-v7-3524-direct
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731/diagnostic-3524-direct/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731
out=$root/diagnostic-3524-direct
work=${SLURM_TMPDIR:-/tmp}/km-v7-3524-direct-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$out" "$work"

KM_ROUTE=elc KM_NO_BOTTOM_PREPASS=1 KM_TIMING=1 \
  timeout 240 /usr/bin/time -v \
  "$root/km" classify \
  /ibex/scratch/hohndor/km/corpus/ore_ont_3524.owl \
  > "$work/classification.json" 2> "$out/timing.log"

/usr/bin/python3 - "$work/classification.json" > "$out/receipt.json.tmp" <<'PY'
import hashlib
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
digest = hashlib.sha256()
with path.open("rb") as handle:
    for chunk in iter(lambda: handle.read(1024 * 1024), b""):
        digest.update(chunk)
row = json.load(path.open())
print(json.dumps({
    "status": "ok",
    "bytes": path.stat().st_size,
    "sha256": digest.hexdigest(),
    "subjects": len(row.get("subsumptions", {})),
    "inconsistent": row.get("inconsistent"),
}, sort_keys=True))
PY
/usr/bin/mv "$out/receipt.json.tmp" "$out/receipt.json"
echo "DIRECT_CLASSIFY_COMPLETE"
