#!/bin/bash
#SBATCH --job-name=km-auto-panel-validate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/auto-panel-20260728/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/auto-panel-20260728
binary=$root/build/bin/km-main
receipt=$root/build/build-receipt.json
routes=$root/build/routes.txt

test -x "$binary"
test -s "$receipt"
"$binary" routes >"$routes"
/usr/bin/awk -F '\t' '$1 == "auto" { found=1 } END { exit !found }' "$routes"
/usr/bin/awk -F '\t' '$1 == "auto-speed" { found=1 } END { exit !found }' "$routes"
/usr/bin/awk -F '\t' '$1 == "auto-memory" { found=1 } END { exit !found }' "$routes"
/usr/bin/python3 - "$binary" "$receipt" <<'PY'
import hashlib
import json
import pathlib
import sys

binary = pathlib.Path(sys.argv[1])
receipt = json.loads(pathlib.Path(sys.argv[2]).read_text())
assert receipt["source_revision"] == "847a872a13e0d617c950ff5121d44ac89632b174"
assert receipt["binary_sha256"] == hashlib.sha256(binary.read_bytes()).hexdigest()
PY
echo "VALIDATION_COMPLETE binary=$binary"
