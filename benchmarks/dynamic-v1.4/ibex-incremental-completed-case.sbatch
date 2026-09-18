#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:20:00
#SBATCH --job-name=km-mmo-n10-full-audit
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
sha256sum -c source.sha256
base=/ibex/scratch/hohndor/km/dynamic-benchmark-20260917
sha256sum -c "$base/incremental-driver-v3/inputs/mmo-n10/SHA256SUMS" > input-verified.log
python3 audit_incremental_completed_case.py --baseline "$base/incremental-driver-v3" \
 --candidate "$base/v141-incremental-final" --case mmo-n10 --out "$DYNAMIC_ROOT/audit"
