#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=6G
#SBATCH --time=00:30:00
#SBATCH --job-name=km-incremental-report-v2
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
sha256sum -c source.sha256
base=/ibex/scratch/hohndor/km/dynamic-benchmark-20260917
args=(--audit "v1.4.0=$base/incremental-driver-v3/main-audit.json"
      --audit "v1.4.0=$base/incremental-pure-dl-supplement/main-audit.json"
      --audit "v1.4.1=$base/v141-incremental-final/main-audit.json")
sacct -X -j 51982318,51982375,51983825 --parsable2 --format=JobID,State,ExitCode > scheduler-terminal.psv
python3 enrich_incremental_failures.py "${args[@]}" --out failure-causes.json
python3 render_incremental_comparison.py "${args[@]}" --failure-causes failure-causes.json \
 --slurm-receipts scheduler-terminal.psv --out comparison
