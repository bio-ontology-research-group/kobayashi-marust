#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=6G
#SBATCH --time=00:30:00
#SBATCH --job-name=km-incremental-report
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
sacct -X -j 51982318,51982375,51983825 --parsable2 --format=JobID,State,ExitCode > scheduler-terminal.psv
python3 render_incremental_comparison.py \
 --audit "v1.4.0=$DYNAMIC_ROOT/../incremental-driver-v3/main-audit.json" \
 --audit "v1.4.0=$DYNAMIC_ROOT/../incremental-pure-dl-supplement/main-audit.json" \
 --audit "v1.4.1=$DYNAMIC_ROOT/main-audit.json" \
 --slurm-receipts scheduler-terminal.psv --out comparison
