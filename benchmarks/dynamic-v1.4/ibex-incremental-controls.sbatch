#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=00:30:00
#SBATCH --array=0-29%4
#SBATCH --job-name=km-incremental-controls
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
cases=(additions deletions rbox abox equality disjunction)
reasoners=(km hermit jfact openllet konclude)
case=${cases[$((SLURM_ARRAY_TASK_ID / 5))]}
reasoner=${reasoners[$((SLURM_ARRAY_TASK_ID % 5))]}
python3 run_incremental.py "$DYNAMIC_ROOT" "$case" "$reasoner" --pilot
