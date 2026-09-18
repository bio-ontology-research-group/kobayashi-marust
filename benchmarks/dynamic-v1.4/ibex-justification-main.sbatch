#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=12:00:00
#SBATCH --job-name=km-justification-main
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
export TMPDIR="$DYNAMIC_ROOT/justification-main/tmp/$SLURM_ARRAY_JOB_ID-$SLURM_ARRAY_TASK_ID"
mkdir -p "$TMPDIR"
trap 'rmdir "$TMPDIR" 2>/dev/null || true' EXIT
id=$(printf '%04d' "$SLURM_ARRAY_TASK_ID")
python3 justification_run.py "justification-main/tasks/$id.json" "justification-main/results/$id"
lscpu > "justification-main/results/$id/lscpu.txt"
sha256sum JustificationBenchmark.java justification_run.py konclude_oracle.py konclude_incremental.py > "justification-main/results/$id/harness.sha256"
echo JUSTIFICATION_MAIN_TASK_COMPLETE
