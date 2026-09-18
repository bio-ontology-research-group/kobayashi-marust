#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=02:00:00
#SBATCH --job-name=km-justification-controls
#SBATCH --array=0-5
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
id=$(printf '%02d' "$SLURM_ARRAY_TASK_ID")
mkdir -p "justification-controls/classes-$id"
javac -cp /ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes/classifier-hermit.jar -d "justification-controls/classes-$id" justification-controls/DynamicBenchmark.java justification-controls/JustificationBenchmark.java justification-controls/JustificationLibrary.java
python3 justification-controls/justification_run.py "justification-controls/$id.json" "justification-controls/results/$id"
echo JUSTIFICATION_CONTROL_COMPLETE
