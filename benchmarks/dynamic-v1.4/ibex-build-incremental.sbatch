#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:05:00
#SBATCH --job-name=km-incremental-driver
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
mkdir -p classes
javac -cp /ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes/classifier-hermit.jar -d classes DynamicBenchmark.java
sha256sum DynamicBenchmark.java classes/org/kmbenchmark/DynamicBenchmark*.class > driver-build.sha256
printf 'job=%s\n' "$SLURM_JOB_ID" > driver-build.receipt
