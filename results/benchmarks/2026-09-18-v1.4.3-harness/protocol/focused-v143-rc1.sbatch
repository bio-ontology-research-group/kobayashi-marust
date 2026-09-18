#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=03:00:00
#SBATCH --job-name=km-v143-data-reference
set -euo pipefail
root=/ibex/scratch/hohndor/km/v143-harness-20260918
test -f "$root/STAGE-COMPLETE"
cd "$root"
sha256sum -c harness-binary.sha256
chunk=$(printf '%03d' "$SLURM_ARRAY_TASK_ID")
out="$root/focused-v143-rc1/$chunk"
mkdir -p "$out"
export HARNESS_OUT_DIR="$out/output"
export KM140_BIN=/ibex/scratch/hohndor/km/v143-harness-20260918/km-candidate-v143-rc1
export TMPDIR="$out/tmp"
mkdir -p "$TMPDIR"
printf 'SLURM_JOB_ID=%s\nSLURM_ARRAY_JOB_ID=%s\nSLURM_ARRAY_TASK_ID=%s\nKM140_BIN=%s\n' "$SLURM_JOB_ID" "$SLURM_ARRAY_JOB_ID" "$SLURM_ARRAY_TASK_ID" "$KM140_BIN" > "$out/environment.txt"
lscpu > "$out/lscpu.txt"
"$root/target/release/owl-reasoner-harness" run \
 --corpus "$root/corpus/pool_sample/files" --only "$root/functional-chunks/$chunk.txt" \
 --reasoner "$root/source/wrappers/run-km-v140.sh" --args '{}' \
 --cap-secs 240 --threads 1 --mem-mb 20480 --out "$out/results.jsonl" \
 > "$out/driver.stdout" 2> "$out/driver.stderr"
touch "$out/COMPLETE"
