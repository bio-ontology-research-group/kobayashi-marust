#!/bin/bash
# Paired seed differential: each task runs its share of the 400 seeds with
# KM_BIN_A then KM_BIN_B (order alternating per task), 60 s, one core.
#SBATCH --job-name=km155-nc-seeds
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --time=04:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v155-nominal-coverage-20261030/slurm/seeds-%A_%a.out
set -uo pipefail
ROOT=/ibex/scratch/projects/c2014/hohndor/km/v155-nominal-coverage-20261030; T=${SLURM_ARRAY_TASK_ID}
export TMPDIR=$ROOT/tmp/seeds_${SLURM_ARRAY_JOB_ID}_$T; mkdir -p "$TMPDIR" $ROOT/out/seeds-$KM_TAGRUN
files=($(ls $ROOT/seeds/*.ofn | awk -v t=$T -v n=$KM_TASKS 'NR%n==t'))
for v in $(env | grep -o '^KM_[A-Z_0-9]*' | grep -v -E '^KM_(BIN_A|BIN_B|TAGRUN|TASKS)$'); do unset $v; done
if (( T % 2 )); then order="A B"; else order="B A"; fi
for w in $order; do
  if [ $w = A ]; then bin=$KM_BIN_A; else bin=$KM_BIN_B; fi
  DIFF_THREADS=1 DIFF_KM_TIMEOUT=60 /usr/bin/python3 -I $ROOT/diff_run.py "$bin" /nonexistent $ROOT/gold $ROOT/out/seeds-$KM_TAGRUN/$w.$T.tsv auto "${files[@]}"
done
rm -rf "$TMPDIR"
