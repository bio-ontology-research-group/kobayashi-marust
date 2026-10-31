#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=01:00:00
#SBATCH --array=0-2
#SBATCH --export=NONE
#SBATCH --job-name=km155-smoke
#SBATCH --output=@ROOT@/slurm/%x-%A_%a.log
# Generated from tools/release/v155/ibex by stage.sh; protocol: one core,
# 240 s, 20 GiB, scoped watchdog (protocol/ modules = the v1.5.4 G8 run's).
set -euo pipefail
root=@ROOT@
export TMPDIR="$root/tmp/${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum --quiet -c files.sha256
# Smoke: task 0 = RC, task 1 = v1.5.3, task 2 = Konclude, on SMOKE_INPUTS
# (held-out and design-half inputs, taken from the full-pool manifest).
SMOKE_INPUTS=$(cat "$root/inputs/smoke-inputs.txt")
case "$SLURM_ARRAY_TASK_ID" in
  0) /usr/bin/python3.9 "$root/run_release.py" --root "$root" --label smoke-rc \
       --manifest "$root/inputs/full-candidate-inputs.json" --only "$SMOKE_INPUTS" \
       --artifact "$root/artifacts/rc.json" --task 0 --job "$SLURM_ARRAY_JOB_ID" ;;
  1) /usr/bin/python3.9 "$root/run_release.py" --root "$root" --label smoke-v153 \
       --manifest "$root/inputs/full-candidate-inputs.json" --only "$SMOKE_INPUTS" \
       --artifact "$root/artifacts/v153.json" --task 0 --job "$SLURM_ARRAY_JOB_ID" ;;
  2) /usr/bin/python3.9 "$root/run_konclude.py" --root "$root" --label smoke-konclude \
       --manifest "$root/inputs/full-candidate-inputs.json" --only "$SMOKE_INPUTS" \
       --artifact "$root/artifacts/konclude.json" --task 0 --job "$SLURM_ARRAY_JOB_ID" ;;
esac
