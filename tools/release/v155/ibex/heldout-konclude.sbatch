#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=04:00:00
#SBATCH --array=0-18
#SBATCH --export=NONE
#SBATCH --job-name=km155-heldout-konclude
#SBATCH --output=@ROOT@/slurm/%x-%A_%a.log
# Generated from tools/release/v155/ibex by stage.sh; protocol: one core,
# 240 s, 20 GiB, scoped watchdog (protocol/ modules = the v1.5.4 G8 run's).
set -euo pipefail
root=@ROOT@
export TMPDIR="$root/tmp/${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum --quiet -c files.sha256
/usr/bin/python3.9 "$root/run_konclude.py" --root "$root" --label heldout-konclude \
  --manifest "$root/inputs/held-out-inputs.json" \
  --artifact "$root/artifacts/konclude.json" --task "$SLURM_ARRAY_TASK_ID" --job "$SLURM_ARRAY_JOB_ID"
