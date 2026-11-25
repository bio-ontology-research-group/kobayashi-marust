#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=10:00:00
#SBATCH --array=0-18
#SBATCH --export=NONE
#SBATCH --job-name=oxidowl-heldout
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/oxidowl-bench-20261125/slurm/%x-%A_%a.log
# KM release protocol (one core, 240 s, 20 GiB, scoped watchdog, gold-6248 nodes),
# as tools/release/v155/ibex/heldout-konclude.sbatch; two measured oxidowl runs per input.
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/oxidowl-bench-20261125
export TMPDIR="$root/tmp/${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum --quiet -c files.sha256
/usr/bin/python3.9 "$root/run_oxidowl.py" --root "$root" --label heldout-oxidowl \
  --manifest "$root/inputs/held-out-inputs.json" \
  --artifact "$root/artifacts/oxidowl.json" --task "$SLURM_ARRAY_TASK_ID" --job "$SLURM_ARRAY_JOB_ID"
