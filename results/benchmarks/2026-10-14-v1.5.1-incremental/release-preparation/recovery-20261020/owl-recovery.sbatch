#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --no-requeue
#SBATCH --export=NONE
#SBATCH --time=14:00:00
#SBATCH --array=64,72-79%4
#SBATCH --job-name=km-4dd7-owl-retry
#SBATCH --output=/ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-4dd7995b-recovery-20261020/slurm-owl-%A_%a.log
set -euo pipefail
[[ ${SLURM_RESTART_COUNT:-0} == 0 ]] || exit 2
I=$SLURM_ARRAY_TASK_ID
exec /usr/bin/python3.9 /ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-4dd7995b-v1/owl_task.py --index "$I" --output /ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-4dd7995b-recovery-20261020/results-owlapi/task-$(printf %03d $I)
