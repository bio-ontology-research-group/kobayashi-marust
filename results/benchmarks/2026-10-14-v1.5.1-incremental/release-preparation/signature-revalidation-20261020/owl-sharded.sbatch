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
#SBATCH --time=03:30:00
#SBATCH --array=0-399%20
#SBATCH --job-name=km-11db-owl
#SBATCH --output=/ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-11db48ce-v1/slurm-%A_%a.log
set -euo pipefail
[[ ${SLURM_RESTART_COUNT:-0} == 0 ]] || exit 2
D=/ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-11db48ce-v1
R=/ibex/project/c2014/hohndor/km/v151-incremental-20261014/final-runtime-v2
I=$((SLURM_ARRAY_TASK_ID / 5))
REP=$((SLURM_ARRAY_TASK_ID % 5))
exec /usr/bin/python3.9 "$D/run_shard.py" --bindings "$D/four-arm-bindings.json" --protocol "$R/control/acceptance-protocol.json" --fixtures "$D/fixtures/task-$(printf %03d "$I").json" --output "$D/shards/task-$(printf %03d "$I")-rep-$REP" --repetition "$REP"
