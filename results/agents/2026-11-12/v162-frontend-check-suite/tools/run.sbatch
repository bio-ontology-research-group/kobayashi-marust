#!/bin/bash
#SBATCH --job-name=km162-fc
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --array=0-149%75
#SBATCH --cpus-per-task=2
#SBATCH --mem=64G
#SBATCH --time=08:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v162-fc-20261112/logs/fc-%A_%a.log
# v1.6.2 KM_FRONTEND_CHECK suite: one shard of the 1,781 checkers-on inputs.
set -u
unset PYTHONPATH LD_LIBRARY_PATH
I=/ibex/scratch/projects/c2014/hohndor/km/v162-fc-20261112
N=$(printf %03d $SLURM_ARRAY_TASK_ID)
mkdir -p $I/out $I/scratch/$N
/usr/bin/python3 -I $I/run_frontend_check_suite.py run --km $I/bin/km --checker $I/bin/km-owl-reference \
  --inputs $I/shards/in-$N.tsv --out-tsv $I/out/fc-$N.tsv --scratch-dir $I/scratch/$N \
  --jobs 1 --timeout 660 --budget 300 --nice 0
echo "FC-SHARD-DONE $SLURM_ARRAY_TASK_ID $(hostname)"
