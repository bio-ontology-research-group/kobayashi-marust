#!/bin/bash
#SBATCH --job-name=km161-q2
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --array=0-149%75
#SBATCH --cpus-per-task=2
#SBATCH --mem=64G
#SBATCH --time=06:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v161-q2-20261112/logs/q2-%A_%a.log
set -u
unset PYTHONPATH LD_LIBRARY_PATH
I=/ibex/scratch/projects/c2014/hohndor/km/v161-q2-20261112
/usr/bin/python3 -I $I/ibex_q2.py $I $SLURM_ARRAY_TASK_ID 150
echo "Q2-SHARD-DONE $SLURM_ARRAY_TASK_ID $(hostname)"
