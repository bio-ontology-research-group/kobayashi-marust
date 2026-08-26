#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:05:00
#SBATCH --array=0-2
#SBATCH --output=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/conflicts-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826
onts=(16444 6212 4205)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
/usr/bin/python3 "$root/inspect_flat_conflicts.py" \
  "/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl"
