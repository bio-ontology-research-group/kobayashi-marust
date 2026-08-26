#!/bin/bash
#SBATCH --job-name=km-v110-candidate-v20
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodelist=gpu510-32,cn509-08-l,cn509-09-l,cn509-20-l,cn509-23-r,cn509-24-l,cn509-24-r,cn509-25-l,cn509-26-r,cn509-27-r,cn509-28-l,cn512-03-l,cn512-04-l,cn512-05-l,cn512-06-r,cn512-09-r,cn512-13-l,cn512-14-l,cn512-15-l,cn512-20-l,cn512-20-r,cn512-21-l,cn512-22-r,cn512-23-r,cn512-24-l,cn512-24-r,cn512-25-l,cn512-27-l,cn512-27-r
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-591%40
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v20-expanded-direct-20260826/full-sweep/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v20-expanded-direct-20260826
template=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/ibex_final_sweep.sbatch
expected=33b536962de62789387d98479d9d4f5d28edc142eb9e7260e9805eb7d79b2c97
[[ $(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1) == "$expected" ]]
generated=${SLURM_TMPDIR:-/tmp}/km-v110-candidate-v20-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|move-augment-right-sized-20260814|v20-expanded-direct-20260826|g' \
  -e 's|/final-sweep|/full-sweep|g' \
  -e "s|275eb9af6d41a9fd5e15c0f2ec93de3b3be122272fc4402a9b859afd7618da70|$expected|g" \
  -e 's|km_route_auto_move_augment_adaptive_workers|km_v110_candidate_v20|g' \
  "$template" > "$generated"
/bin/bash "$generated"
