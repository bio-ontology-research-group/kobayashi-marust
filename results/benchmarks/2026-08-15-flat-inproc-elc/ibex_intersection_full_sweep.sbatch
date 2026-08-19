#!/bin/bash
#SBATCH --job-name=km-intersection-el-full
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-591%40
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/intersection-el-route-20260815/full-sweep/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/intersection-el-route-20260815
template=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/ibex_final_sweep.sbatch
expected=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $expected == 519a892f87f27da0396a8278ae8a81effc7e646f7e42f59d015370e9d26c39bb ]]
generated=${SLURM_TMPDIR:-/tmp}/km-intersection-el-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|move-augment-right-sized-20260814|intersection-el-route-20260815|g' \
  -e 's|/final-sweep|/full-sweep|g' \
  -e "s|275eb9af6d41a9fd5e15c0f2ec93de3b3be122272fc4402a9b859afd7618da70|$expected|g" \
  -e 's|km_route_auto_move_augment_adaptive_workers|km_route_auto_intersection_el|g' \
  "$template" > "$generated"
/bin/bash "$generated"
