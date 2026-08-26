#!/bin/bash
#SBATCH --job-name=km-v110-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-591%40
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-stream-flat-20260825/functional-sweep/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-stream-flat-20260825
template=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/ibex_final_sweep.sbatch
expected=ae629a04cbe37cf3a75e39946125d9a09d66876d07ef1bfceb7cef8a734c35a6
[[ $(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/functional-sweep"
generated=${SLURM_TMPDIR:-/tmp}/km-v110-functional-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|move-augment-right-sized-20260814|v110-stream-flat-20260825|g' \
  -e 's|/final-sweep|/functional-sweep|g' \
  -e "s|275eb9af6d41a9fd5e15c0f2ec93de3b3be122272fc4402a9b859afd7618da70|$expected|g" \
  -e 's|km_route_auto_move_augment_adaptive_workers|km_v110_combined_functional|g' \
  -e '/^if \[\[ \$cpu_model != /,/^fi$/d' \
  "$template" > "$generated"
/bin/bash "$generated"
