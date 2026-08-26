#!/bin/bash
#SBATCH --job-name=km-v110-candidate-v5
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
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825/full-sweep/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825
template=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/ibex_final_sweep.sbatch
expected=e9f06cda45e0e9256984167b650ec6664754b81a837628d3ff63bcd0a6d06620
[[ $(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1) == "$expected" ]]
generated=${SLURM_TMPDIR:-/tmp}/km-v110-candidate-v5-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|move-augment-right-sized-20260814|v1-cert-overhead-v5-20260825|g' \
  -e 's|/final-sweep|/full-sweep|g' \
  -e "s|275eb9af6d41a9fd5e15c0f2ec93de3b3be122272fc4402a9b859afd7618da70|$expected|g" \
  -e 's|km_route_auto_move_augment_adaptive_workers|km_v110_candidate_v5|g' \
  "$template" > "$generated"
/bin/bash "$generated"
