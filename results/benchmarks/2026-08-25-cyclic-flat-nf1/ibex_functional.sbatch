#!/bin/bash
#SBATCH --job-name=km-cyclic-flat-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=121,306,348,390,434,473,510,569%8
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-cyclic-flat-20260825/functional/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-cyclic-flat-20260825
template=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/ibex_final_sweep.sbatch
expected=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/functional"
for file in audit_strict.py full_panel_fingerprint.py \
  full_panel_run_one_collision_safe.py full_panel_run_one_fulliri_only.py \
  full_panel_run_one.py ore_canon.py tree_watchdog.py ore592.txt; do
  [[ -s "$root/functional/$file" ]]
done
generated=${SLURM_TMPDIR:-/tmp}/km-cyclic-flat-functional-${SLURM_JOB_ID}.sh
sed \
  -e 's|move-augment-right-sized-20260814|v110-cyclic-flat-20260825|g' \
  -e 's|/final-sweep|/functional|g' \
  -e "s|275eb9af6d41a9fd5e15c0f2ec93de3b3be122272fc4402a9b859afd7618da70|$expected|g" \
  -e 's|km_route_auto_move_augment_adaptive_workers|km_v110_cyclic_flat_functional|g' \
  -e '/^if \[\[ \$cpu_model != /,/^fi$/d' \
  "$template" > "$generated"
/bin/bash "$generated"
