#!/bin/bash
#SBATCH --job-name=km-builtin-flat-full
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
#SBATCH --output=/ibex/scratch/hohndor/km/v110-builtin-flat-20260825/full-sweep/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-builtin-flat-20260825
template=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/ibex_final_sweep.sbatch
expected=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1) == "$expected" ]]
for file in audit_strict.py full_panel_fingerprint.py \
  full_panel_run_one_collision_safe.py full_panel_run_one_fulliri_only.py \
  full_panel_run_one.py ore_canon.py tree_watchdog.py ore592.txt; do
  [[ -s "$root/full-sweep/$file" ]]
done
generated=${SLURM_TMPDIR:-/tmp}/km-builtin-flat-full-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|move-augment-right-sized-20260814|v110-builtin-flat-20260825|g' \
  -e 's|/final-sweep|/full-sweep|g' \
  -e "s|275eb9af6d41a9fd5e15c0f2ec93de3b3be122272fc4402a9b859afd7618da70|$expected|g" \
  -e 's|km_route_auto_move_augment_adaptive_workers|km_v110_builtin_flat_full|g' \
  "$template" > "$generated"
/bin/bash "$generated"
