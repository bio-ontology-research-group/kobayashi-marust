#!/bin/bash
#SBATCH --job-name=km-v110-release-final
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=140-189%1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.1.0-final-20260826/full-sweep/slurm-%A_%a.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.1.0-final-20260826
template=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/ibex_final_sweep.sbatch
expected=fd9d7f1a1f4365a3262aeb37be8095631489257ea1e030e400a647d382b6a88a
[[ $(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1) == "$expected" ]]
for required in ore592.txt full_panel_fingerprint.py full_panel_run_one.py \
  full_panel_run_one_collision_safe.py full_panel_run_one_fulliri_only.py \
  ore_canon.py tree_watchdog.py; do
  [[ -s "$root/full-sweep/$required" ]] || {
    echo "HARNESS_PREFLIGHT_MISSING $required" >&2
    exit 2
  }
done
[[ $(/usr/bin/wc -l < "$root/full-sweep/ore592.txt") -eq 592 ]]
PYTHONPATH="$root/full-sweep" /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, full_panel_run_one_collision_safe, full_panel_run_one_fulliri_only, ore_canon, tree_watchdog'
generated=${SLURM_TMPDIR:-/tmp}/km-v110-release-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|move-augment-right-sized-20260814|v1.1.0-final-20260826|g' \
  -e 's|/final-sweep|/full-sweep|g' \
  -e "s|275eb9af6d41a9fd5e15c0f2ec93de3b3be122272fc4402a9b859afd7618da70|$expected|g" \
  -e 's|km_route_auto_move_augment_adaptive_workers|km_v110_release|g' \
  "$template" > "$generated"
/bin/bash "$generated"
