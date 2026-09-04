#!/bin/bash
#SBATCH --job-name=km-v14-nosaturation-1194
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodelist=cn512-15-r
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=28G
#SBATCH --array=33
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4.0-nosaturation-candidate-20260901/full-sweep/slurm-%A_%a.out

set -euo pipefail
export MALLOC_ARENA_MAX=1
export KM_HT_NO_SATURATION=1
root=/ibex/scratch/hohndor/km/v1.4.0-nosaturation-candidate-20260901
template=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/ibex_final_sweep.sbatch
expected=${KM_CANDIDATE_SHA:?submit with KM_CANDIDATE_SHA}
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]]
for required in ore592.txt full_panel_fingerprint.py full_panel_run_one.py \
  full_panel_run_one_collision_safe.py full_panel_run_one_fulliri_only.py \
  ore_canon.py tree_watchdog.py; do
  [[ -s "$root/full-sweep/$required" ]]
done
[[ $(wc -l < "$root/full-sweep/ore592.txt") -eq 592 ]]
PYTHONPATH="$root/full-sweep" python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, full_panel_run_one_collision_safe, full_panel_run_one_fulliri_only, ore_canon, tree_watchdog'
mkdir -p "$root/.work"
generated=$root/.work/km-v140-trim-${SLURM_JOB_ID}.sh
trap 'unlink "$generated" 2>/dev/null || true' EXIT
sed \
  -e 's|move-augment-right-sized-20260814|v1.4.0-nosaturation-candidate-20260901|g' \
  -e 's|/final-sweep|/full-sweep|g' \
  -e "s|275eb9af6d41a9fd5e15c0f2ec93de3b3be122272fc4402a9b859afd7618da70|$expected|g" \
  -e 's|km_route_auto_move_augment_adaptive_workers|km_v140_nosaturation_candidate|g' \
  "$template" > "$generated"
bash "$generated"
