#!/bin/bash
#SBATCH --job-name=km-elc-typed-input-route-drop-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:10:00
#SBATCH --array=0-9
#SBATCH --output=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/elc-typed-route-drop-pair-%A_%a.out

set -euo pipefail
ids=(10890 4460 14587 11452 15917 6751 14574 13840 15341 9014)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl
baseline="$root/km-release-input"
candidate="$root/km-elc-typed-input-route-drop"

for repeat in 0 1 2 3 4; do
    if (( repeat % 2 == 0 )); then order=(baseline candidate); else order=(candidate baseline); fi
    for label in "${order[@]}"; do
        binary="$baseline"
        if [[ "$label" == candidate ]]; then binary="$candidate"; fi
        output="$root/${id}-${label}-${repeat}.elc-typed-route-drop.json"
        timing="$root/${id}-${label}-${repeat}.elc-typed-route-drop.time"
        /usr/bin/time -f 'wall_s=%e peak_kb=%M' -o "$timing" \
            "$binary" classify "$ontology" > "$output"
        echo "RESULT ontology=$id repeat=$repeat label=$label $(cat "$timing") sha=$(sha256sum "$output" | cut -d' ' -f1)"
    done
    cmp "$root/${id}-baseline-${repeat}.elc-typed-route-drop.json" \
        "$root/${id}-candidate-${repeat}.elc-typed-route-drop.json"
done
echo "OUTPUT_IDENTICAL ontology=$id repeats=5"
