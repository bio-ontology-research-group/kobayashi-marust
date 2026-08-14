#!/bin/bash
#SBATCH --job-name=km-inproc-el-no-json-median
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:10:00
#SBATCH --array=0-20
#SBATCH --output=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814/combined-median-%A_%a.out

set -euo pipefail
ids=(13852 10806 3480 2128 5184 3231 947 12653 2497 6433 9792 14280 13383 9557 9590 13113 12802 964 14153 8347 15672)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl
baseline=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/km-elc-typed-input-route-drop
candidate="$root/km-combined"
for repeat in 0 1 2 3 4; do
    if (( repeat % 2 == 0 )); then order=(baseline candidate); else order=(candidate baseline); fi
    for label in "${order[@]}"; do
        binary="$baseline"
        if [[ "$label" == candidate ]]; then binary="$candidate"; fi
        output="$root/combined-median-${id}-${label}-${repeat}.json"
        timing="$root/combined-median-${id}-${label}-${repeat}.time"
        /usr/bin/time -f 'wall_s=%e peak_kb=%M' -o "$timing" \
            "$binary" classify "$ontology" > "$output"
        echo "RESULT ontology=$id repeat=$repeat label=$label $(cat "$timing") sha=$(sha256sum "$output" | cut -d' ' -f1)"
    done
    cmp "$root/combined-median-${id}-baseline-${repeat}.json" "$root/combined-median-${id}-candidate-${repeat}.json"
done
echo "OUTPUT_IDENTICAL ontology=$id repeats=5"
