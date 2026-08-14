#!/bin/bash
#SBATCH --job-name=km-large-inproc-ofn-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:20:00
#SBATCH --array=0-13
#SBATCH --output=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814/pair-%A_%a.out

set -euo pipefail
# Eight expensive exact-EL routes followed by six large non-EL controls.
ids=(13482 15280 10689 9674 1012 1559 10750 15059 3215 14817 6934 4669 868 15703)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl
baseline=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/km-elc-typed-input-route-drop
candidate="$root/km"
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == 6b4dbd165382f19ec666520cb226b46058b77a3bc83ccc9f7a779f8b2f0eb9e1 ]]

for repeat in 0 1 2; do
    if (( repeat % 2 == 0 )); then order=(baseline candidate); else order=(candidate baseline); fi
    for label in "${order[@]}"; do
        binary="$baseline"
        env_args=()
        if [[ "$label" == candidate ]]; then
            binary="$candidate"
            env_args=(env KM_INPROC_OFN_MAX=1073741824)
        fi
        output="$root/${id}-${label}-${repeat}.json"
        timing="$root/${id}-${label}-${repeat}.time"
        /usr/bin/time -f 'wall_s=%e peak_kb=%M' -o "$timing" \
            "${env_args[@]}" "$binary" classify "$ontology" > "$output"
        echo "RESULT ontology=$id repeat=$repeat label=$label $(cat "$timing") sha=$(sha256sum "$output" | cut -d' ' -f1)"
    done
    cmp "$root/${id}-baseline-${repeat}.json" "$root/${id}-candidate-${repeat}.json"
done
echo "OUTPUT_IDENTICAL ontology=$id repeats=3"
