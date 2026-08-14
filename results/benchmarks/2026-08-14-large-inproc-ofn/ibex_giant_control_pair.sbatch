#!/bin/bash
#SBATCH --job-name=km-large-inproc-ofn-giant-controls
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:15:00
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814/giant-%A_%a.out

set -euo pipefail
ids=(8737 16744)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl
baseline=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/km-elc-typed-input-route-drop
candidate="$root/km"
for repeat in 0 1 2; do
    if (( repeat % 2 == 0 )); then order=(baseline candidate); else order=(candidate baseline); fi
    for label in "${order[@]}"; do
        binary="$baseline"
        env_args=()
        if [[ "$label" == candidate ]]; then
            binary="$candidate"
            env_args=(env KM_INPROC_OFN_MAX=1073741824)
        fi
        output="$root/giant-${id}-${label}-${repeat}.json"
        timing="$root/giant-${id}-${label}-${repeat}.time"
        /usr/bin/time -f 'wall_s=%e peak_kb=%M' -o "$timing" \
            "${env_args[@]}" "$binary" classify "$ontology" > "$output"
        echo "RESULT ontology=$id repeat=$repeat label=$label $(cat "$timing") sha=$(sha256sum "$output" | cut -d' ' -f1)"
    done
    cmp "$root/giant-${id}-baseline-${repeat}.json" "$root/giant-${id}-candidate-${repeat}.json"
done
echo "OUTPUT_IDENTICAL ontology=$id repeats=3"
