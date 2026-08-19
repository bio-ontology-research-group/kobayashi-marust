#!/bin/bash
#SBATCH --job-name=km-light-el-route-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:12:00
#SBATCH --array=0-3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/flat-inproc-elc-20260815/light-el-%A_%a.out

set -euo pipefail
ids=(10806 9590 13664 868)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/flat-inproc-elc-20260815
binary=$root/km
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl
mkdir -p "$root/light-el"
for repeat in 0 1; do
    if (( repeat % 2 == 0 )); then
        order=(baseline candidate)
    else
        order=(candidate baseline)
    fi
    for arm in "${order[@]}"; do
        output="$root/light-el/${id}-${repeat}-${arm}.json"
        timing="$root/light-el/${id}-${repeat}-${arm}.time"
        route=auto
        [[ $arm == candidate ]] && route=elc
        /usr/bin/time -f 'wall_s=%e peak_kb=%M' -o "$timing" \
            env KM_TIMING=1 "$binary" classify --route "$route" "$ontology" > "$output"
        echo "RESULT ontology=$id repeat=$repeat arm=$arm route=$route $(cat "$timing") sha=$(sha256sum "$output" | cut -d' ' -f1)"
    done
    cmp "$root/light-el/${id}-${repeat}-baseline.json" "$root/light-el/${id}-${repeat}-candidate.json"
done
echo "OUTPUT_IDENTICAL ontology=$id repeats=2"
