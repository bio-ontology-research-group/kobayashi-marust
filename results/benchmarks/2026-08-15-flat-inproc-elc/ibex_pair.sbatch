#!/bin/bash
#SBATCH --job-name=km-flat-inproc-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:12:00
#SBATCH --array=0-12
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/flat-inproc-elc-20260815/pair-%A_%a.out

set -euo pipefail
ids=(13141 9790 10280 1493 14027 16114 3480 9513 6433 964 7608 5487 7120)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/flat-inproc-elc-20260815
binary=$root/km
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl
mkdir -p "$root/pair"
for repeat in 0 1 2; do
    if (( repeat % 2 == 0 )); then
        order=(baseline candidate)
    else
        order=(candidate baseline)
    fi
    for arm in "${order[@]}"; do
        output="$root/pair/${id}-${repeat}-${arm}.json"
        timing="$root/pair/${id}-${repeat}-${arm}.time"
        env_args=(KM_TIMING=1)
        [[ $arm == baseline ]] && env_args+=(KM_NO_INPROC_ELC=1)
        /usr/bin/time -f 'wall_s=%e peak_kb=%M' -o "$timing" \
            env "${env_args[@]}" "$binary" classify "$ontology" > "$output"
        echo "RESULT ontology=$id repeat=$repeat arm=$arm $(cat "$timing") sha=$(sha256sum "$output" | cut -d' ' -f1)"
    done
    cmp "$root/pair/${id}-${repeat}-baseline.json" "$root/pair/${id}-${repeat}-candidate.json"
done
echo "OUTPUT_IDENTICAL ontology=$id repeats=3"
