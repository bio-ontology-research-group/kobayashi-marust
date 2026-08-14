#!/bin/bash
#SBATCH --job-name=km-inproc-ofn-4m-band
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:12:00
#SBATCH --array=0-56
#SBATCH --output=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814/inproc-4m-%A_%a.out

set -euo pipefail
ids=(11140 10123 8492 7439 13000 443 1501 13852 2128 8347 947 2497 14280 6198 4226 10806 15793 8864 1666 6230 5002 11502 14027 15098 15288 7251 6870 16114 9590 6453 5965 5974 3406 4662 9944 15260 7234 15491 6076 964 9792 935 16619 3480 8792 3797 7608 10951 2317 8579 2591 5487 9513 6433 15178 12802 12698)
if (( SLURM_ARRAY_TASK_ID >= ${#ids[@]} )); then
    echo "ERROR: array index $SLURM_ARRAY_TASK_ID exceeds ${#ids[@]} ontology IDs" >&2
    exit 2
fi
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl
binary="$root/km-combined"
for repeat in 0 1 2; do
    if (( repeat % 2 == 0 )); then order=(control candidate); else order=(candidate control); fi
    for label in "${order[@]}"; do
        threshold=2097152
        if [[ "$label" == candidate ]]; then threshold=4194304; fi
        output="$root/inproc-4m-${id}-${label}-${repeat}.json"
        timing="$root/inproc-4m-${id}-${label}-${repeat}.time"
        /usr/bin/time -f 'wall_s=%e peak_kb=%M' -o "$timing" \
            env KM_INPROC_OFN_MAX="$threshold" "$binary" classify "$ontology" > "$output"
        echo "RESULT ontology=$id repeat=$repeat label=$label $(cat "$timing") sha=$(sha256sum "$output" | cut -d' ' -f1)"
    done
    cmp "$root/inproc-4m-${id}-control-${repeat}.json" "$root/inproc-4m-${id}-candidate-${repeat}.json"
done
echo "OUTPUT_IDENTICAL ontology=$id repeats=3"
