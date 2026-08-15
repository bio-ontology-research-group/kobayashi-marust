#!/bin/bash
#SBATCH --job-name=km-intersection-auto-pair
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
#SBATCH --output=/ibex/scratch/hohndor/km/intersection-el-route-20260815/pair-%A_%a.out

set -euo pipefail
ids=(10806 9590 13664 868)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/intersection-el-route-20260815
baseline=/ibex/scratch/hohndor/km/flat-inproc-elc-20260815/km
candidate=$root/km
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl
mkdir -p "$root/pair"
for arm in baseline candidate; do
    binary=$baseline
    [[ $arm == candidate ]] && binary=$candidate
    /usr/bin/time -f 'wall_s=%e peak_kb=%M' -o "$root/pair/${id}-${arm}.time" \
        env KM_TIMING=1 "$binary" classify "$ontology" > "$root/pair/${id}-${arm}.json"
    echo "RESULT ontology=$id arm=$arm $(cat "$root/pair/${id}-${arm}.time") sha=$(sha256sum "$root/pair/${id}-${arm}.json" | cut -d' ' -f1)"
done
cmp "$root/pair/${id}-baseline.json" "$root/pair/${id}-candidate.json"
echo "OUTPUT_IDENTICAL ontology=$id"
