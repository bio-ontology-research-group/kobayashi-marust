#!/bin/bash
#SBATCH --job-name=km-classify-borrowed
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:30:00
#SBATCH --output=/ibex/scratch/hohndor/km/frontend-borrowed-names-20260813/classify-%A_%a.out
#SBATCH --array=0-4

set -euo pipefail

ids=(13482 15280 10750 1012 9674)
id="${ids[$SLURM_ARRAY_TASK_ID]}"
root=/ibex/scratch/hohndor/km/frontend-borrowed-names-20260813
ontology="/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl"
baseline=/ibex/scratch/hohndor/km/v0215-next-profile/km-candidate-ibex
candidate="$root/km-final"

for label in baseline candidate; do
    binary="$baseline"
    if [[ "$label" == candidate ]]; then
        binary="$candidate"
    fi
    output="$root/${id}-${label}.classify.txt"
    timing="$root/${id}-${label}.classify.time.txt"
    /usr/bin/time -v -o "$timing" timeout 240s \
        "$binary" classify "$ontology" > "$output"
    sha256sum "$output"
    grep -E 'Elapsed|Maximum resident|User time|System time' "$timing"
done

cmp "$root/${id}-baseline.classify.txt" "$root/${id}-candidate.classify.txt"
echo "CLASSIFY_IDENTICAL ontology=$id"
