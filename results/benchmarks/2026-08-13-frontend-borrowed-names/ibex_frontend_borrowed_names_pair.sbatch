#!/bin/bash
#SBATCH --job-name=km-ofn-borrowed
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:30:00
#SBATCH --output=/ibex/scratch/hohndor/km/frontend-borrowed-names-20260813/pair-%A_%a.out
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
    clauses="$root/${id}-${label}.clauses.json"
    meta="$root/${id}-${label}.meta.json"
    timing="$root/${id}-${label}.time.txt"
    KM_OFN_TIMING=1 /usr/bin/time -v -o "$timing" \
        "$binary" ofn "$ontology" --meta "$meta" > "$clauses"
    sha256sum "$clauses" "$meta"
    grep -E 'Elapsed|Maximum resident|User time|System time' "$timing"
done

cmp "$root/${id}-baseline.clauses.json" "$root/${id}-candidate.clauses.json"
cmp "$root/${id}-baseline.meta.json" "$root/${id}-candidate.meta.json"
echo "BYTE_IDENTICAL ontology=$id"
