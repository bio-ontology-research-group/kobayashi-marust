#!/bin/bash
#SBATCH --job-name=km-6682-features
#SBATCH --partition=batch
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --time=00:10:00
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-d725ad2-large-abox-20260805/6682-elc-cert/features-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/candidate-d725ad2-large-abox-20260805/6682-elc-cert
binary=/ibex/scratch/hohndor/km/candidate-d725ad2-large-abox-20260805/km
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_6682.owl

mkdir -p "$root/results"
"$binary" features "$ontology" > "$root/results/features-6682.jsonl"
test "$(wc -l < "$root/results/features-6682.jsonl")" -eq 1
