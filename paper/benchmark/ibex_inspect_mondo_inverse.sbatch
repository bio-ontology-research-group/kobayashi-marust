#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --job-name=km-paper-mondo-inverse
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/mondo-inverse-%j.out

set -euo pipefail
ontology=/ibex/scratch/hohndor/km/paper-benchmark-20260830/obo-snapshot/merged/mondo.ofn
test -s "$ontology"
grep -n -B 1 -A 1 'ObjectInverseOf' "$ontology" | head -n 120
printf 'MONDO_INVERSE_INSPECTION_COMPLETE\n'
