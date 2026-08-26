#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --time=00:02:00
#SBATCH --output=/ibex/scratch/hohndor/km/v12-flat-disjoint-syntax-20260826/slurm-%j.out

set -euo pipefail
corpus=/ibex/scratch/hohndor/km/corpus
for ont in 6212 4205; do
  input=$corpus/ore_ont_${ont}.owl
  [[ -s "$input" ]]
  echo "ONTOLOGY $ont"
  grep -m 30 -n 'ObjectComplementOf' "$input" || true
done
