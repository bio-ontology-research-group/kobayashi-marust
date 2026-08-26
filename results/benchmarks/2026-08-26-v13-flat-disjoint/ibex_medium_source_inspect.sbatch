#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:03:00
#SBATCH --output=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/medium-inspect-%j.out

set -euo pipefail
corpus=/ibex/scratch/hohndor/km/corpus
for ont in 16444 9663 9724; do
  input=$corpus/ore_ont_${ont}.owl
  [[ -s "$input" ]]
  echo "ONTOLOGY $ont"
  wc -c -l "$input"
  grep -m 20 -nE 'ObjectComplementOf|ObjectUnionOf|EquivalentClasses|DisjointClasses|Object(All|Min|Max|Exact)' "$input" || true
done
