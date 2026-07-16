#!/bin/bash
# Single-pass KM expressivity + source/clause statistics for every ORE input.
# These exact JSON records are the feature table used to train the router.
#SBATCH --job-name=km-profile-all
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=22G
#SBATCH --array=0-591%36
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/profile-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715
km_root=/ibex/scratch/hohndor/km
mapfile -t ontologies < "$root/onts.txt"
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
mkdir -p "$root/profiles" "$root/profile-times"
/usr/bin/timeout -k 5 1200 /usr/bin/time -v \
  -o "$root/profile-times/$ontology.time" \
  /usr/bin/env KM_KEEP_CHAIN_AXIOMS=1 \
  "$root/km-profiled" profile "$local_ontology" \
  > "$root/profiles/$ontology.json.tmp"
/usr/bin/mv "$root/profiles/$ontology.json.tmp" "$root/profiles/$ontology.json"
/usr/bin/rm -f "$local_ontology"
