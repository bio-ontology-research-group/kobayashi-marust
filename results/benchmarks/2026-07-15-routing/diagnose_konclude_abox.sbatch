#!/bin/bash
# Capture Konclude's verbose precomputation/classification trace for the three
# assertion-heavy inputs that defeat KM's monolithic nominal ground context.
# This is a diagnostic only; the frozen procedure matrix remains authoritative
# for time, memory, and taxonomy comparisons.
#SBATCH --job-name=kon-abox-trace
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-2
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/kon-abox-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
kon=$km_root/Konclude-official
out_dir=$root/konclude-abox-trace
work=${SLURM_TMPDIR:-/tmp}/kon-abox-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
ontologies=(ore_ont_10697.owl ore_ont_15725.owl ore_ont_15846.owl)
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}

/usr/bin/mkdir -p "$work" "$out_dir" "$root/slurm"
/usr/bin/cp "$km_root/corpus/$ontology" "$work/$ontology"
export LD_LIBRARY_PATH="$km_root:${LD_LIBRARY_PATH:-}"

/usr/bin/time -v -o "$out_dir/$ontology.time" \
  "$kon" classification -w 16 -v \
  -i "$work/$ontology" -o "$work/$ontology.taxonomy.owl" \
  > "$out_dir/$ontology.stdout" 2> "$out_dir/$ontology.stderr"

/usr/bin/sha256sum "$work/$ontology.taxonomy.owl" \
  > "$out_dir/$ontology.taxonomy.sha256"
/usr/bin/rm -rf "$work"
