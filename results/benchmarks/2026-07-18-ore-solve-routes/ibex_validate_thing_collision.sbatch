#!/bin/bash
# Verify the told superclass relations that the 3524/15703 KM output omits.
#SBATCH --job-name=km-tail-thing
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=6G
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/thing-%A_%a.out

set -u

km_root=/ibex/scratch/hohndor/km
validation=$km_root/routing_20260715/tail-validation-20260718
case ${SLURM_ARRAY_TASK_ID:-0} in
  0) ontology_id=3524 ;;
  1) ontology_id=15703 ;;
  *) exit 2 ;;
esac

target='http://purl.obolibrary.org/obo/BFO_0000050_some_http://www.w3.org/2002/07/owl#Thing'
/usr/bin/python3 "$validation/validate_told_subclass_target.py" \
  --ontology "$km_root/corpus/ore_ont_${ontology_id}.owl" \
  --km-output "$validation/results/km_production_${ontology_id}/stdout.log" \
  --target "$target" \
  --output "$validation/results/km_production_${ontology_id}/told-target-validation.json"
rc=$?
/usr/bin/printf 'DONE ontology=%s expected_incomplete_rc=%s host=%s\n' \
  "$ontology_id" "$rc" "$(hostname)"
test "$rc" -eq 1
