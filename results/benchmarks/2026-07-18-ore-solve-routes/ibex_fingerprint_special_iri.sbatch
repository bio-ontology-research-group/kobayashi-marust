#!/bin/bash
# Compare KM and Konclude with full IRIs and a shared source declaration universe.
#SBATCH --job-name=km-special-fp
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=6G
#SBATCH --array=0-3%4
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/special-fp-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
validation=$km_root/routing_20260715/tail-validation-20260718
task=${SLURM_ARRAY_TASK_ID:-0}
case "$task" in
  0) label=km_fulliri_audit_7581; ontology_id=7581; format=json ;;
  1) label=konclude_fulliri_audit_7581; ontology_id=7581; format=owlxml ;;
  2) label=km_fulliri_audit_13503; ontology_id=13503; format=json ;;
  3) label=konclude_fulliri_audit_13503; ontology_id=13503; format=owlxml ;;
  *) exit 2 ;;
esac

result=$validation/results/$label
input=$result/stdout.log
if [[ "$format" == owlxml ]]; then
  input=$result/taxonomy.owl
fi
/usr/bin/python3 "$validation/fingerprint_tail_fulliri.py" \
  --input "$input" --format "$format" \
  --source-ontology "$km_root/corpus/ore_ont_${ontology_id}.owl" \
  --output-prefix "$result/fulliri-source"
