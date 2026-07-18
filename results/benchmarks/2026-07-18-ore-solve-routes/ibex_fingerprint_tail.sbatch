#!/bin/bash
# Exact full-IRI taxonomy fingerprints for giant/no-gold validation outputs.
#SBATCH --job-name=km-tail-fulliri
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=22G
#SBATCH --array=0-8%6
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/fulliri-%A_%a.out

set -u

validation=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718
results=$validation/results
script=$validation/fingerprint_tail_fulliri.py
task=${SLURM_ARRAY_TASK_ID:-0}

case "$task" in
  0) label=km_production_3524; format=json ;;
  1) label=konclude_w16_3524; format=owlxml ;;
  2) label=elk_3524; format=functional ;;
  3) label=km_production_15703; format=json ;;
  4) label=konclude_w16_15703; format=owlxml ;;
  5) label=elk_15703; format=functional ;;
  6) label=km_production_4669; format=json ;;
  7) label=km_ht_bridge_4669; format=json ;;
  8) label=elk_4669; format=functional ;;
  *) /usr/bin/printf 'invalid task %s\n' "$task" >&2; exit 2 ;;
esac

out=$results/$label
input=$out/stdout.log
if [[ "$format" == functional || "$format" == owlxml ]]; then
  input=$out/taxonomy.owl
fi
if [[ ! -s "$input" ]]; then
  /usr/bin/printf 'missing retained output: %s\n' "$input" >&2
  exit 2
fi

/usr/bin/timeout -k 10 900 /usr/bin/python3 "$script" \
  --input "$input" --format "$format" --output-prefix "$out/fulliri" \
  > "$out/fulliri.stdout" 2> "$out/fulliri.stderr"
rc=$?
/usr/bin/printf 'DONE label=%s task=%s rc=%s host=%s\n' \
  "$label" "$task" "$rc" "$(hostname)"
exit "$rc"
