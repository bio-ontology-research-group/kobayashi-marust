#!/bin/bash
# Exact low-memory canonicalization of retained tail-validation outputs.
#SBATCH --job-name=km-tail-bitset
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=22G
#SBATCH --array=0-13%4
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/bitset-%A_%a.out

set -u

root=/ibex/scratch/hohndor/km/routing_20260715
validation=$root/tail-validation-20260718
results=$validation/results
canonicalizer=$root/oracle/ore/ore_canon.py
script=$validation/canonicalize_tail_bitset.py
task=${SLURM_ARRAY_TASK_ID:-0}

case "$task" in
  0) label=km_ht_bridge_4669; format=json ;;
  1) label=km_ht_full_4669; format=json ;;
  2) label=km_production_4669; format=json ;;
  3) label=km_production_3524; format=json ;;
  4) label=km_production_15703; format=json ;;
  5) label=konclude_w16_3524; format=owlxml ;;
  6) label=hermit_3524; format=json ;;
  7) label=elk_3524; format=functional ;;
  8) label=konclude_w16_15703; format=owlxml ;;
  9) label=hermit_15703; format=json ;;
  10) label=elk_15703; format=functional ;;
  11) label=konclude_w16_4669; format=owlxml ;;
  12) label=hermit_4669; format=json ;;
  13) label=elk_4669; format=functional ;;
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
  --canonicalizer "$canonicalizer" --input "$input" --format "$format" \
  --output "$out/signature-bitset.sig.gz" \
  > "$out/canonicalize-bitset.stdout" 2> "$out/canonicalize-bitset.stderr"
rc=$?
/usr/bin/printf 'DONE label=%s task=%s rc=%s host=%s\n' \
  "$label" "$task" "$rc" "$(hostname)"
exit "$rc"
