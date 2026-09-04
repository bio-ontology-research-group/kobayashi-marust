#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=6G
#SBATCH --job-name=km-enable-final

set -euo pipefail
: "${IMPACT_ROOT:?set IMPACT_ROOT}"

validator="$IMPACT_ROOT/staged/validate_enablement_extension.py"
old_impact=/ibex/scratch/hohndor/km/v1.4-paper-impact-20260903
output="$IMPACT_ROOT/summary.json"
test -s "$validator"
rm -f "$output" "$IMPACT_ROOT/FINAL_RECEIPT.tsv"
/usr/bin/time -v -o "$IMPACT_ROOT/validation.time" \
  /usr/bin/python3 "$validator" --root "$IMPACT_ROOT" \
  --old-impact-root "$old_impact" --output "$output" \
  > "$IMPACT_ROOT/validation.stdout.json"
test -s "$output"
test "$(/usr/bin/python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["status"])' "$output")" = validated

{
  printf 'schema\t1\nstatus\tvalidated\n'
  printf 'slurm_job_id\t%s\nhost\t%s\n' "$SLURM_JOB_ID" "$(hostname)"
  printf 'summary_sha256\t%s\n' "$(sha256sum "$output" | awk '{print $1}')"
  printf 'validator_sha256\t%s\n' "$(sha256sum "$validator" | awk '{print $1}')"
  printf 'prepare_script_sha256\t%s\n' "$(sha256sum "$IMPACT_ROOT/staged/ibex_enablement_prepare.sbatch" | awk '{print $1}')"
  printf 'run_script_sha256\t%s\n' "$(sha256sum "$IMPACT_ROOT/staged/ibex_enablement_run.sbatch" | awk '{print $1}')"
  printf 'finalize_script_sha256\t%s\n' "$(sha256sum "$IMPACT_ROOT/staged/ibex_enablement_finalize.sbatch" | awk '{print $1}')"
  grep -E 'Elapsed \(wall clock\)|Maximum resident set size|Exit status' "$IMPACT_ROOT/validation.time" || true
  printf 'terminal_marker\tVALIDATION_COMPLETE\n'
} > "$IMPACT_ROOT/FINAL_RECEIPT.tsv"
