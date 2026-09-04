#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=8G
#SBATCH --array=0-2%2
#SBATCH --job-name=km-impact-explain

set -euo pipefail
: "${IMPACT_ROOT:?set IMPACT_ROOT}"
: "${PAPER_ROOT:?set PAPER_ROOT}"
binary="$IMPACT_ROOT/target/release/km"
cases="$PAPER_ROOT/paper/impact/cases"
results="$IMPACT_ROOT/results"
mkdir -p "$results"
test -x "$binary"
test -s "$IMPACT_ROOT/build-receipt.tsv"
test "$(awk -F '\t' '$1 == "binary_sha256" {print $2}' "$IMPACT_ROOT/build-receipt.tsv")" = "$(sha256sum "$binary" | awk '{print $1}')"
names=(hidden-full-dl-positive snomed-style-positive access-control-positive)
classes=(http://example.org/impact#IntegratedFinding http://example.org/impact#BilateralProcedure http://example.org/impact#PrivilegedContractor)
name=${names[$SLURM_ARRAY_TASK_ID]}
class=${classes[$SLURM_ARRAY_TASK_ID]}
ontology="$cases/$name.ofn"
prefix="$results/$name.explain"
rm -f "$prefix".{json,stderr,time,receipt.tsv}
query=(unsatisfiable "$class")
if [ "$name" = snomed-style-positive ]; then query=(inconsistent); fi
set +e
/usr/bin/time -v -o "$prefix.time" /usr/bin/timeout -k 5 600 \
/usr/bin/env KM_ROUTE=auto KM_THREADS=4 "$binary" explain --pretty \
  --max-axioms 64 --max-checks 256 --max-justifications 1 \
  "$ontology" "${query[@]}" > "$prefix.json" 2> "$prefix.stderr"
rc=$?
set -e
test "$rc" -eq 0
python3 -m json.tool "$prefix.json" >/dev/null
{
  printf 'case\t%s\n' "$name"
  printf 'exit_code\t%s\n' "$rc"
  printf 'binary_sha256\t%s\n' "$(sha256sum "$binary" | awk '{print $1}')"
  printf 'ontology_sha256\t%s\n' "$(sha256sum "$ontology" | awk '{print $1}')"
  printf 'output_sha256\t%s\n' "$(sha256sum "$prefix.json" | awk '{print $1}')"
  printf 'slurm_job_id\t%s\n' "$SLURM_JOB_ID"
  printf 'slurm_array_task_id\t%s\n' "$SLURM_ARRAY_TASK_ID"
} > "$prefix.receipt.tsv"
