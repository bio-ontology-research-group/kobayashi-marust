#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=01:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --array=0-9%4
#SBATCH --job-name=km-impact

set -euo pipefail
: "${IMPACT_ROOT:?set IMPACT_ROOT}"
: "${PAPER_ROOT:?set PAPER_ROOT}"
: "${SOURCE_COMMIT:?set SOURCE_COMMIT}"
binary="$IMPACT_ROOT/target/release/km"
cases="$PAPER_ROOT/paper/impact/cases"
results="$IMPACT_ROOT/results"
mkdir -p "$results" "$IMPACT_ROOT/logs"
test -x "$binary"
test -s "$IMPACT_ROOT/build-receipt.tsv"
test "$(awk -F '\t' '$1 == "source_commit" {print $2}' "$IMPACT_ROOT/build-receipt.tsv")" = "$SOURCE_COMMIT"
test "$(awk -F '\t' '$1 == "binary_sha256" {print $2}' "$IMPACT_ROOT/build-receipt.tsv")" = "$(sha256sum "$binary" | awk '{print $1}')"

names=(
  hidden-full-dl-negative
  hidden-full-dl-positive
  snomed-style-negative
  snomed-style-positive
  access-control-negative
  access-control-positive
  galen-ore9724
  galen-ore9724-repeat
  uberon-2026-06-23
  uberon-2026-06-23-repeat
)
name=${names[$SLURM_ARRAY_TASK_ID]}
case "$name" in
  galen-ore9724*) ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_9724.owl; timeout_s=600 ;;
  uberon-2026-06-23*) ontology=/ibex/scratch/hohndor/km/paper-benchmark-20260830/obo-snapshot/merged/uberon.ofn; timeout_s=3600 ;;
  *) ontology="$cases/$name.ofn"; timeout_s=300 ;;
esac
test -s "$ontology"

prefix="$results/$name"
rm -f "$prefix".{json,stderr,time,receipt.tsv} \
  "$prefix".fingerprint.{json,tsv,stdout.json}
set +e
/usr/bin/time -v -o "$prefix.time" \
  /usr/bin/timeout -k 10 "$timeout_s" \
  /usr/bin/env KM_ROUTE=auto KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18 \
  "$binary" classify "$ontology" > "$prefix.json" 2> "$prefix.stderr"
rc=$?
set -e
status=error
if [ "$rc" -eq 0 ] && python3 -m json.tool "$prefix.json" >/dev/null; then status=ok; fi
if [ "$status" = ok ]; then
  tools=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runner-tools
  PYTHONPATH="$tools" python3 "$tools/full_iri_fingerprint.py" \
    --input "$prefix.json" --format json --source-ontology "$ontology" \
    --output-prefix "$prefix.fingerprint" > "$prefix.fingerprint.stdout.json"
fi
{
  printf 'case\t%s\n' "$name"
  printf 'status\t%s\n' "$status"
  printf 'exit_code\t%s\n' "$rc"
  printf 'source_commit\t%s\n' "$SOURCE_COMMIT"
  printf 'binary_sha256\t%s\n' "$(sha256sum "$binary" | awk '{print $1}')"
  printf 'ontology_path\t%s\n' "$ontology"
  printf 'ontology_sha256\t%s\n' "$(sha256sum "$ontology" | awk '{print $1}')"
  printf 'output_sha256\t%s\n' "$(sha256sum "$prefix.json" | awk '{print $1}')"
  printf 'stderr_sha256\t%s\n' "$(sha256sum "$prefix.stderr" | awk '{print $1}')"
  if [ -s "$prefix.fingerprint.json" ]; then
    printf 'fingerprint_sha256\t%s\n' "$(sha256sum "$prefix.fingerprint.json" | awk '{print $1}')"
    python3 - "$prefix.fingerprint.json" <<'PY'
import json,sys
d=json.load(open(sys.argv[1]))
for key in ('consistent','unsatisfiable','subsumptions','taxonomy_sha256','relation_sha256'):
    print(f'{key}\t{d[key]}')
PY
  fi
  printf 'host\t%s\n' "$(hostname)"
  printf 'slurm_job_id\t%s\n' "$SLURM_JOB_ID"
  printf 'slurm_array_task_id\t%s\n' "$SLURM_ARRAY_TASK_ID"
  grep -E 'Elapsed \(wall clock\)|Maximum resident set size' "$prefix.time" || true
} > "$prefix.receipt.tsv"
test "$status" = ok
