#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=01:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --array=0-1%2
#SBATCH --job-name=km-impact-uberon-routes

set -euo pipefail
: "${IMPACT_ROOT:?set IMPACT_ROOT}"
binary="$IMPACT_ROOT/target/release/km"
ontology=/ibex/scratch/hohndor/km/paper-benchmark-20260830/obo-snapshot/merged/uberon.ofn
results="$IMPACT_ROOT/results"
mkdir -p "$results"
test -x "$binary"
test -s "$IMPACT_ROOT/build-receipt.tsv"
test "$(awk -F '\t' '$1 == "binary_sha256" {print $2}' "$IMPACT_ROOT/build-receipt.tsv")" = "$(sha256sum "$binary" | awk '{print $1}')"
routes=(production_all1 certified_nominals)
route=${routes[$SLURM_ARRAY_TASK_ID]}
prefix="$results/uberon-$route"
rm -f "$prefix".{json,stderr,time,receipt.tsv} \
  "$prefix".fingerprint.{json,tsv,stdout.json}
set +e
/usr/bin/time -v -o "$prefix.time" /usr/bin/timeout -k 10 3600 \
  /usr/bin/env KM_THREADS=1 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18 \
  "$binary" classify --route "$route" "$ontology" > "$prefix.json" 2> "$prefix.stderr"
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
  printf 'case\tuberon-%s\n' "$route"
  printf 'route\t%s\n' "$route"
  printf 'status\t%s\n' "$status"
  printf 'exit_code\t%s\n' "$rc"
  printf 'source_commit\t%s\n' "$(awk -F '\t' '$1 == "source_commit" {print $2}' "$IMPACT_ROOT/build-receipt.tsv")"
  printf 'binary_sha256\t%s\n' "$(sha256sum "$binary" | awk '{print $1}')"
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
