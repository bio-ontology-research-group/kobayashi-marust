#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=18G
#SBATCH --array=0-10%2
#SBATCH --job-name=km-enable-run

set -euo pipefail
: "${IMPACT_ROOT:?set IMPACT_ROOT}"

benchmark=/ibex/scratch/hohndor/km/paper-benchmark-20260830
tools="$benchmark/runner-tools"
old_impact=/ibex/scratch/hohndor/km/v1.4-paper-impact-20260903
binary="$old_impact/target/release/km"
staged="$IMPACT_ROOT/staged"
inputs="$IMPACT_ROOT/inputs"
results="$IMPACT_ROOT/results"
mkdir -p "$results" "$IMPACT_ROOT/logs"

test -s "$IMPACT_ROOT/receipts/preparation.receipt.tsv"
grep -Fxq $'terminal_marker\tPREPARATION_COMPLETE' "$IMPACT_ROOT/receipts/preparation.receipt.tsv"
test "$(sha256sum "$binary" | awk '{print $1}')" = c8688f6b286db2b422f1ec1df0874eadbbce0cc9e2899f35dbe143ccad70639d

run_km_classify() {
  local name=$1 ontology=$2 timeout_s=$3
  local prefix="$results/km/$name"
  mkdir -p "$(dirname "$prefix")"
  rm -f "$prefix".{json,stderr,time,receipt.tsv} "$prefix".fingerprint.*
  set +e
  /usr/bin/time -v -o "$prefix.time" /usr/bin/timeout -k 10 "$timeout_s" \
    /usr/bin/env KM_ROUTE=auto KM_THREADS=4 KM_PAR_MEM_GB=14 KM_HT_MEM_GB=14 \
    "$binary" classify "$ontology" > "$prefix.json" 2> "$prefix.stderr"
  rc=$?
  set -e
  status=error
  if [ "$rc" -eq 0 ] && python3 -m json.tool "$prefix.json" >/dev/null; then status=ok; fi
  if [ "$status" = ok ]; then
    PYTHONPATH="$tools" python3 "$tools/full_iri_fingerprint.py" \
      --input "$prefix.json" --format json --source-ontology "$ontology" \
      --output-prefix "$prefix.fingerprint" > "$prefix.fingerprint.stdout.json"
  fi
  {
    printf 'schema\t1\ncase\t%s\nstatus\t%s\nexit_code\t%s\n' "$name" "$status" "$rc"
    printf 'source_commit\t301d37426cdf3dea249d9609037a2f1e47e89314\n'
    printf 'route\tauto\nthreads\t4\nparallel_mem_gb\t14\nht_mem_gb\t14\n'
    printf 'binary_sha256\t%s\n' "$(sha256sum "$binary" | awk '{print $1}')"
    printf 'ontology_path\t%s\nontology_sha256\t%s\n' "$ontology" "$(sha256sum "$ontology" | awk '{print $1}')"
    printf 'output_sha256\t%s\noutput_bytes\t%s\n' "$(sha256sum "$prefix.json" | awk '{print $1}')" "$(stat -c %s "$prefix.json")"
    printf 'stderr_sha256\t%s\n' "$(sha256sum "$prefix.stderr" | awk '{print $1}')"
    printf 'slurm_job_id\t%s\nslurm_array_task_id\t%s\nhost\t%s\n' "$SLURM_JOB_ID" "$SLURM_ARRAY_TASK_ID" "$(hostname)"
    grep -E 'Elapsed \(wall clock\)|Maximum resident set size|Exit status' "$prefix.time" || true
    printf 'terminal_marker\tTASK_COMPLETE\n'
  } > "$prefix.receipt.tsv"
  test "$status" = ok
}

run_java() {
  local reasoner=$1 name=$2 ontology=$3
  local jar factory
  case "$reasoner" in
    elk) jar="$benchmark/runtimes/classifier-elk.jar"; factory=org.semanticweb.elk.owlapi.ElkReasonerFactory ;;
    hermit) jar="$benchmark/runtimes/classifier-hermit.jar"; factory=org.semanticweb.HermiT.ReasonerFactory ;;
    *) exit 2 ;;
  esac
  PYTHONPATH="$tools" python3 "$tools/run_java_one.py" \
    --baseline "$reasoner" --factory "$factory" --jar "$jar" \
    --ontology "$ontology" --ontology-id "$name" \
    --output-root "$results" --tools-root "$tools" \
    --timeout 1200 --memcap-mb 14336
  test "$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["status"])' "$results/$reasoner/$name.result.json")" = ok
}

run_explain() {
  local ontology="$staged/product-configuration-conflict.ofn"
  local prefix="$results/km/product-conflict-explain"
  mkdir -p "$(dirname "$prefix")"
  rm -f "$prefix".{json,stderr,time,receipt.tsv}
  set +e
  /usr/bin/time -v -o "$prefix.time" /usr/bin/timeout -k 10 600 \
    /usr/bin/env KM_ROUTE=auto KM_THREADS=4 \
    "$binary" explain --pretty --max-axioms 64 --max-checks 256 \
    --max-justifications 1 "$ontology" unsatisfiable \
    http://example.org/km-impact/configuration#DualSensorSurveyDrone \
    > "$prefix.json" 2> "$prefix.stderr"
  rc=$?
  set -e
  test "$rc" -eq 0
  python3 -m json.tool "$prefix.json" >/dev/null
  {
    printf 'schema\t1\ncase\tproduct-conflict-explain\nstatus\tok\nexit_code\t%s\n' "$rc"
    printf 'binary_sha256\t%s\n' "$(sha256sum "$binary" | awk '{print $1}')"
    printf 'ontology_sha256\t%s\n' "$(sha256sum "$ontology" | awk '{print $1}')"
    printf 'output_sha256\t%s\noutput_bytes\t%s\n' "$(sha256sum "$prefix.json" | awk '{print $1}')" "$(stat -c %s "$prefix.json")"
    printf 'slurm_job_id\t%s\nslurm_array_task_id\t%s\nhost\t%s\n' "$SLURM_JOB_ID" "$SLURM_ARRAY_TASK_ID" "$(hostname)"
    grep -E 'Elapsed \(wall clock\)|Maximum resident set size|Exit status' "$prefix.time" || true
    printf 'terminal_marker\tTASK_COMPLETE\n'
  } > "$prefix.receipt.tsv"
}

case "$SLURM_ARRAY_TASK_ID" in
  0) run_km_classify product-control-full "$staged/product-configuration-control.ofn" 600 ;;
  1) run_km_classify product-conflict-full "$staged/product-configuration-conflict.ofn" 600 ;;
  2) run_java hermit product-control-full "$staged/product-configuration-control.ofn" ;;
  3) run_java hermit product-conflict-full "$staged/product-configuration-conflict.ofn" ;;
  4) run_km_classify product-control-el "$inputs/product-control-el.ofn" 600 ;;
  5) run_km_classify product-conflict-el "$inputs/product-conflict-el.ofn" 600 ;;
  6) run_java elk product-control-el "$inputs/product-control-el.ofn" ;;
  7) run_java elk product-conflict-el "$inputs/product-conflict-el.ofn" ;;
  8) run_km_classify galen-ore9724-el "$inputs/galen-ore9724-el.ofn" 1200 ;;
  9) run_java elk galen-ore9724-el "$inputs/galen-ore9724-el.ofn" ;;
  10) run_explain ;;
  *) exit 2 ;;
esac
