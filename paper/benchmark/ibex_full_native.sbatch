#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --array=0-377%8
#SBATCH --job-name=km-paper-native-full
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/native-full-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
km_root=/ibex/scratch/hohndor/km
manifest=$root/obo-snapshot/obo-freeze-20260830.tsv
cpu_model=$(awk -F ': ' '/model name/{print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]

baselines=(km konclude)
eligible_count=189
baseline_index=$((SLURM_ARRAY_TASK_ID / eligible_count))
ontology_position=$((SLURM_ARRAY_TASK_ID % eligible_count))
baseline=${baselines[$baseline_index]}
ontology_id=$(awk -F '\t' '$5 == "true" {n++; if (n == wanted) {print $2; exit}}' \
  wanted=$((ontology_position + 1)) "$manifest")
test -n "$ontology_id"
ontology=$root/obo-snapshot/merged/$ontology_id.ofn
profile=$root/obo-snapshot/profiles/$ontology_id.tsv
runner=$root/runner-tools/run_native_one.py
validator=$root/runner-tools/validate_result.py
validator_sha256=5ae4d5d6ae897677bb515ef7715c13557c97f6dfbf926fae70c0af41268aa6ac
result=$root/current-results/$baseline/$ontology_id.result.json
test -s "$ontology"
test "$(tail -n 1 "$profile")" = $'Z\tcomplete'
test "$(sha256sum "$validator" | awk '{print $1}')" = "$validator_sha256"

if test "$baseline" = km; then
  runtime=$km_root/v1.3.0-candidate-5c64a02/km
  expected=cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d
  extra=()
  validation_extra=()
else
  konclude_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
  runtime=$konclude_root/Konclude-build-a
  expected=e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4
  (cd "$konclude_root" && sha256sum --check runtime-files.sha256)
  runtime_ontology=$root/obo-snapshot/verified-xml/$ontology_id.xml
  conversion_receipt=$root/obo-snapshot/verified-xml-receipts/$ontology_id.tsv
  test -s "$runtime_ontology"
  test "$(tail -n 1 "$conversion_receipt")" = $'Z\tcomplete'
  test "$(awk -F '\t' '$2 == "conversion" {print $3}' "$conversion_receipt")" = \
    konclude-compatible-serialization-v2
  test "$(awk -F '\t' '$2 == "roundtrip_logical_axioms_equal" {print $3}' "$conversion_receipt")" = true
  test "$(awk -F '\t' '$2 == "roundtrip_signature_equal" {print $3}' "$conversion_receipt")" = true
  test "$(awk -F '\t' '$2 == "source_sha256" {print $3}' "$conversion_receipt")" = \
    "$(sha256sum "$ontology" | awk '{print $1}')"
  test "$(awk -F '\t' '$2 == "output_sha256" {print $3}' "$conversion_receipt")" = \
    "$(sha256sum "$runtime_ontology" | awk '{print $1}')"
  extra=(--library-path "$konclude_root/runtime-lib" --input-ontology "$runtime_ontology")
  validation_extra=(--input-ontology "$runtime_ontology")
fi
test "$(sha256sum "$runtime" | awk '{print $1}')" = "$expected"

if python3 "$validator" \
    --result "$result" --baseline "$baseline" --ontology-id "$ontology_id" \
    --ontology "$ontology" "${validation_extra[@]}" \
    --runtime "$runtime" --runner "$runner" >/dev/null 2>&1; then
  printf 'NATIVE_FULL_RESUME_OK\t%s\t%s\n' "$baseline" "$ontology_id"
  exit 0
fi

PYTHONPATH=$root/runner-tools python3 "$runner" \
  --baseline "$baseline" --binary "$runtime" "${extra[@]}" \
  --ontology "$ontology" --ontology-id "$ontology_id" \
  --output-root "$root/current-results" --tools-root "$root/runner-tools" \
  --timeout 600 --memcap-mb 32768
python3 "$validator" \
  --result "$result" --baseline "$baseline" --ontology-id "$ontology_id" \
  --ontology "$ontology" "${validation_extra[@]}" --runtime "$runtime" --runner "$runner"
printf 'NATIVE_FULL_TERMINAL\t%s\t%s\n' "$baseline" "$ontology_id"
