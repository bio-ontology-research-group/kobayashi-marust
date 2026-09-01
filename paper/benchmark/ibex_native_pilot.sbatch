#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --array=0-3%2
#SBATCH --job-name=km-paper-native-pilot
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/native-pilot-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
km_root=/ibex/scratch/hohndor/km
cpu_model=$(awk -F ': ' '/model name/{print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]

baselines=(km konclude)
ontologies=(ado mondo)
baseline_index=$((SLURM_ARRAY_TASK_ID / 2))
ontology_index=$((SLURM_ARRAY_TASK_ID % 2))
baseline=${baselines[$baseline_index]}
ontology_id=${ontologies[$ontology_index]}
ontology=$root/obo-snapshot/merged/$ontology_id.ofn
test -s "$ontology"
if test "$baseline" = km; then
  binary=$km_root/v1.3.0-candidate-5c64a02/km
  test "$(sha256sum "$binary" | awk '{print $1}')" = cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d
  extra=()
else
  konclude_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
  binary=$konclude_root/Konclude-build-a
  test "$(sha256sum "$binary" | awk '{print $1}')" = e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4
  (cd "$konclude_root" && sha256sum --check runtime-files.sha256)
  extra=(--library-path "$konclude_root/runtime-lib")
fi

PYTHONPATH=$root/runner-tools python3 "$root/runner-tools/run_native_one.py" \
  --baseline "$baseline" --binary "$binary" "${extra[@]}" \
  --ontology "$ontology" --ontology-id "$ontology_id" \
  --output-root "$root/native-pilot-results" --tools-root "$root/runner-tools" \
  --timeout 600 --memcap-mb 32768
result=$root/native-pilot-results/$baseline/$ontology_id.result.json
test -s "$result"
test "$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["status"])' "$result")" != running
printf 'NATIVE_PILOT_TERMINAL\t%s\t%s\n' "$baseline" "$ontology_id"
