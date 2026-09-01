#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --array=0-7%4
#SBATCH --job-name=km-paper-fma-benchmark
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/fma-benchmark-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
km_root=/ibex/scratch/hohndor/km
cpu_model=$(awk -F ': ' '/model name/{print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
baselines=(km konclude hermit jfact openllet more elk whelk)
factories=(
  '' ''
  org.semanticweb.HermiT.ReasonerFactory
  uk.ac.manchester.cs.jfact.JFactFactory
  openllet.owlapi.OpenlletReasonerFactory
  org.semanticweb.more.reasoner.MOReReasonerFactory
  org.semanticweb.elk.owlapi.ElkReasonerFactory
  org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory
)
baseline=${baselines[$SLURM_ARRAY_TASK_ID]}
ontology=$root/hard-cases/merged/fma.ofn
test -s "$ontology"
test "$(tail -n 1 "$root/hard-cases/profiles/fma.tsv")" = $'Z\tcomplete'

if test "$baseline" = km; then
  runtime=$km_root/v1.3.0-candidate-5c64a02/km
  test "$(sha256sum "$runtime" | awk '{print $1}')" = cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d
  runner=$root/runner-tools/run_native_one.py
  extra=(--binary "$runtime")
elif test "$baseline" = konclude; then
  konclude_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
  runtime=$konclude_root/Konclude-build-a
  test "$(sha256sum "$runtime" | awk '{print $1}')" = e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4
  (cd "$konclude_root" && sha256sum --check runtime-files.sha256)
  runner=$root/runner-tools/run_native_one.py
  extra=(--binary "$runtime" --library-path "$konclude_root/runtime-lib")
else
  runtime=$root/runtimes/classifier-$baseline.jar
  runner=$root/runner-tools/run_java_one.py
  extra=(--jar "$runtime" --factory "${factories[$SLURM_ARRAY_TASK_ID]}")
fi
result=$root/hard-results/$baseline/fma.result.json
if python3 "$root/runner-tools/validate_result.py" \
    --result "$result" --baseline "$baseline" --ontology-id fma \
    --ontology "$ontology" --runtime "$runtime" --runner "$runner" >/dev/null 2>&1; then
  printf 'FMA_BENCHMARK_RESUME_OK\t%s\n' "$baseline"
  exit 0
fi

PYTHONPATH=$root/runner-tools python3 "$runner" \
  --baseline "$baseline" "${extra[@]}" --ontology "$ontology" --ontology-id fma \
  --output-root "$root/hard-results" --tools-root "$root/runner-tools" \
  --timeout 600 --memcap-mb 32768
python3 "$root/runner-tools/validate_result.py" \
  --result "$result" --baseline "$baseline" --ontology-id fma \
  --ontology "$ontology" --runtime "$runtime" --runner "$runner"
printf 'FMA_BENCHMARK_TERMINAL\t%s\n' "$baseline"
