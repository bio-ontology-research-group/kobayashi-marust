#!/bin/bash
# Preliminary cross-reasoner adjudication only. These records never satisfy
# the full-sweep checkpoint contract.
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --array=0-11%6
#SBATCH --job-name=km-paper-disagreement-probe
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/disagreement-probe-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
km_root=/ibex/scratch/hohndor/km
ontologies=(cvdo doid)
baselines=(konclude jfact openllet more elk whelk)
factories=(
  ""
  uk.ac.manchester.cs.jfact.JFactFactory
  openllet.owlapi.OpenlletReasonerFactory
  org.semanticweb.more.reasoner.MOReReasonerFactory
  org.semanticweb.elk.owlapi.ElkReasonerFactory
  org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory
)
ontology=${ontologies[$((SLURM_ARRAY_TASK_ID % 2))]}
baseline_index=$((SLURM_ARRAY_TASK_ID / 2))
baseline=${baselines[$baseline_index]}
factory=${factories[$baseline_index]}
input=$root/obo-snapshot/merged/$ontology.ofn
output_root=$root/disagreement-probes
mkdir -p "$output_root/$baseline"

cpu_model=$(awk -F ': ' '/model name/{print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]

if test "$baseline" = konclude; then
  runtime_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
  runtime=$runtime_root/Konclude-build-a
  runner=$root/runner-tools/run_native_one.py
  PYTHONPATH=$root/runner-tools python3 "$runner" \
    --baseline "$baseline" --binary "$runtime" \
    --library-path "$runtime_root/runtime-lib" \
    --ontology "$input" --ontology-id "$ontology" \
    --output-root "$output_root" --tools-root "$root/runner-tools" \
    --timeout 600 --memcap-mb 32768
else
  runtime=$root/runtimes/classifier-$baseline.jar
  runner=$root/runner-tools/run_java_one.py
  PYTHONPATH=$root/runner-tools python3 "$runner" \
    --baseline "$baseline" --factory "$factory" --jar "$runtime" \
    --ontology "$input" --ontology-id "$ontology" \
    --output-root "$output_root" --tools-root "$root/runner-tools" \
    --timeout 600 --memcap-mb 32768
fi
python3 "$root/runner-tools/validate_result.py" \
  --result "$output_root/$baseline/$ontology.result.json" \
  --baseline "$baseline" --ontology-id "$ontology" \
  --ontology "$input" --runtime "$runtime" --runner "$runner"
printf 'DISAGREEMENT_PROBE_TERMINAL\t%s\t%s\n' "$baseline" "$ontology"
