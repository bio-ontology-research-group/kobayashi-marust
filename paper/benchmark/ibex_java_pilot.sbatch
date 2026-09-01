#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --array=0-11%4
#SBATCH --job-name=km-paper-java-pilot
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/java-pilot-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
cpu_model=$(awk -F ': ' '/model name/{print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]

baselines=(hermit jfact openllet elk whelk more)
factories=(
  org.semanticweb.HermiT.ReasonerFactory
  uk.ac.manchester.cs.jfact.JFactFactory
  openllet.owlapi.OpenlletReasonerFactory
  org.semanticweb.elk.owlapi.ElkReasonerFactory
  org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory
  org.semanticweb.more.reasoner.MOReReasonerFactory
)
ontologies=(ado mondo)
baseline_index=$((SLURM_ARRAY_TASK_ID / 2))
ontology_index=$((SLURM_ARRAY_TASK_ID % 2))
baseline=${baselines[$baseline_index]}
factory=${factories[$baseline_index]}
ontology_id=${ontologies[$ontology_index]}
ontology=$root/obo-snapshot/merged/$ontology_id.ofn
test -s "$ontology"

PYTHONPATH=$root/runner-tools python3 "$root/runner-tools/run_java_one.py" \
  --baseline "$baseline" --factory "$factory" \
  --jar "$root/runtimes/classifier-$baseline.jar" \
  --ontology "$ontology" --ontology-id "$ontology_id" \
  --output-root "$root/java-pilot-results" --tools-root "$root/runner-tools" \
  --timeout 600 --memcap-mb 32768

result=$root/java-pilot-results/$baseline/$ontology_id.result.json
test -s "$result"
test "$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["status"])' "$result")" != running
printf 'JAVA_PILOT_TERMINAL\t%s\t%s\n' "$baseline" "$ontology_id"
