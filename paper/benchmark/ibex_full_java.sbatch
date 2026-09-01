#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --array=0-1133%8
#SBATCH --job-name=km-paper-java-full
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/java-full-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
manifest=$root/obo-snapshot/obo-freeze-20260830.tsv
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
eligible_count=189
baseline_index=$((SLURM_ARRAY_TASK_ID / eligible_count))
ontology_position=$((SLURM_ARRAY_TASK_ID % eligible_count))
baseline=${baselines[$baseline_index]}
factory=${factories[$baseline_index]}
ontology_id=$(awk -F '\t' '$5 == "true" {n++; if (n == wanted) {print $2; exit}}' \
  wanted=$((ontology_position + 1)) "$manifest")
test -n "$ontology_id"
ontology=$root/obo-snapshot/merged/$ontology_id.ofn
profile=$root/obo-snapshot/profiles/$ontology_id.tsv
runtime=$root/runtimes/classifier-$baseline.jar
runner=$root/runner-tools/run_java_one.py
validator=$root/runner-tools/validate_result.py
validator_sha256=5ae4d5d6ae897677bb515ef7715c13557c97f6dfbf926fae70c0af41268aa6ac
result=$root/current-results/$baseline/$ontology_id.result.json
test -s "$ontology"
test "$(tail -n 1 "$profile")" = $'Z\tcomplete'
test "$(sha256sum "$validator" | awk '{print $1}')" = "$validator_sha256"

if python3 "$validator" \
    --result "$result" --baseline "$baseline" --ontology-id "$ontology_id" \
    --ontology "$ontology" --runtime "$runtime" --runner "$runner" >/dev/null 2>&1; then
  printf 'JAVA_FULL_RESUME_OK\t%s\t%s\n' "$baseline" "$ontology_id"
  exit 0
fi

PYTHONPATH=$root/runner-tools python3 "$runner" \
  --baseline "$baseline" --factory "$factory" --jar "$runtime" \
  --ontology "$ontology" --ontology-id "$ontology_id" \
  --output-root "$root/current-results" --tools-root "$root/runner-tools" \
  --timeout 600 --memcap-mb 32768
python3 "$validator" \
  --result "$result" --baseline "$baseline" --ontology-id "$ontology_id" \
  --ontology "$ontology" --runtime "$runtime" --runner "$runner"
printf 'JAVA_FULL_TERMINAL\t%s\t%s\n' "$baseline" "$ontology_id"
