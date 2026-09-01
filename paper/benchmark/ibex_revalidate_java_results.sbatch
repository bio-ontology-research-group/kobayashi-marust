#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --array=0-1133%16
#SBATCH --job-name=km-paper-java-revalidate
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/java-revalidate-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
manifest=$root/obo-snapshot/obo-freeze-20260830.tsv
baselines=(hermit jfact openllet elk whelk more)
eligible_count=189
baseline_index=$((SLURM_ARRAY_TASK_ID / eligible_count))
ontology_position=$((SLURM_ARRAY_TASK_ID % eligible_count))
baseline=${baselines[$baseline_index]}
ontology_id=$(awk -F '\t' '$5 == "true" {n++; if (n == wanted) {print $2; exit}}' \
  wanted=$((ontology_position + 1)) "$manifest")
test -n "$ontology_id"
ontology=$root/obo-snapshot/merged/$ontology_id.ofn
runtime=$root/runtimes/classifier-$baseline.jar
runner=$root/runner-tools/run_java_one.py
validator=$root/runner-tools/validate_result.py.next
result=$root/current-results/$baseline/$ontology_id.result.json
validator_sha256=5ae4d5d6ae897677bb515ef7715c13557c97f6dfbf926fae70c0af41268aa6ac
test "$(sha256sum "$validator" | awk '{print $1}')" = "$validator_sha256"
/usr/bin/python3 "$validator" --result "$result" --baseline "$baseline" \
  --ontology-id "$ontology_id" --ontology "$ontology" \
  --runtime "$runtime" --runner "$runner" >/dev/null
printf 'JAVA_REVALIDATE_OK\t%s\t%s\t%s\n' \
  "$SLURM_ARRAY_TASK_ID" "$baseline" "$ontology_id"
