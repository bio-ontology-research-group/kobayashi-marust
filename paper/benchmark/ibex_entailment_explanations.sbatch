#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --array=0-1%2
#SBATCH --job-name=km-paper-entailment-explanation
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/entailment-explanation-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
helper=$root/runner-tools/entailment-explanation.jar
runtime=$root/runtimes/classifier-hermit.jar
test "$(sha256sum "$helper" | awk '{print $1}')" = \
  4ef0527e488a0a59f2c253d6e85a31a0dd228dbc944810b9f24aae3b166f79ef
test "$(sha256sum "$runtime" | awk '{print $1}')" = \
  59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c

ids=(doid cvdo)
subs=(DOID_1024 CVDO_0000010)
supers=(DOID_7 CVDO_0000546)
id=${ids[$SLURM_ARRAY_TASK_ID]}
base=http://purl.obolibrary.org/obo/
output=$root/diagnostics/entailment-explanations/$id
mkdir -p "$output"
/usr/bin/time -v -o "$output/time.txt" \
  /usr/bin/java -Xmx30g --add-opens=java.base/java.lang=ALL-UNNAMED \
  -cp "$helper:$runtime" org.kmbenchmark.EntailmentExplanation \
  org.semanticweb.HermiT.ReasonerFactory \
  "$root/obo-snapshot/merged/$id.ofn" \
  "$base${subs[$SLURM_ARRAY_TASK_ID]}" \
  "$base${supers[$SLURM_ARRAY_TASK_ID]}" \
  "$output/module.ofn" "$output/explanation.tsv"
test "$(tail -n 1 "$output/explanation.tsv")" = $'Z\tcomplete'
printf 'ENTAILMENT_EXPLANATION_OK\t%s\n' "$id"
