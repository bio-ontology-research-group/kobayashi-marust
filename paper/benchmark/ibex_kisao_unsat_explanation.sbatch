#!/bin/bash
# Source-bound explanation for one KISAO bottom entailment omitted by JFact.
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --job-name=km-paper-kisao-unsat
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/kisao-unsat-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
helper=$root/runner-tools/entailment-explanation.jar
runtime=$root/runtimes/classifier-hermit.jar
test "$(sha256sum "$helper" | awk '{print $1}')" = \
  4ef0527e488a0a59f2c253d6e85a31a0dd228dbc944810b9f24aae3b166f79ef
test "$(sha256sum "$runtime" | awk '{print $1}')" = \
  59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c

output=$root/diagnostics/entailment-explanations/kisao-unsat-0000086
mkdir -p "$output"
/usr/bin/time -v -o "$output/time.txt" \
  /usr/bin/java -Xmx30g --add-opens=java.base/java.lang=ALL-UNNAMED \
  -cp "$helper:$runtime" org.kmbenchmark.EntailmentExplanation \
  org.semanticweb.HermiT.ReasonerFactory \
  "$root/obo-snapshot/merged/kisao.ofn" \
  'http://www.biomodels.net/kisao/KISAO#KISAO_0000086' \
  'http://www.w3.org/2002/07/owl#Nothing' \
  "$output/module.ofn" "$output/explanation.tsv"
test "$(grep -F $'M\tentailed\t' "$output/explanation.tsv")" = $'M\tentailed\ttrue'
test "$(tail -n 1 "$output/explanation.tsv")" = $'Z\tcomplete'
sha256sum "$root/obo-snapshot/merged/kisao.ofn" "$output/module.ofn" \
  "$output/explanation.tsv" > "$output/SHA256SUMS"
printf 'KISAO_UNSAT_EXPLANATION_OK\n'
