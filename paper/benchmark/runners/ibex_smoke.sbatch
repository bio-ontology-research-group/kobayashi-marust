#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=4G
#SBATCH --array=0-11%6
#SBATCH --job-name=km-paper-baseline-smoke
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/baseline-smoke-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
runtime=$root/runtimes
tests=$root/runner-tests
outputs=$root/runner-smoke
mkdir -p "$outputs"
(cd "$runtime" && sha256sum --check SHA256SUMS)

baselines=(hermit jfact openllet elk whelk more)
factories=(
  org.semanticweb.HermiT.ReasonerFactory
  uk.ac.manchester.cs.jfact.JFactFactory
  openllet.owlapi.OpenlletReasonerFactory
  org.semanticweb.elk.owlapi.ElkReasonerFactory
  org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory
  org.semanticweb.more.reasoner.MOReReasonerFactory
)
cases=(taxonomy inconsistent)
baseline_index=$((SLURM_ARRAY_TASK_ID / 2))
case_index=$((SLURM_ARRAY_TASK_ID % 2))
baseline=${baselines[$baseline_index]}
factory=${factories[$baseline_index]}
case_name=${cases[$case_index]}
jar=$runtime/classifier-$baseline.jar
output=$outputs/$baseline-$case_name.tsv
rm -f "$output" "$output.part"

if test "$baseline" = more; then
  java --add-opens=java.base/java.lang=ALL-UNNAMED -Xmx3g -cp "$jar" \
    org.kmbenchmark.FullIriClassifier3 "$factory" "$tests/$case_name.ofn" "$output"
else
  java --add-opens=java.base/java.lang=ALL-UNNAMED -Xmx3g -jar "$jar" \
    "$factory" "$tests/$case_name.ofn" "$output"
fi
python3 "$tests/validate_output.py" "$output"
test ! -e "$output.part"

if test "$case_name" = taxonomy; then
  grep -Fx $'U\thttp://example.org/km-paper-test#D' "$output"
  grep -Fx $'S\thttp://example.org/km-paper-test#A\thttp://example.org/km-paper-test#B' "$output"
  grep -Fx $'S\thttp://example.org/km-paper-test#A\thttp://example.org/km-paper-test#C' "$output"
  if test "$baseline" = more; then grep -Fx $'C\tunknown' "$output"; else grep -Fx $'C\ttrue' "$output"; fi
else
  if test "$baseline" = more; then grep -Fx $'C\tunknown' "$output"; else grep -Fx $'C\tfalse' "$output"; fi
fi
printf 'SMOKE_OK\t%s\t%s\n' "$baseline" "$case_name"
