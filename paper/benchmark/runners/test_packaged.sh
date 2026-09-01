#!/bin/bash
set -euo pipefail

root=$(git rev-parse --show-toplevel)
artifacts=$root/.work/artifacts/paper-baselines
outputs=$root/.work/artifacts/paper-baseline-smoke
validator=$root/paper/benchmark/runners/validate_output.py
tests=$root/paper/benchmark/runners/tests
mkdir -p "$outputs"

declare -A factory=(
  [hermit]=org.semanticweb.HermiT.ReasonerFactory
  [jfact]=uk.ac.manchester.cs.jfact.JFactFactory
  [openllet]=openllet.owlapi.OpenlletReasonerFactory
  [elk]=org.semanticweb.elk.owlapi.ElkReasonerFactory
  [whelk]=org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory
)

for baseline in hermit jfact openllet elk whelk; do
  jar=$artifacts/classifier-$baseline.jar
  test -s "$jar"
  for case in taxonomy inconsistent; do
    output=$outputs/$baseline-$case.tsv
    rm -f "$output" "$output.part"
    java --add-opens=java.base/java.lang=ALL-UNNAMED -Xmx2g -jar "$jar" \
      "${factory[$baseline]}" "$tests/$case.ofn" "$output"
    "$validator" "$output"
    test ! -e "$output.part"
    if test "$case" = taxonomy; then
      grep -Fx $'C\ttrue' "$output"
      grep -Fx $'U\thttp://example.org/km-paper-test#D' "$output"
      grep -Fx $'S\thttp://example.org/km-paper-test#A\thttp://example.org/km-paper-test#B' "$output"
      grep -Fx $'S\thttp://example.org/km-paper-test#A\thttp://example.org/km-paper-test#C' "$output"
    else
      grep -Fx $'C\tfalse' "$output"
      test "$(grep -c $'^S\t\|^U\t' "$output" || true)" -eq 0
    fi
  done
done
