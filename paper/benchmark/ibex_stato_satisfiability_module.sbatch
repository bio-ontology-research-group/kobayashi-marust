#!/bin/bash
# Source-bound locality-module adjudication of JFact's STATO_0000073 bottom result.
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=36G
#SBATCH --job-name=km-paper-stato-module
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/stato-module-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
helper=$root/runner-tools/entailment-explanation.jar
hermit=$root/runtimes/classifier-hermit.jar
runner=$root/runner-tools/run_java_one.py
out=$root/diagnostics/stato-0000073-module
source=$root/obo-snapshot/merged/stato.ofn
class=http://purl.obolibrary.org/obo/STATO_0000073
bottom=http://www.w3.org/2002/07/owl#Nothing

test "$(sha256sum "$helper" | awk '{print $1}')" = \
  4ef0527e488a0a59f2c253d6e85a31a0dd228dbc944810b9f24aae3b166f79ef
test "$(sha256sum "$hermit" | awk '{print $1}')" = \
  59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c
mkdir -p "$out"

/usr/bin/time -v -o "$out/extraction.time" \
  /usr/bin/java -Xmx30g --add-opens=java.base/java.lang=ALL-UNNAMED \
  -cp "$helper:$hermit" org.kmbenchmark.EntailmentExplanation \
  org.semanticweb.HermiT.ReasonerFactory "$source" "$class" "$bottom" \
  "$out/module.ofn" "$out/hermit-query.tsv"
test "$(grep -F $'M\tentailed\t' "$out/hermit-query.tsv")" = \
  $'M\tentailed\tfalse'
test "$(tail -n 1 "$out/hermit-query.tsv")" = $'Z\tcomplete'

for baseline in jfact openllet; do
  case $baseline in
    jfact)
      factory=uk.ac.manchester.cs.jfact.JFactFactory ;;
    openllet)
      factory=openllet.owlapi.OpenlletReasonerFactory ;;
  esac
  runtime=$root/runtimes/classifier-$baseline.jar
  PYTHONPATH=$root/runner-tools /usr/bin/python3 "$runner" \
    --baseline "$baseline" --factory "$factory" --jar "$runtime" \
    --ontology "$out/module.ofn" --ontology-id stato-0000073-module \
    --output-root "$out/results" --tools-root "$root/runner-tools" \
    --timeout 600 --memcap-mb 32768
  result=$out/results/$baseline/stato-0000073-module.result.json
  /usr/bin/python3 - "$result" "$baseline" <<'PY'
import json
import sys
from pathlib import Path

record = json.loads(Path(sys.argv[1]).read_text())
if record.get("status") != "ok":
    raise SystemExit(f"{sys.argv[2]} did not complete: {record.get('status')}")
PY
done

grep -F $'U\thttp://purl.obolibrary.org/obo/STATO_0000073' \
  "$out/results/jfact/stato-0000073-module.taxonomy.tsv" > "$out/jfact-bottom.tsv"
if grep -Fq $'U\thttp://purl.obolibrary.org/obo/STATO_0000073' \
  "$out/results/openllet/stato-0000073-module.taxonomy.tsv"; then
  echo 'Openllet unexpectedly reports STATO_0000073 bottom' >&2
  exit 1
fi

(
  cd "$out"
  sha256sum module.ofn hermit-query.tsv jfact-bottom.tsv \
    results/jfact/stato-0000073-module.result.json \
    results/openllet/stato-0000073-module.result.json
) > "$out/SHA256SUMS"
printf 'STATO_MODULE_ADJUDICATION_OK\n'
