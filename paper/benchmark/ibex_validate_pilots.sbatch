#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --job-name=km-paper-pilot-validate
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/pilot-validate-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
km_root=/ibex/scratch/hohndor/km
baselines=(km konclude hermit jfact openllet elk whelk more)
ontologies=(ado mondo)
valid=0
for baseline in "${baselines[@]}"; do
  if test "$baseline" = km; then
    results=$root/native-pilot-results
    runtime=$km_root/v1.3.0-candidate-5c64a02/km
    runner=$root/runner-tools/run_native_one.py
  elif test "$baseline" = konclude; then
    results=$root/native-pilot-results
    runtime=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03/Konclude-build-a
    runner=$root/runner-tools/run_native_one.py
  else
    results=$root/java-pilot-results
    runtime=$root/runtimes/classifier-$baseline.jar
    runner=$root/runner-tools/run_java_one.py
  fi
  for ontology_id in "${ontologies[@]}"; do
    python3 "$root/runner-tools/validate_result.py" \
      --result "$results/$baseline/$ontology_id.result.json" \
      --baseline "$baseline" --ontology-id "$ontology_id" \
      --ontology "$root/obo-snapshot/merged/$ontology_id.ofn" \
      --runtime "$runtime" --runner "$runner"
    valid=$((valid + 1))
  done
done
test "$valid" = 16

python3 - <<'PY'
import json
from pathlib import Path
root = Path('/ibex/scratch/hohndor/km/paper-benchmark-20260830')
rows = {}
for baseline in ('km', 'konclude'):
    base = root / 'native-pilot-results'
    rows[baseline] = {name: json.load(open(base / baseline / (name + '.result.json')))
                      for name in ('ado', 'mondo')}
for baseline in ('hermit', 'jfact', 'openllet', 'elk', 'whelk', 'more'):
    base = root / 'java-pilot-results'
    rows[baseline] = {name: json.load(open(base / baseline / (name + '.result.json')))
                      for name in ('ado', 'mondo')}
ado = [rows[baseline]['ado'] for baseline in rows]
assert all(row['status'] == 'ok' for row in ado)
assert len({row['relation_sha256'] for row in ado}) == 1
normal = [row for baseline, row in ((b, rows[b]['ado']) for b in rows) if baseline != 'more']
assert len({row['taxonomy_sha256'] for row in normal}) == 1
summary = {baseline: {ontology: rows[baseline][ontology]['status']
                      for ontology in ('ado', 'mondo')} for baseline in rows}
print(json.dumps({'status': 'PILOT_VALIDATION_OK', 'results': 16,
                  'ado_relation_consensus': ado[0]['relation_sha256'],
                  'terminal_statuses': summary}, sort_keys=True))
PY
printf 'PILOT_VALIDATION_TERMINAL\n'
