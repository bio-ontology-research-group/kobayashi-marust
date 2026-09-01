#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --job-name=km-ncbitaxon-sparse-fingerprint
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/km-ncbitaxon-sparse-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
script=$root/runner-tools/fingerprint_km_json_sparse.py
expected=337411472cc53677ee8e73b54335ac404c66e6043d74d3329d1688bdb3f550b6
test "$(sha256sum "$script" | awk '{print $1}')" = "$expected"
mkdir -p "$root/diagnostics/km-sparse-fingerprint"
/usr/bin/time -v -o "$root/diagnostics/km-sparse-fingerprint/ncbitaxon.time" \
  env PYTHONPATH=$root/runner-tools /usr/bin/python3 "$script" \
  --input "$root/current-results/km/ncbitaxon.taxonomy.json" \
  --source-ontology "$root/obo-snapshot/merged/ncbitaxon.ofn" \
  --output-prefix "$root/diagnostics/km-sparse-fingerprint/ncbitaxon" >/dev/null
test "$(/usr/bin/python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["status"])' \
  "$root/diagnostics/km-sparse-fingerprint/ncbitaxon.json")" = ok
printf 'KMBIG_SPARSE_OK\tncbitaxon\n'
