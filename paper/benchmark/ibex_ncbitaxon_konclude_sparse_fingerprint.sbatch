#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --job-name=konclude-ncbitaxon-sparse-fingerprint
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/konclude-ncbitaxon-sparse-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
script=$root/runner-tools/fingerprint_km_json_sparse.py.next
expected=287c240260deac31d047c63893c7565cbd0a27b50c5e454bc4b82dc77fea6bb7
test "$(sha256sum "$script" | awk '{print $1}')" = "$expected"
mkdir -p "$root/diagnostics/konclude-sparse-fingerprint"
/usr/bin/time -v -o "$root/diagnostics/konclude-sparse-fingerprint/ncbitaxon.time" \
  env PYTHONPATH=$root/runner-tools /usr/bin/python3 "$script" \
  --input "$root/current-results/konclude/ncbitaxon.taxonomy.owlxml" \
  --format owlxml \
  --source-ontology "$root/obo-snapshot/merged/ncbitaxon.ofn" \
  --output-prefix "$root/diagnostics/konclude-sparse-fingerprint/ncbitaxon" >/dev/null
test "$(/usr/bin/python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["status"])' \
  "$root/diagnostics/konclude-sparse-fingerprint/ncbitaxon.json")" = ok
printf 'KONCLUDE_BIG_SPARSE_OK\tncbitaxon\n'
