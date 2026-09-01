#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --array=0-188%8
#SBATCH --job-name=km-sparse-fingerprint-diff
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/km-sparse-fingerprint-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
manifest=$root/obo-snapshot/obo-freeze-20260830.tsv
ontology_id=$(awk -F '\t' '$5 == "true" {n++; if (n == wanted) {print $2; exit}}' \
  wanted=$((SLURM_ARRAY_TASK_ID + 1)) "$manifest")
test -n "$ontology_id"
result=$root/current-results/km/$ontology_id.result.json
old=$root/current-results/km/$ontology_id.fingerprint.json
if ! /usr/bin/python3 - "$result" "$old" <<'PY'
import json, pathlib, sys
result, old = map(pathlib.Path, sys.argv[1:])
if not result.is_file() or not old.is_file(): raise SystemExit(1)
r=json.load(result.open()); f=json.load(old.open())
if r.get("slurm_array_job_id") != "51028377" or r.get("status") != "ok": raise SystemExit(1)
if f.get("status") != "ok": raise SystemExit(1)
PY
then
  printf 'KM_SPARSE_DIFF_SKIP\t%s\n' "$ontology_id"
  exit 0
fi
input=$root/current-results/km/$ontology_id.taxonomy.json
source=$root/obo-snapshot/merged/$ontology_id.ofn
prefix=$root/diagnostics/km-sparse-fingerprint/$ontology_id
mkdir -p "$(dirname "$prefix")"
PYTHONPATH=$root/runner-tools /usr/bin/python3 \
  $root/runner-tools/fingerprint_km_json_sparse.py \
  --input "$input" --source-ontology "$source" --output-prefix "$prefix" >/dev/null
/usr/bin/python3 - "$old" "$prefix.json" <<'PY'
import json,sys
a,b=(json.load(open(path)) for path in sys.argv[1:])
fields=("consistent","subsumptions","unsatisfiable","nonempty_lefts",
        "taxonomy_sha256","relation_sha256","input_sha256")
different={field:(a.get(field),b.get(field)) for field in fields if a.get(field)!=b.get(field)}
if different: raise SystemExit("fingerprint mismatch: "+repr(different))
PY
printf 'KM_SPARSE_DIFF_OK\t%s\n' "$ontology_id"
