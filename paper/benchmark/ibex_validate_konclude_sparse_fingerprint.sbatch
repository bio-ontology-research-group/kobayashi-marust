#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --array=0-188%8
#SBATCH --job-name=konclude-sparse-fingerprint-diff
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/konclude-sparse-fingerprint-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
manifest=$root/obo-snapshot/obo-freeze-20260830.tsv
script=$root/runner-tools/fingerprint_km_json_sparse.py.next
expected=287c240260deac31d047c63893c7565cbd0a27b50c5e454bc4b82dc77fea6bb7
test "$(sha256sum "$script" | awk '{print $1}')" = "$expected"
ontology_id=$(awk -F '\t' '$5 == "true" {n++; if (n == wanted) {print $2; exit}}' \
  wanted=$((SLURM_ARRAY_TASK_ID + 1)) "$manifest")
test -n "$ontology_id"
result=$root/current-results/konclude/$ontology_id.result.json
old=$root/current-results/konclude/$ontology_id.fingerprint.json
if ! /usr/bin/python3 - "$result" "$old" <<'PY'
import json, pathlib, sys
result, old = map(pathlib.Path, sys.argv[1:])
if not result.is_file() or not old.is_file(): raise SystemExit(1)
r=json.load(result.open()); f=json.load(old.open())
if r.get("slurm_array_job_id") != "51028377" or r.get("status") != "ok": raise SystemExit(1)
if f.get("status") != "ok": raise SystemExit(1)
PY
then
  printf 'KONCLUDE_SPARSE_DIFF_SKIP\t%s\n' "$ontology_id"
  exit 0
fi
input=$root/current-results/konclude/$ontology_id.taxonomy.owlxml
source=$root/obo-snapshot/merged/$ontology_id.ofn
prefix=$root/diagnostics/konclude-sparse-fingerprint/$ontology_id
mkdir -p "$(dirname "$prefix")"
PYTHONPATH=$root/runner-tools /usr/bin/python3 "$script" \
  --input "$input" --format owlxml --source-ontology "$source" \
  --output-prefix "$prefix" >/dev/null
/usr/bin/python3 - "$old" "$prefix.json" <<'PY'
import json,sys
a,b=(json.load(open(path)) for path in sys.argv[1:])
fields=("consistent","subsumptions","unsatisfiable","nonempty_lefts",
        "taxonomy_sha256","relation_sha256","input_sha256","source_edges",
        "source_equivalence_groups","source_declarations","output_declarations",
        "ontology_declarations","missing_source_declarations")
different={field:(a.get(field),b.get(field)) for field in fields if a.get(field)!=b.get(field)}
if different: raise SystemExit("fingerprint mismatch: "+repr(different))
PY
printf 'KONCLUDE_SPARSE_DIFF_OK\t%s\n' "$ontology_id"
