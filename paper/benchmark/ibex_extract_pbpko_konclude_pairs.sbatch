#!/bin/bash
# Materialize Konclude's closed PBPKO relation and compare it with JFact.
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --job-name=km-paper-pbpko-diff
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/pbpko-diff-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
results=$root/current-results
out=$root/diagnostics/pbpko-final-diff
mkdir -p "$out"

/usr/bin/python3 "$root/runner-tools/fingerprint_km_json_sparse.py" \
  --input "$results/konclude/pbpko.taxonomy.owlxml" \
  --format owlxml \
  --source-ontology "$root/obo-snapshot/merged/pbpko.ofn" \
  --output-prefix "$out/konclude" \
  --pairs-output "$out/konclude.taxonomy.tsv" \
  > "$out/konclude.fingerprint.json"

/usr/bin/python3 "$root/runner-tools/compare_taxonomy_tsv.py" \
  --left "$results/jfact/pbpko.taxonomy.tsv" \
  --right "$out/konclude.taxonomy.tsv" \
  --left-label jfact --right-label konclude --sample-limit 25 \
  --output "$out/jfact-vs-konclude.json"

test "$(/usr/bin/wc -l < "$out/konclude.taxonomy.tsv")" -eq 7568
test -s "$out/jfact-vs-konclude.json"
/usr/bin/sha256sum "$out/konclude.taxonomy.tsv" \
  "$out/konclude.fingerprint.json" "$out/jfact-vs-konclude.json" \
  > "$out/SHA256SUMS"
echo "PBPKO_FINAL_DIFF_OK"
