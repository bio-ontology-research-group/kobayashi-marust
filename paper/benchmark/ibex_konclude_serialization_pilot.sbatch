#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --exclusive
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/konclude-serialization-pilot-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
konclude_root=/ibex/scratch/hohndor/km/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
binary=$konclude_root/Konclude-build-a
export LD_LIBRARY_PATH="$konclude_root/runtime-lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
out=$root/konclude-serialization-pilot
mkdir -p "$out"

declare -A expected=(
  [bspo]=8eeb99d77f74dcc9e9356933542b51ff62f6ca1a14a6ceed916bb5038d0c8b84
  [cdno]=0d95dbe3331cd87a7db62a452db115c0049c34282e808aed940668ec204b4c83
  [cvdo]=889545ecee413983afe9766b41c7067ec4a8d32454597d8b0f6e122fcba72527
  [htn]=28cd9f4347dc8a9677b9a7f5690c1b8ab90560e443933b72987bc6bf7a25683e
)

for ontology in bspo cdno cvdo htn; do
  input=$root/obo-snapshot/verified-xml/$ontology.xml
  receipt=$root/obo-snapshot/verified-xml-receipts/$ontology.tsv
  source=$root/obo-snapshot/merged/$ontology.ofn
  test "$(tail -n 1 "$receipt")" = $'Z\tcomplete'
  test "$(awk -F '\t' '$2 == "conversion" {print $3}' "$receipt")" = \
    konclude-compatible-serialization-v2
  test "$(awk -F '\t' '$2 == "source_sha256" {print $3}' "$receipt")" = \
    "$(sha256sum "$source" | awk '{print $1}')"
  test "$(awk -F '\t' '$2 == "output_sha256" {print $3}' "$receipt")" = \
    "$(sha256sum "$input" | awk '{print $1}')"

  printf 'BEGIN\t%s\t%s\n' "$ontology" \
    "$(awk -F '\t' '$2 == "serialization" {print $3}' "$receipt")"
  "$binary" classification -w 16 -v -i "$input" -o "$out/$ontology.owlxml"
  python3 "$root/runner-tools/full_iri_fingerprint.py" \
    --input "$out/$ontology.owlxml" --format owlxml \
    --source-ontology "$source" \
    --output-prefix "$out/$ontology.fingerprint" > "$out/$ontology.fingerprint.stdout.json"
  python3 - "$out/$ontology.fingerprint.json" "${expected[$ontology]}" <<'PY'
import json
import sys

record = json.load(open(sys.argv[1], encoding="utf-8"))
assert record["missing_source_declarations"] == 0, record
assert record["relation_sha256"] == sys.argv[2], record
PY
  printf 'END\t%s\t%s\n' "$ontology" "$(stat -c %s "$out/$ontology.owlxml")"
done

printf 'KONCLUDE_SERIALIZATION_PILOT_OK\t4\n'
