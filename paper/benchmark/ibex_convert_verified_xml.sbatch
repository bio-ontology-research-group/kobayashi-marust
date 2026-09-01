#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=36G
#SBATCH --array=0-188%8
#SBATCH --job-name=km-paper-verified-xml
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/verified-xml-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
manifest=$root/obo-snapshot/obo-freeze-20260830.tsv
position=$((SLURM_ARRAY_TASK_ID + 1))
ontology_id=$(awk -F '\t' '$5 == "true" {n++; if (n == wanted) {print $2; exit}}' \
  wanted="$position" "$manifest")
test -n "$ontology_id"
source=$root/obo-snapshot/merged/$ontology_id.ofn
output=$root/obo-snapshot/verified-xml/$ontology_id.xml
receipt=$root/obo-snapshot/verified-xml-receipts/$ontology_id.tsv
converter=$root/convert-syntax.jar
owlapi=$root/runtimes/classifier-hermit.jar
expected_converter=aa938444d680c783cff9a50a35ddd9ec19510755cdd25aacaf7b7f08df16e1ed
test "$(sha256sum "$converter" | awk '{print $1}')" = "$expected_converter"
test "$(sha256sum "$owlapi" | awk '{print $1}')" = \
  59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c

source_digest=$(sha256sum "$source" | awk '{print $1}')
if test -s "$output" && test -s "$receipt" \
    && test "$(tail -n 1 "$receipt")" = $'Z\tcomplete' \
    && test "$(awk -F '\t' '$2 == "source_sha256" {print $3}' "$receipt")" = "$source_digest" \
    && test "$(awk -F '\t' '$2 == "output_sha256" {print $3}' "$receipt")" = \
            "$(sha256sum "$output" | awk '{print $1}')" \
    && test "$(awk -F '\t' '$2 == "conversion" {print $3}' "$receipt")" = konclude-compatible-serialization-v2 \
    && test "$(awk -F '\t' '$2 == "converter_sha256" {print $3}' "$receipt")" = "$expected_converter" \
    && test "$(awk -F '\t' '$2 == "roundtrip_logical_axioms_equal" {print $3}' "$receipt")" = true \
    && test "$(awk -F '\t' '$2 == "roundtrip_signature_equal" {print $3}' "$receipt")" = true; then
  printf 'VERIFIED_XML_RESUME_OK\t%s\n' "$ontology_id"
  exit 0
fi

mkdir -p "$(dirname "$output")" "$(dirname "$receipt")"
if ! java -Xmx30g -Dkm.converter.sha256="$expected_converter" -cp "$converter:$owlapi" org.kmbenchmark.ConvertSyntax \
    "$source" "$output" "$receipt" owlxml; then
  java -Xmx30g -Dkm.converter.sha256="$expected_converter" -cp "$converter:$owlapi" org.kmbenchmark.ConvertSyntax \
    "$source" "$output" "$receipt" functional
fi
test "$(tail -n 1 "$receipt")" = $'Z\tcomplete'
printf 'VERIFIED_XML_TERMINAL\t%s\t%s\n' "$ontology_id" \
  "$(awk -F '\t' '$2 == "serialization" {print $3}' "$receipt")"
