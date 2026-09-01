#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=32G
#SBATCH --array=0-189%4
#SBATCH --job-name=km-paper-import-freeze
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/import-freeze-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
manifest=$root/obo-snapshot/obo-freeze-20260830.tsv
runtime=$root/runtimes/classifier-hermit.jar
classes=$root/runner-tools/profile-classes
sources=$root/obo-snapshot/sources
merged=$root/obo-snapshot/merged
receipts=$root/obo-snapshot/import-receipts
mkdir -p "$merged" "$receipts"
test -s "$manifest"
test -s "$runtime"
test -s "$classes/org/kmbenchmark/FreezeImports.class"

IFS=$'\t' read -r index id eligible status < <(
  awk -F '\t' -v n=$((SLURM_ARRAY_TASK_ID + 2)) \
    'NR == n {print $1 "\t" $2 "\t" $5 "\t" $6}' "$manifest"
)
test "$index" = "$SLURM_ARRAY_TASK_ID"
if test "$eligible" != true; then
  if test -s "$receipts/$id.tsv" && test "$(tail -n 1 "$receipts/$id.tsv")" = $'Z\tsource_unavailable'; then
    printf 'IMPORT_FREEZE_RESUME_OK\t%s\t%s\n' "$index" "$id"
    exit 0
  fi
  printf 'M\tschema\t1\nM\tid\t%s\nM\tstatus\t%s\nZ\tsource_unavailable\n' \
    "$id" "$status" > "$receipts/$id.tsv"
  exit 0
fi
test -s "$sources/$id.owl"
output=$merged/$id.ofn
receipt=$receipts/$id.tsv
if test -s "$output" && test -s "$receipt" && \
   test "$(tail -n 1 "$receipt")" = $'Z\tcomplete'; then
  expected=$(awk -F '\t' '$1 == "M" && $2 == "merged_sha256" {print $3}' "$receipt")
  normalization=$(awk -F '\t' '$1 == "M" && $2 == "normalization" {print $3}' "$receipt")
  if test -n "$expected" && \
     test "$normalization" = inverse-chain-members-to-defined-named-roles-v1 && \
     test "$expected" = "$(sha256sum "$output" | awk '{print $1}')"; then
    printf 'IMPORT_FREEZE_RESUME_OK\t%s\t%s\n' "$index" "$id"
    exit 0
  fi
fi
rm -f "$output" "$output.part" "$receipt" "$receipt.part"
attempt=1
while ! java -Xmx28g -cp "$classes:$runtime" org.kmbenchmark.FreezeImports \
  "$sources/$id.owl" "$output" "$receipt"; do
  if test "$attempt" -ge 3; then
    printf 'IMPORT_FREEZE_FAILED\t%s\t%s\t%s\n' "$index" "$id" "$attempt" >&2
    exit 1
  fi
  printf 'IMPORT_FREEZE_RETRY\t%s\t%s\t%s\n' "$index" "$id" "$attempt" >&2
  rm -f "$output" "$output.part" "$receipt" "$receipt.part"
  sleep $((attempt * 10))
  attempt=$((attempt + 1))
done
test -s "$output"
test -s "$receipt"
test "$(tail -n 1 "$receipt")" = $'Z\tcomplete'
test "$(awk -F '\t' '$1 == "M" && $2 == "merged_sha256" {print $3}' "$receipt")" = \
  "$(sha256sum "$output" | awk '{print $1}')"
test "$(awk -F '\t' '$1 == "M" && $2 == "normalization" {print $3}' "$receipt")" = \
  inverse-chain-members-to-defined-named-roles-v1
printf 'IMPORT_FREEZE_OK\t%s\t%s\n' "$index" "$id"
