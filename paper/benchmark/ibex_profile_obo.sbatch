#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=32G
#SBATCH --array=0-189%4
#SBATCH --job-name=km-paper-obo-profile
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/obo-profile-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
manifest=$root/obo-snapshot/obo-freeze-20260830.tsv
runtime=$root/runtimes/classifier-hermit.jar
classes=$root/runner-tools/profile-classes
merged=$root/obo-snapshot/merged
profiles=$root/obo-snapshot/profiles
receipts=$root/obo-snapshot/import-receipts
mkdir -p "$profiles"
test -s "$manifest"
test -s "$runtime"
test -s "$classes/org/kmbenchmark/ProfileOntology.class"

IFS=$'\t' read -r index id eligible status < <(
  awk -F '\t' -v n=$((SLURM_ARRAY_TASK_ID + 2)) \
    'NR == n {print $1 "\t" $2 "\t" $5 "\t" $6}' "$manifest"
)
test "$index" = "$SLURM_ARRAY_TASK_ID"
output=$profiles/$id.tsv
if test "$eligible" != true; then
  if test -s "$output" && test "$(tail -n 1 "$output")" = $'Z\tsource_unavailable'; then
    printf 'PROFILE_RESUME_OK\t%s\t%s\n' "$index" "$id"
    exit 0
  fi
  printf 'M\tschema\t1\nM\tid\t%s\nM\tstatus\t%s\nZ\tsource_unavailable\n' \
    "$id" "$status" > "$output"
  exit 0
fi

ontology=$merged/$id.ofn
receipt=$receipts/$id.tsv
test -s "$ontology"
test -s "$receipt"
test "$(tail -n 1 "$receipt")" = $'Z\tcomplete'
expected=$(awk -F '\t' '$1 == "M" && $2 == "merged_sha256" {print $3}' "$receipt")
test -n "$expected"
if test -s "$output" && test "$(tail -n 1 "$output")" = $'Z\tcomplete'; then
  recorded=$(awk -F '\t' '$1 == "M" && $2 == "source_sha256" {print $3}' "$output")
  if test "$recorded" = "$expected"; then
    printf 'PROFILE_RESUME_OK\t%s\t%s\n' "$index" "$id"
    exit 0
  fi
fi

java -Xmx28g -cp "$classes:$runtime" org.kmbenchmark.ProfileOntology \
  "$ontology" "$output"
test -s "$output"
test "$(tail -n 1 "$output")" = $'Z\tcomplete'
test "$(awk -F '\t' '$1 == "M" && $2 == "source_sha256" {print $3}' "$output")" = "$expected"
test "$(awk -F '\t' '$1 == "P" {n++} END {print n+0}' "$output")" = 5
printf 'PROFILE_OK\t%s\t%s\n' "$index" "$id"
