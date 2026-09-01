#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=32G
#SBATCH --job-name=km-paper-fma-profile
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/fma-profile-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
ontology=$root/hard-cases/merged/fma.ofn
receipt=$root/hard-cases/import-receipts/fma.tsv
output=$root/hard-cases/profiles/fma.tsv
mkdir -p "$(dirname "$output")"
test -s "$ontology"
expected=$(awk -F '\t' '$1 == "M" && $2 == "merged_sha256" {print $3}' "$receipt")
test -n "$expected"
java -Xmx28g -cp "$root/runner-tools/profile-classes:$root/runtimes/classifier-hermit.jar" \
  org.kmbenchmark.ProfileOntology "$ontology" "$output"
test "$(tail -n 1 "$output")" = $'Z\tcomplete'
test "$(awk -F '\t' '$1 == "M" && $2 == "source_sha256" {print $3}' "$output")" = "$expected"
printf 'FMA_PROFILE_OK\t%s\n' "$expected"
