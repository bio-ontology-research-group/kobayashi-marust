#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=32G
#SBATCH --job-name=km-paper-fma-prepare
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/fma-prepare-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
snapshot=$root/hard-cases
python3 "$root/validate_obo_one.py" "$root/hard-public-candidates.tsv" "$snapshot" --index 0
test "$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["status"])' "$snapshot/validation/fma.json")" = verified
mkdir -p "$snapshot/merged" "$snapshot/import-receipts"
java -Xmx28g -cp "$root/runner-tools/profile-classes:$root/runtimes/classifier-hermit.jar" \
  org.kmbenchmark.FreezeImports \
  "$snapshot/sources/fma.owl" "$snapshot/merged/fma.ofn" "$snapshot/import-receipts/fma.tsv"
test "$(tail -n 1 "$snapshot/import-receipts/fma.tsv")" = $'Z\tcomplete'
expected=$(awk -F '\t' '$1 == "M" && $2 == "merged_sha256" {print $3}' "$snapshot/import-receipts/fma.tsv")
test "$expected" = "$(sha256sum "$snapshot/merged/fma.ofn" | awk '{print $1}')"
test "$(awk -F '\t' '$1 == "M" && $2 == "normalization" {print $3}' "$snapshot/import-receipts/fma.tsv")" = \
  inverse-chain-members-to-defined-named-roles-v1
printf 'FMA_PREPARE_OK\t%s\n' "$expected"
