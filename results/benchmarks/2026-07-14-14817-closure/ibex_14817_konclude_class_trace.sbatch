#!/bin/bash
#SBATCH --job-name=kon-14817-class
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/konclude-class-%j.out

set -euo pipefail

module load qt/5.15.5/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
binary=$km_root/9724_closure_20260714/Konclude-9724-debug-native/Release/Konclude
ontology=$km_root/corpus/ore_ont_14817.owl
run=$root/konclude-class
mkdir -p "$run" "$root/slurm"

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 240 \
  /usr/bin/env KCLASSDBG=1 \
  "$binary" classification -w 1 -v \
    -i "$ontology" \
    -o "$run/14817.taxonomy.owl" \
    > "$run/14817.stdout" \
    2> "$run/14817.stderr"

/usr/bin/grep -E 'NBO_0000042|NBO_0000774|NBO_0000040|NBO_0000771' \
  "$run/14817.stderr" || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Percent of CPU|Maximum resident set size' \
  "$run/14817.time" || true
echo "END date=$(date -Is)"
