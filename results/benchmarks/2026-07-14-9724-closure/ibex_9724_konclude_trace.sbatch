#!/bin/bash
#SBATCH --job-name=kon-9724-trace
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/konclude-trace-%j.out

set -euo pipefail

module load qt/5.15.5/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
binary=$root/Konclude-9724-debug-native/Release/Konclude
ontology=$km_root/corpus/ore_ont_9724.owl
run=$root/konclude-trace
mkdir -p "$run" "$root/slurm"

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

/usr/bin/time -v -o "$run/9724.time" \
  /usr/bin/timeout -k 5 240 \
  /usr/bin/env KSEEDDBG=1 KSATDBG=1 \
  "$binary" classification -w 16 -v \
    -i "$ontology" \
    -o "$run/9724.taxonomy.owl" \
    > "$run/9724.stdout" \
    2> "$run/9724.stderr"

/usr/bin/grep -E 'KSEEDDBG|KSATDBG' "$run/9724.stderr" || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Maximum resident set size' \
  "$run/9724.time" || true
echo "END date=$(date -Is)"
