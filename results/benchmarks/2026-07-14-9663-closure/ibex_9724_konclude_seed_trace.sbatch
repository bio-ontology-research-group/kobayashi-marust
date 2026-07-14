#!/bin/bash
#SBATCH --job-name=kon-9724-seeds
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9663_closure_20260714/slurm/konclude-9724-seeds-%j.out

set -euo pipefail

module load qt/5.15.5/gnu-12.2.0

root=/ibex/scratch/hohndor/km
out=$root/9663_closure_20260714/konclude-9724-seeds
binary=$root/Konclude-debug/Release/Konclude
ontology=$root/corpus/ore_ont_9724.owl

mkdir -p "$out" "$root/9663_closure_20260714/slurm"
export LD_LIBRARY_PATH="$root${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

/usr/bin/time -v -o "$out/9724.time" \
  /usr/bin/timeout -k 5 240 \
  /usr/bin/env KSEEDDBG=1 \
  "$binary" classification -w 16 -v \
    -i "$ontology" \
    -o "$out/9724.taxonomy.owl" \
    > "$out/9724.stdout" \
    2> "$out/9724.stderr"

/usr/bin/grep 'KSEEDDBG' "$out/9724.stderr" || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Maximum resident set size' \
  "$out/9724.time" || true
echo "END date=$(date -Is)"
