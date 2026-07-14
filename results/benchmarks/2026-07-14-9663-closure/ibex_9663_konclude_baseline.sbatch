#!/bin/bash
#SBATCH --job-name=kon-9663-base
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9663_closure_20260714/slurm/konclude-baseline-%j.out

set -euo pipefail

module load qt/5.15.5/gnu-12.2.0

root=/ibex/scratch/hohndor/km
out=$root/9663_closure_20260714/konclude-baseline
binary=$root/Konclude-official
ontology=$root/corpus/ore_ont_9663.owl

mkdir -p "$out" "$root/9663_closure_20260714/slurm"
export LD_LIBRARY_PATH="$root${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"
/usr/bin/time -v -o "$out/9663.time" \
  /usr/bin/timeout -k 5 240 \
  "$binary" classification -w 1 -v \
    -i "$ontology" \
    -o "$out/9663.taxonomy.owl" \
    > "$out/9663.stdout" \
    2> "$out/9663.stderr"

/usr/bin/grep -E \
  'Precomputation|Class classification|Classification time|Total time' \
  "$out/9663.stdout" || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Maximum resident set size' \
  "$out/9663.time" || true
echo "END date=$(date -Is)"
