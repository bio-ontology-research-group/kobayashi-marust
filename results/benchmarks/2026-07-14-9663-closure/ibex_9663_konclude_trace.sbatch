#!/bin/bash
#SBATCH --job-name=kon-9663-trace
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9663_closure_20260714/slurm/konclude-trace-%j.out

set -euo pipefail

module load qt/5.15.5/gnu-12.2.0

root=/ibex/scratch/hohndor/km
out=$root/9663_closure_20260714/konclude-trace
binary=$root/Konclude-debug/Release/Konclude
ontology=$root/corpus/ore_ont_9663.owl

mkdir -p "$out" "$root/9663_closure_20260714/slurm"
export LD_LIBRARY_PATH="$root${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$sha256"

/usr/bin/time -v -o "$out/9663.time" \
  /usr/bin/timeout -k 5 240 \
  /usr/bin/env KCLASSDBG=1 \
  "$binary" classification -w 16 -v \
    -i "$ontology" \
    -o "$out/9663.taxonomy.owl" \
    > "$out/9663.stdout" \
    2> "$out/9663.stderr"

for pattern in \
  'KCLASSDBG saturation' \
  'KCLASSDBG satisfiable derived=true' \
  'KCLASSDBG satisfiable precheck=' \
  'KCLASSDBG satisfiable dispatch' \
  'KCLASSDBG satisfiable callback' \
  'KMDBG calculateSubsumption ENTRY'
do
  printf '%s\t' "$pattern"
  /usr/bin/grep -c "$pattern" "$out/9663.stderr" || true
done

/usr/bin/grep 'KCLASSDBG saturation' "$out/9663.stderr" \
  | /usr/bin/awk \
      '{for (i=1;i<=NF;i++) if ($i ~ /^(unsat|insufficient|incomplete|possible|derived)=/) c[$i]++} END {for (key in c) print key, c[key]}' \
  | /usr/bin/sort
/usr/bin/grep 'KSATDBG classify' "$out/9663.stderr" || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Maximum resident set size' \
  "$out/9663.time" || true
echo "END date=$(date -Is)"
