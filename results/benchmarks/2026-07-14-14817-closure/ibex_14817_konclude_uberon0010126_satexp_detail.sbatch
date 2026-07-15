#!/bin/bash
#SBATCH --job-name=kon-14817-u10126-detail
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/konclude-u10126-detail-%j.out

set -u

module load qt/5.15.5/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
binary=$root/Konclude-14817-satexp-detail
ontology=$km_root/corpus/ore_ont_14817.owl
config=$root/konclude-no-completion-saturation-caching.xml
run=$root/konclude-uberon0010126-satexp-detail
mkdir -p "$run" "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
set +e
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 210 \
  /usr/bin/env KCOMPDBG=UBERON_0010126 KCLASSDBG=1 \
  "$binary" classification -w 1 -v \
    -c "$config" \
    -i "$ontology" \
    -o "$run/14817.taxonomy.owl" \
    > "$run/14817.stdout" \
    2> "$run/14817.stderr"
status=$?
set -e

echo "RESULT exit=$status"
for key in activate handle-exit task-fixpoint satexp-detect satexp-lookup satexp-compatible-hit satexp-incompatible-hit satexp-ancestor-hit satexp-write-expansion; do
  printf '%s=' "$key"
  /usr/bin/grep -c "KCOMPDBG $key" "$run/14817.stderr" || true
done
/usr/bin/grep -E 'KCOMPDBG (activate|handle-exit|task-fixpoint|satexp-(detect|lookup|compatible-hit|incompatible-hit|ancestor-hit|write-expansion))' "$run/14817.stderr" | head -n 320 || true
/usr/bin/grep -E 'Elapsed \(wall clock\)|Maximum resident set size' "$run/14817.time" || true
echo "END date=$(date -Is)"
