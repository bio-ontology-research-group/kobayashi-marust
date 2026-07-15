#!/bin/bash
#SBATCH --job-name=kon-14817-u11342-sxp
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/konclude-u11342-sxp-%j.out

set -u

module load qt/5.15.5/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
binary=$km_root/9724_closure_20260714/Konclude-9724-debug-native/Release/Konclude
ontology=$km_root/corpus/ore_ont_14817.owl
config=$root/konclude-no-completion-saturation-caching.xml
run=$root/konclude-uberon0011342-satexp-trace
mkdir -p "$run" "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
set +e
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 210 \
  /usr/bin/env KCOMPDBG=UBERON_0011342 KCLASSDBG=1 \
  "$binary" classification -w 1 -v \
    -c "$config" \
    -i "$ontology" \
    -o "$run/14817.taxonomy.owl" \
    > "$run/14817.stdout" \
    2> "$run/14817.stderr"
status=$?
set -e

echo "RESULT exit=$status"
for key in activate root-saturation root-initialized task-fixpoint successor-expansion-begin successor-expansion-end cache-establish some-attempt some-result; do
  printf '%s=' "$key"
  /usr/bin/grep -c "KCOMP.*$key" "$run/14817.stderr" || true
done
/usr/bin/grep -E 'KCOMPDBG (activate|task-fixpoint)|UBERON_0011342' "$run/14817.stderr" | tail -n 30 || true
/usr/bin/grep -E 'Elapsed \(wall clock\)|Maximum resident set size' "$run/14817.time" || true
echo "END date=$(date -Is)"
