#!/bin/bash
#SBATCH --job-name=kon-14817-cache-ab
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --array=0-2
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/konclude-cache-ab-%A_%a.out

set -u

module load qt/5.15.5/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
binary=$km_root/9724_closure_20260714/Konclude-9724-debug-native/Release/Konclude
ontology=$km_root/corpus/ore_ont_14817.owl
case "$SLURM_ARRAY_TASK_ID" in
  0) variant=no-sat-expander-cache; config=$root/konclude-no-sat-expander-cache.xml ;;
  1) variant=no-completion-saturation-expansion; config=$root/konclude-no-completion-saturation-expansion.xml ;;
  2) variant=no-completion-saturation-caching; config=$root/konclude-no-completion-saturation-caching.xml ;;
esac
run=$root/konclude-cache-ab/$variant
mkdir -p "$run" "$root/slurm"

echo "BEGIN variant=$variant host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
set +e
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 240 \
  "$binary" classification -w 1 -v \
    -c "$config" \
    -i "$ontology" \
    -o "$run/14817.taxonomy.owl" \
    > "$run/14817.stdout" \
    2> "$run/14817.stderr"
status=$?
set -e

echo "RESULT variant=$variant exit=$status"
/usr/bin/grep -E 'Finished (precomputing|class classification)|Total processing time' \
  "$run/14817.stdout" || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Percent of CPU|Maximum resident set size' \
  "$run/14817.time" || true
echo "END date=$(date -Is)"
