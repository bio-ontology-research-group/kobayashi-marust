#!/bin/bash
#SBATCH --job-name=kon-14817-u14672
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/konclude-u14672-%j.out

set -u

module load qt/5.15.5/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
bundle=$root/Konclude-14817-redland-trace
binary=$bundle/Konclude
ontology=$km_root/corpus/ore_ont_14817.owl
run=$root/konclude-uberon0014672-completion-trace
mkdir -p "$run" "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
set +e
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 240 \
  /usr/bin/env \
    LD_LIBRARY_PATH="$bundle/redland-libs${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
    KCOMPDBG=UBERON_0014672 \
    KCLASSDBG=1 \
    "$binary" classification -w 1 -v \
      -i "$ontology" \
      -o "$run/14817.taxonomy.owl" \
      > "$run/14817.stdout" \
      2> "$run/14817.stderr"
status=$?
set -e

echo "RESULT exit=$status"
for key in activate inherit handle-exit task-fixpoint root-saturation root-initialized cache-establish successor-expansion-begin successor-expansion-end satexp-detect satexp-lookup satexp-compatible-hit satexp-incompatible-hit satexp-ancestor-hit satexp-write-expansion or-trigger-install or-trigger-reinstall or-delay-queue or-delay-requeue or-task-fork or-child; do
  printf '%s=' "$key"
  /usr/bin/grep -c "KCOMPDBG $key" "$run/14817.stderr" || true
done
/usr/bin/grep -E 'KCOMPDBG|KCLASSDBG.*UBERON_0014672' "$run/14817.stderr" | head -n 1200 || true
/usr/bin/grep -E 'Elapsed \(wall clock\)|Maximum resident set size' "$run/14817.time" || true
echo "END date=$(date -Is)"
