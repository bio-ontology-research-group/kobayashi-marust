#!/bin/bash
#SBATCH --job-name=kon-14817-sxp-stats
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/konclude-sxp-stats-%j.out

set -euo pipefail

module load qt/5.15.5/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/14817_closure_20260714
binary=$root/Konclude-14817-satexp-stats-stripped
ontology=$km_root/corpus/ore_ont_14817.owl
run=$root/konclude-sat-exp-stats
mkdir -p "$run" "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 120 \
  /usr/bin/env KCLASSDBG=1 \
  "$binary" classification -w 1 -v \
    -i "$ontology" \
    -o "$run/14817.taxonomy.owl" \
    > "$run/14817.stdout" \
    2> "$run/14817.stderr"

/usr/bin/grep -E \
  'KCLASSDBG satisfiable (dispatch|callback).*class=http://purl.obolibrary.org/obo/(UBERON_0006535|NBO_0000042)$' \
  "$run/14817.stderr" || true
/usr/bin/grep -E \
  'Elapsed \(wall clock\)|Percent of CPU|Maximum resident set size' \
  "$run/14817.time" || true
echo "END date=$(date -Is)"
