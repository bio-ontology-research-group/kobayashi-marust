#!/bin/bash
#SBATCH --job-name=kon-14817-red-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/14817_closure_20260714/slurm/konclude-red-smoke-%j.out

set -u
module load qt/5.15.5/gnu-12.2.0

root=/ibex/scratch/hohndor/km/14817_closure_20260714
bundle=$root/Konclude-14817-redland-trace
run=$root/konclude-redland-smoke
mkdir -p "$run" "$root/slurm"
set +e
/usr/bin/time -v -o "$run/14817.time" \
  /usr/bin/timeout -k 5 240 \
  /usr/bin/env LD_LIBRARY_PATH="$bundle/redland-libs${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
    "$bundle/Konclude" classification -w 1 -v \
      -i /ibex/scratch/hohndor/km/corpus/ore_ont_14817.owl \
      -o "$run/14817.taxonomy.owl" \
      > "$run/14817.stdout" 2> "$run/14817.stderr"
status=$?
set -e
echo "RESULT exit=$status"
tail -n 20 "$run/14817.stdout" || true
/usr/bin/grep -E 'Elapsed \(wall clock\)|Maximum resident set size' "$run/14817.time" || true
