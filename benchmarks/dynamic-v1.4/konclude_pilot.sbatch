#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:30:00
#SBATCH --job-name=konclude-dynamic-pilot
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
binary=/ibex/scratch/hohndor/km/Konclude-official
sha256sum "$binary" konclude_incremental.py /home/hohndor/bench/compat/libpcre.so.3 > konclude-runtime-hashes.txt
hostname > konclude-host.txt
lscpu >> konclude-host.txt
printf 'job=%s\n' "$SLURM_JOB_ID" >> konclude-host.txt
ldd "$binary" > konclude-linked-libraries.txt
for case in chains ado; do
  python3 konclude_incremental.py "$binary" "inputs/$case/states.txt" "results/$case/konclude/fresh" --reference "results/$case/hermit/fresh"
done
