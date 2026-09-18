#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=00:06:00
set -u
root=/ibex/scratch/hohndor/km/v143-harness-20260918
ontologies=(ore_ont_16371 ore_ont_16542)
ont=${ontologies[$SLURM_ARRAY_TASK_ID]}
out="$root/references-konclude-recovered/$ont"
mkdir -p "$out"
export LD_LIBRARY_PATH="/ibex/scratch/hohndor/km:${LD_LIBRARY_PATH:-}"
ulimit -v 20971520
sha256sum /ibex/scratch/hohndor/km/Konclude-official > "$out/binary.sha256"
/usr/bin/time -v -o "$out/time" timeout --kill-after=5s 240 /ibex/scratch/hohndor/km/Konclude-official classification -w 1 -i "$root/corpus/pool_sample/files/$ont.owl" -o "$out/taxonomy.owl" > "$out/stdout" 2> "$out/stderr"
echo "$?" > "$out/exit-code"
