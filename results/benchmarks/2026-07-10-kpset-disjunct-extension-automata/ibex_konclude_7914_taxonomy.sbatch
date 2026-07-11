#!/bin/bash
#SBATCH --job-name=kon-7914-tax
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=40G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_disj_ext_auto_20260710/konclude-7914-taxonomy.slurm

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_disj_ext_auto_20260710"
mkdir -p "$OUT"
export LD_LIBRARY_PATH="$ROOT${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

/usr/bin/time -v -o "$OUT/konclude-7914-taxonomy.time" \
  timeout 480 "$ROOT/Konclude-official" classification -w 1 -v \
    -i "$ROOT/corpus/ore_ont_7914.owl" \
    -o "$OUT/konclude-7914-taxonomy.owl" \
    >"$OUT/konclude-7914-taxonomy.stdout" \
    2>"$OUT/konclude-7914-taxonomy.stderr"
rc=$?
printf 'rc=%s\n' "$rc"
exit "$rc"
