#!/bin/bash
#SBATCH --job-name=kon-rem5-extract
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:18:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=40G
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/rem5_diag_20260710/extract-slurm-%A_%a.out

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/rem5_diag_20260710"
KON="$ROOT/Konclude-official"
ONTS=(3215 14817)

ont=${ONTS[$SLURM_ARRAY_TASK_ID]}
input="$ROOT/corpus/ore_ont_${ont}.owl"
prefix="$OUT/no_test_extract_${ont}"

mkdir -p "$OUT"
export LD_LIBRARY_PATH="$ROOT${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
echo "BEGIN ont=$ont host=$(hostname) date=$(date -Is)"
/usr/bin/time -v -o "$prefix.time" \
  timeout 900 "$KON" classification -w 1 -v \
    -c "$OUT/konclude-no-test-extraction.xml" \
    -i "$input" -o "$prefix.owl" \
    >"$prefix.stdout" 2>"$prefix.stderr"
rc=$?
echo "END ont=$ont rc=$rc date=$(date -Is)"
rm -f "$prefix.owl"
