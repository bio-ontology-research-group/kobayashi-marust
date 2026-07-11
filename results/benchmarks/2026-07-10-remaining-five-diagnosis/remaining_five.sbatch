#!/bin/bash
#SBATCH --job-name=km-rem5-diag
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:35:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=40G
#SBATCH --array=0-14%12
#SBATCH --output=/ibex/scratch/hohndor/km/rem5_diag_20260710/slurm-%A_%a.out

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/rem5_diag_20260710"
KON="$ROOT/Konclude-official"
CORPUS="$ROOT/corpus"
ONTS=(3215 7914 9663 9724 14817)
ARMS=(default no_sat_extract no_succ_ext)

ont=${ONTS[$((SLURM_ARRAY_TASK_ID % 5))]}
arm=${ARMS[$((SLURM_ARRAY_TASK_ID / 5))]}
input="$CORPUS/ore_ont_${ont}.owl"
prefix="$OUT/${arm}_${ont}"
config=()
case "$arm" in
  no_sat_extract) config=(-c "$OUT/konclude-no-saturation.xml") ;;
  no_succ_ext) config=(-c "$OUT/konclude-no-successor-extension.xml") ;;
esac

mkdir -p "$OUT"
export LD_LIBRARY_PATH="$ROOT${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

echo "BEGIN ont=$ont arm=$arm host=$(hostname) date=$(date -Is)"
/usr/bin/time -v -o "$prefix.time" \
  timeout 900 "$KON" classification -w 1 -v \
    "${config[@]}" -i "$input" -o "$prefix.owl" \
    >"$prefix.stdout" 2>"$prefix.stderr"
rc=$?
echo "END ont=$ont arm=$arm rc=$rc date=$(date -Is)"

grep -E 'Finished (precomputing|classifying)|Used .*satisfiable tests|Confirmed .*possible subsumer' "$prefix.stdout" \
  >"$prefix.key" || true
rm -f "$prefix.owl"
