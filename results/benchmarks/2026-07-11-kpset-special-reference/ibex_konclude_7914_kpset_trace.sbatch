#!/bin/bash
#SBATCH --job-name=konclude-7914-kpset
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=32G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/konclude-7914-kpset-%j.out

set -euo pipefail
module load qt/5.15.5/gnu-12.2.0

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KON="$ROOT/Konclude-debug/Release/Konclude"
INPUT="$ROOT/corpus/ore_ont_7914.owl"
PREFIX="$OUT/konclude-7914-kpset-${SLURM_JOB_ID}"

rm -f "$PREFIX.tax" "$PREFIX.stderr" "$PREFIX.time" "$PREFIX.counts"
echo "BEGIN host=$(hostname) date=$(date -Is) sha256=$(sha256sum "$KON" | cut -d' ' -f1)"
/usr/bin/time -v -o "$PREFIX.time" \
  timeout 600 env KCOMMONDBG=UBERON_0008922,UBERON_0008923,UBERON_0008926 KBRANCHDBG=1 KCOMPDBG=${KCOMPDBG:-UBERON_0009732} KSATSTATUSDBG=${KSATSTATUSDBG:-UBERON_0009732} "$KON" classification -i "$INPUT" -o "$PREFIX.tax" \
  > /dev/null 2> "$PREFIX.stderr"

for decision in 'satisfiable derived=true' 'satisfiable precheck=' 'satisfiable dispatch'; do
  printf '%s\t' "$decision"
  grep -c "KCLASSDBG $decision" "$PREFIX.stderr" || true
done | tee "$PREFIX.counts"
grep 'KCLASSDBG saturation ' "$PREFIX.stderr" \
  | awk '{for (i=1;i<=NF;i++) if ($i ~ /^(unsat|insufficient|incomplete|derived)=/) c[$i]++} END {for (k in c) print k, c[k]}' \
  | sort
grep '^KSATSTATUS' "$PREFIX.stderr" || true
grep '^KCOMPDBG' "$PREFIX.stderr" || true
grep '^KCOMMONDBG' "$PREFIX.stderr" || true
echo "END date=$(date -Is)"
