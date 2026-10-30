#!/bin/bash
# Sequential timing of the gated ORE inputs, one process at a time.
# usage: ore_time.sh KM_BIN LIST OUTDIR TAG [ENV=VALUE ...]
# Writes OUTDIR/times-TAG.tsv (file, tag, rc, seconds, route) and keeps the
# SUB/UNSAT/CONSISTENT lines of every run, gzipped, in OUTDIR/out-TAG/.
km=$1; list=$2; outdir=$3; tag=$4; shift 4
mkdir -p "$outdir/out-$tag"
while read -r p; do
  n=$(basename "$p" .owl)
  s=$(date +%s.%N)
  env $(env | grep -o '^KM_[A-Z_]*' | sed 's/^/-u /') KM_TIMING=1 "$@" timeout 300 "$km" classify --lines "$p" \
    > "$outdir/out-$tag/$n.out" 2> "$outdir/out-$tag/$n.err"
  rc=$?; e=$(date +%s.%N)
  route=$(grep -o 'route=[a-z_]*' "$outdir/out-$tag/$n.err" | head -1 | cut -d= -f2)
  grep -E '^(SUB|UNSAT|CONSISTENT)' "$outdir/out-$tag/$n.out" | sort | gzip > "$outdir/out-$tag/$n.sig.gz"
  rm -f "$outdir/out-$tag/$n.out"; tail -c 4000 "$outdir/out-$tag/$n.err" > "$outdir/out-$tag/$n.errtail"; rm -f "$outdir/out-$tag/$n.err"
  echo -e "$n\t$tag\t$rc\t$(echo "$e - $s" | bc)\t$route" >> "$outdir/times-$tag.tsv"
done < "$list"
echo DONE >> "$outdir/times-$tag.tsv"
