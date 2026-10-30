#!/bin/bash
# usage: ore_one.sh KM_BIN OUTDIR TAG TIMEOUT NAME   (env ORE_KEEP: extra KM_ settings)
km=$1; outdir=$2; tag=$3; to=$4; n=$5
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
mkdir -p "$outdir/out-$tag"
export TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-coverage/tmp
s=$(date +%s.%N)
env $(env | grep -o '^KM_[A-Z_0-9]*' | sed 's/^/-u /') KM_TIMING=1 $ORE_KEEP timeout -s KILL $to setsid -w "$km" classify --lines "$C/$n.owl" \
  > "$outdir/out-$tag/$n.out" 2> "$outdir/out-$tag/$n.err"
rc=$?; e=$(date +%s.%N)
route=$(grep -o 'route=[a-z_]*' "$outdir/out-$tag/$n.err" | tail -1 | cut -d= -f2)
rel=$(grep -c 'nominal CB input: released' "$outdir/out-$tag/$n.err")
grep -E '^(SUB|UNSAT|CONSISTENT)' "$outdir/out-$tag/$n.out" | sort | gzip > "$outdir/out-$tag/$n.sig.gz"
rm -f "$outdir/out-$tag/$n.out"; tail -c 3000 "$outdir/out-$tag/$n.err" > "$outdir/out-$tag/$n.errtail"; rm -f "$outdir/out-$tag/$n.err"
echo -e "$n\t$tag\t$rc\t$(echo "$e - $s" | bc)\t$route\t$rel" >> "$outdir/times-$tag.tsv"
