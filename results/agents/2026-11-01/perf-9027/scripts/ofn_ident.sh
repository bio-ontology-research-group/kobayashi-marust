#!/bin/bash
# ofn_ident.sh OLD NEW LIST OUTDIR CPU: byte-compare `km ofn` (nominal mode) clause and meta output.
OLD=$1; NEW=$2; LIST=$3; OUT=$4; CPU=$5
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
mkdir -p $OUT
export KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_NOMINALS=1
while read n; do
  f=$C/$n.owl; [ -f $f ] || continue
  timeout -s KILL 120 taskset -c $CPU $OLD ofn $f --meta $OUT/o.meta > $OUT/o.json 2>/dev/null; ro=$?
  timeout -s KILL 120 taskset -c $CPU $NEW ofn $f --meta $OUT/n.meta > $OUT/n.json 2>/dev/null; rn=$?
  if [ $ro -ne 0 ] || [ $rn -ne 0 ]; then echo "$n rc $ro $rn"; continue; fi
  if cmp -s $OUT/o.json $OUT/n.json && cmp -s $OUT/o.meta $OUT/n.meta; then echo "$n same $(stat -c %s $OUT/n.json)"; else echo "$n DIFF"; fi
done < $LIST
