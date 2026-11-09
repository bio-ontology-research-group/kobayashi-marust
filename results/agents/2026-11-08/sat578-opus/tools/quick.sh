#!/bin/bash
# quick.sh BIN TAG EXTRA: nine fixtures (both routes) and the flipped rows, one run.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus
BIN=$1; TAG=$2; EXTRA=$3; cd $S; mkdir -p quick
rm -f quick/fx-$TAG.tsv quick/flips-$TAG.tsv
TMPDIR=$S/tmp FAM_THREADS=2 FAM_TIMEOUT=60 FAM_FORCED_TIMEOUT=60 FAM_EXTRA="$EXTRA" python3 -I tools/fam_run.py $BIN fxgold quick/fx-$TAG.tsv ht_bridge,auto 1 fx/*.ofn
grep -v refl1213 runs/flips.tsv > quick/flips12.tsv
DIFF_THREADS=2 ROWS_EXTRA="$(echo $EXTRA | tr ';' ',')" tools/rows.sh $BIN quick/flips12.tsv quick/flips-$TAG.tsv 60 >/dev/null 2>&1
echo "fixtures: $(cut -f4 quick/fx-$TAG.tsv | sort | uniq -c | tr '\n' ' ')"
awk -F'\t' '{print $2"\t"$3"\t"$4"\t"$5}' quick/flips-$TAG.tsv | sed 's|.*/||'
