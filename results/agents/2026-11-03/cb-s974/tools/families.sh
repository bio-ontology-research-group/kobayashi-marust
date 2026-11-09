#!/bin/bash
# families.sh BIN LABEL RUNS : both sibling families on BIN (merge: auto and
# cb_plain1; vacuous: auto and seq), RUNS runs per seed and route.
T=$(dirname $(readlink -f $0)); BIN=$1; L=$2; N=${3:-3}
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-s974
export TMPDIR=$S/tmp
mkdir -p $S/fam-out
for f in merge:auto,cb_plain1 vacuous:auto,seq; do fam=${f%%:*}; specs=${f#*:}
  out=$S/fam-out/$fam.$L.tsv; : > $out
  python3 -I $T/fam_run.py $BIN $S/fam-$fam/gold $out $specs $N $(ls $S/fam-$fam/seeds/*.ofn | sort -V)
  echo "$fam $L $(cut -f2,4 $out | sort | uniq -c | tr '\n' ' ')"
done
