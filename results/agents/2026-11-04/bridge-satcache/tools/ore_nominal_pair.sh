#!/bin/bash
# ore_nominal_pair.sh BASE_BIN NEW_BIN : the 112 nominal ORE design-half
# inputs, BASE and NEW on each input at the same time (two KM processes, the
# same host load for both), release flags, 300 s. Same outputs as
# ore_nominal.sh (times-before.tsv, times-after.tsv, out-*/NAME.sig.gz,
# pair.txt), so ore_pair.py reads them unchanged.
T=$(dirname $(readlink -f $0))
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-satcache/ore
mkdir -p $O/out-before $O/out-after; rm -f $O/times-before.tsv $O/times-after.tsv
F="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
one() { # one KM_BIN INPUT TAG
  local km=$1 p=$2 tag=$3 n s e rc route
  n=$(basename "$p" .owl); s=$(date +%s.%N)
  env $(env | grep -o '^KM_[A-Z_]*' | sed 's/^/-u /') KM_TIMING=1 $F timeout 300 "$km" classify --lines "$p" \
    > "$O/out-$tag/$n.out" 2> "$O/out-$tag/$n.err"
  rc=$?; e=$(date +%s.%N)
  route=$(grep -o 'route=[a-z_]*' "$O/out-$tag/$n.err" | head -1 | cut -d= -f2)
  grep -E '^(SUB|UNSAT|CONSISTENT)' "$O/out-$tag/$n.out" | sort | gzip > "$O/out-$tag/$n.sig.gz"
  rm -f "$O/out-$tag/$n.out"; tail -c 4000 "$O/out-$tag/$n.err" > "$O/out-$tag/$n.errtail"; rm -f "$O/out-$tag/$n.err"
  echo -e "$n\t$tag\t$rc\t$(echo "$e - $s" | bc)\t$route" >> "$O/times-$tag.tsv"
}
while read -r p; do
  one $1 "$p" before & one $2 "$p" after & wait
done < $T/ore-design-nominal.txt
echo DONE >> $O/times-before.tsv; echo DONE >> $O/times-after.tsv
python3 -I $T/ore_pair.py $O before after > $O/pair.txt
echo "guard fired (after): $(grep -l 'coverage guard fired' $O/out-after/*.errtail | wc -l)" >> $O/pair.txt
