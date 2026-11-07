#!/bin/bash
# ore_nominal_seq.sh BASE_BIN NEW_BIN : the 112 nominal ORE design-half inputs,
# one process at a time, base then new on each input, release flags, 300 s
# (ore_time.sh on one-line lists; ore_pair.py pairs the two tags).
T=$(dirname $(readlink -f $0))
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-nn1811/ore
mkdir -p $O; rm -f $O/times-before.tsv $O/times-after.tsv
F="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
while read -r p; do
  echo "$p" > $O/one.txt
  $T/ore_time.sh $1 $O/one.txt $O before $F
  $T/ore_time.sh $2 $O/one.txt $O after $F
done < $T/ore-design-nominal.txt
sed -i '/^DONE$/d' $O/times-before.tsv $O/times-after.tsv
python3 -I $T/ore_pair.py $O before after > $O/pair.txt
echo "guard fired (after): $(grep -l 'coverage guard' $O/out-after/*.errtail | wc -l)" >> $O/pair.txt
