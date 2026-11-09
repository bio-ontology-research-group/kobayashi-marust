#!/bin/bash
# ore_nominal.sh BASE_BIN NEW_BIN : the 112 nominal ORE design-half inputs,
# base then new, one process at a time, release flags, 300 s (ore_time.sh,
# ore_pair.py and the list copied from results/agents/2026-11-02/bridge-self).
T=$(dirname $(readlink -f $0))
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-s974/ore
mkdir -p $O; rm -f $O/times-before.tsv $O/times-after.tsv
F="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
$T/ore_time.sh $1 $T/ore-design-nominal.txt $O before $F
$T/ore_time.sh $2 $T/ore-design-nominal.txt $O after $F
python3 -I $T/ore_pair.py $O before after > $O/pair.txt
echo "guard fired (after): $(grep -l 'coverage guard fired' $O/out-after/*.errtail | wc -l)" >> $O/pair.txt
