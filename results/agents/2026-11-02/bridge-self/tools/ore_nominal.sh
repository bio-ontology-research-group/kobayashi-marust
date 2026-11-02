#!/bin/bash
# ore_nominal.sh BIN : the 112 nominal ORE design-half inputs, before (the
# SELF refusal) and after, one process at a time, release flags, 300 s.
T=$(dirname $(readlink -f $0)); BIN=$1
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-self/ore
mkdir -p $O; rm -f $O/times-before.tsv $O/times-after.tsv
F="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
$T/ore_time.sh $BIN $T/ore-design-nominal.txt $O after $F
$T/ore_time.sh $BIN $T/ore-design-nominal.txt $O before $F KM_BRIDGE_SAT_REFUSE_SELF=1
python3 -I $T/ore_pair.py $O before after > $O/pair.txt
