#!/bin/bash
# ore_self4.sh BIN OUT : the four SELF-bearing nominal design-half inputs, after then before.
T=$(dirname $(readlink -f $0)); BIN=$1; O=$2; mkdir -p $O
grep -E "12451|2548|7532|9662" $T/ore-design-nominal.txt > $O/list.txt
$T/ore_time.sh $BIN $O/list.txt $O after KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1
$T/ore_time.sh $BIN $O/list.txt $O before KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_BRIDGE_SAT_REFUSE_SELF=1
python3 -I $T/ore_pair.py $O before after > $O/pair.txt
