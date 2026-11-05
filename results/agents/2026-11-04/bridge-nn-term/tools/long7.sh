#!/bin/bash
# long7.sh BIN LABEL CAP ROUTE : the seven slow seeds, two at a time, NN trace counts.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-term; BIN=$1; L=$2; CAP=$3; ROUTE=$4
export TMPDIR=$S/tmp
F="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
R=""; [ "$ROUTE" != auto ] && R="KM_ROUTE=$ROUTE"
one(){ s=$(date +%s.%N); env -i PATH=$PATH HOME=$HOME TMPDIR=$TMPDIR $F $R KM_HT_NN_TRACE=${TRACE:-0} timeout -k 5 $CAP $BIN classify $S/seven/nn$1.ofn > $S/seven/nn$1.$L.$ROUTE.json 2> $S/seven/nn$1.$L.$ROUTE.err; rc=$?
 w=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-6); echo -e "nn$1\t$L\t$ROUTE\trc=$rc\t$w\tnn=$(grep -c NN-RULE $S/seven/nn$1.$L.$ROUTE.err)" >> $S/seven/summary.tsv; }
set -- 1333 346 952 745 1957 777 969
while [ $# -gt 0 ]; do one $1 & [ -n "$2" ] && one $2 & wait; shift; shift; done
