#!/bin/bash
# usage: bridge.sh <km> <ontology> <tag> [extra env assignments...]; forced ht_bridge with progress logs
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values
km=$1; o=$2; tag=$3; shift 3
cd $S
mkdir -p $S/tmp/$o.$tag; env "$@" TMPDIR=$S/tmp/$o.$tag KM_HT_STATS=1 KM_THREADS=1 KM_ROUTE=ht_bridge KM_BRIDGE_PROGRESS=1 KM_DATA_ASSERTION_AS_CLASS=1 KM_TIMING=1 /usr/bin/time -f "%e s %M KB" timeout ${TO:-600} $km classify $(ls ${SRC:-inputs}/$o.owl ${SRC:-inputs}/$o.ttl 2>/dev/null | head -1) > logs/$o.$tag.out 2> logs/$o.$tag.err
echo "== $o $tag $(tail -1 logs/$o.$tag.err)"; grep -E "prepare-total|DEFER|bridge defer|NOMINAL-CONSISTENCY|engine block" logs/$o.$tag.err | head -4
rm -rf $S/tmp/$o.$tag
