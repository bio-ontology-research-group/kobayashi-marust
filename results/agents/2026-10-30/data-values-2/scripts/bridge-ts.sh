#!/bin/bash
# usage: bridge-ts.sh <km> <input> <tag> [env...]; forced ht_bridge, stderr timestamped to logs/<tag>.err
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-2
km=$1; in=$2; tag=$3; shift 3
mkdir -p $S/tmp/$tag
( env "$@" TMPDIR=$S/tmp/$tag KM_HT_STATS=1 KM_THREADS=1 KM_ROUTE=${ROUTE:-ht_bridge} KM_BRIDGE_PROGRESS=1 KM_DATA_ASSERTION_AS_CLASS=1 KM_TIMING=1 KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1 /usr/bin/time -f "%e s %M KB" timeout ${TO:-600} $km classify $in > $S/logs/$tag.out ) 2>&1 | python3 $S/bin/tstamp.py $S/logs/$tag.err
rm -rf $S/tmp/$tag
echo "== $tag $(tail -1 $S/logs/$tag.err)"
