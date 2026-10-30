#!/bin/bash
# usage: capture.sh <km> <input> <prefix> [route]; runs classify and copies the first `km engine` child's stdin+env to <prefix>.clauses.json/.env
km=$1; in=$2; pre=$3; route=${4:-auto}
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-2
mkdir -p $S/tmp/cap.$$
( export OMP_NUM_THREADS=1 RAYON_NUM_THREADS=1 KM_THREADS=1 KM_ROUTE=$route KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1 TMPDIR=$S/tmp/cap.$$; timeout 120 $km classify $in > /dev/null 2>&1 ) &
for i in $(seq 1200); do
  for p in $(pgrep -f "^$km engine"); do
    f=$(readlink /proc/$p/fd/0)
    case $f in $S/tmp/cap.$$/*) cp $f $pre.clauses.json; tr '\0' '\n' < /proc/$p/environ | grep '^KM_' | sort > $pre.env; kill $p; echo captured $p; wait; rm -rf $S/tmp/cap.$$; exit 0;; esac
  done; sleep 0.1
done
