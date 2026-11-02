#!/bin/bash
# diff_all.sh BIN TAG : HermiT differentials of BIN on the seed pools (routes
# ht_bridge and auto, 60 s per KM run, two KM runs at a time). Output:
# $S/diff/<pool>-<TAG>.tsv (diff_run.py columns).
B=$1; TAG=$2
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-abox-probes
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle
T=$(dirname $0)
mkdir -p $S/diff
export TMPDIR=$S/tmp DIFF_THREADS=2 DIFF_KM_TIMEOUT=60 DIFF_HERMIT_TIMEOUT=120
export DIFF_KEEP="KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1"
run() { pool=$1; gold=$2; shift 2; rm -f $S/diff/$pool-$TAG.tsv; python3 -I $T/diff_run.py $B $O $gold $S/diff/$pool-$TAG.tsv ht_bridge,auto "$@"; echo "$pool done" >> $S/diff/progress-$TAG.txt; }
run mrest $S/mgold $(ls $S/mseeds/*.ofn | sort -V)
run same $A/sameindividual-bridge/gold $(ls $A/sameindividual-bridge/seeds/*.ofn | sort -V)
run chain $A/sameindividual-bridge/cgold $(ls $A/sameindividual-bridge/cseeds/*.ofn | sort -V)
run defers $S/defers/gold $(ls $S/defers/seeds/*.ofn | sort -V)
run defersf $S/defers/fgold $(ls $S/defers/fseeds/*.ofn | sort -V)
run nommerge $A/bridge-nominal-merge/gold $(ls $A/bridge-nominal-merge/seeds/*.ofn | sort -V)
echo ALL >> $S/diff/progress-$TAG.txt
