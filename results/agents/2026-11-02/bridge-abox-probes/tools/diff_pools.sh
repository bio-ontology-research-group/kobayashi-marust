#!/bin/bash
# diff_pools.sh BIN TAG POOL... : HermiT differentials of BIN (routes ht_bridge
# and auto, DIFF_KM_TIMEOUT s per KM run, DIFF_THREADS KM runs at a time) on
# the named seed pools: mrest same chain defers defersf nommerge.
# Output: $S/diff/<pool>-<TAG>.tsv (diff_run.py columns).
B=$1; TAG=$2; shift 2
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-abox-probes
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle
T=$(dirname $0)
mkdir -p $S/diff
export TMPDIR=$S/tmp DIFF_THREADS=${DIFF_THREADS:-2} DIFF_KM_TIMEOUT=${DIFF_KM_TIMEOUT:-30} DIFF_HERMIT_TIMEOUT=120
export DIFF_KEEP="KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1,TMPDIR=$S/tmp"
pool_args() {
  case $1 in
    mrest) echo "$S/mgold $(ls $S/mseeds/*.ofn | sort -V)";;
    same) echo "$A/sameindividual-bridge/gold $(ls $A/sameindividual-bridge/seeds/*.ofn | sort -V)";;
    chain) echo "$A/sameindividual-bridge/cgold $(ls $A/sameindividual-bridge/cseeds/*.ofn | sort -V)";;
    defers) echo "$S/defers/gold $(ls $S/defers/seeds/*.ofn | sort -V)";;
    defersf) echo "$S/defers/fgold $(ls $S/defers/fseeds/*.ofn | sort -V)";;
    nommerge) echo "$A/bridge-nominal-merge/gold $(ls $A/bridge-nominal-merge/seeds/*.ofn | sort -V)";;
  esac
}
for pool in "$@"; do
  set -- $(pool_args $pool)
  gold=$1; shift
  rm -f $S/diff/$pool-$TAG.tsv
  python3 -I $T/diff_run.py $B $O $gold $S/diff/$pool-$TAG.tsv ht_bridge,auto "$@"
  echo "$pool done $(date +%T)" >> $S/diff/progress-$TAG.txt
done
