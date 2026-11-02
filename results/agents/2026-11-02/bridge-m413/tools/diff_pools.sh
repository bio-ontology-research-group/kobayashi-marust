#!/bin/bash
# diff_pools.sh BIN TAG POOL... : HermiT differentials of BIN on the named seed
# pools, routes ht_bridge and auto, release flags, DIFF_KM_TIMEOUT s per run
# (default 30), DIFF_THREADS KM runs at a time (default 2).
# Pools: k (this agent, gen_m413.py), mrest same chain defers defersf nommerge replay
# dcr nomcov dvprobes fndm tnd (bridge-defers run_pools.sh), res (gold-bearing seeds of
# results/agents/2026-10-3*/ copied to $S/respool).
# Output: $S/diff/<pool>-<TAG>.tsv (diff_run.py columns).
B=$1; TAG=$2; shift 2
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-m413
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle
T=$(dirname $0)
mkdir -p $S/diff $S/tmp
export TMPDIR=$S/tmp DIFF_THREADS=${DIFF_THREADS:-2} DIFF_KM_TIMEOUT=${DIFF_KM_TIMEOUT:-30} DIFF_HERMIT_TIMEOUT=120
export DIFF_KEEP="KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1,TMPDIR=$S/tmp"
pool_args() {
  case $1 in
    k) echo "$S/kgold $(ls $S/kseeds/*.ofn | sort -V)";;
    mrest) echo "$A/bridge-abox-probes/mgold $(ls $A/bridge-abox-probes/mseeds/*.ofn | sort -V)";;
    same) echo "$A/sameindividual-bridge/gold $(ls $A/sameindividual-bridge/seeds/*.ofn | sort -V)";;
    chain) echo "$A/sameindividual-bridge/cgold $(ls $A/sameindividual-bridge/cseeds/*.ofn | sort -V)";;
    defers) echo "$A/bridge-abox-probes/defers/gold $(ls $A/bridge-abox-probes/defers/seeds/*.ofn | sort -V)";;
    defersf) echo "$A/bridge-abox-probes/defers/fgold $(ls $A/bridge-abox-probes/defers/fseeds/*.ofn | sort -V)";;
    nommerge) echo "$A/bridge-nominal-merge/gold $(ls $A/bridge-nominal-merge/seeds/*.ofn | sort -V)";;
    replay) echo "$A/bridge-replay/pool/gold $(ls $A/bridge-replay/pool/seeds/*.ofn | sort -V)";;
    dcr) echo "$A/data-coverage-regression/gold-seeds $(ls $A/data-coverage-regression/seeds/*.ofn | sort -V)";;
    nomcov) echo "$A/nominal-coverage/gold $(ls $A/nominal-coverage/seeds/*.ofn | sort -V)";;
    dvprobes) echo "$A/data-values/probes/gold $(ls $A/data-values/probes/gen/*.ofn | sort -V)";;
    fndm) echo "$A/forced-nominal-data-misses/gold-fixtures $(ls $A/forced-nominal-data-misses/fixtures/*.ofn | sort -V)";;
    tnd) echo "$A/top-nominal-data/gold_fresh3 $(ls $A/top-nominal-data/fresh3/*.ofn | sort -V)";;
    res) echo "$S/respool/gold $(ls $S/respool/seeds/*.ofn | sort -V)";;
  esac
}
for pool in "$@"; do
  set -- $(pool_args $pool)
  gold=$1; shift
  rm -f $S/diff/$pool-$TAG.tsv
  python3 -I $T/diff_run.py $B $O $gold $S/diff/$pool-$TAG.tsv ht_bridge,auto "$@"
  echo "$pool done $(date +%T)" >> $S/diff/progress-$TAG.txt
done
