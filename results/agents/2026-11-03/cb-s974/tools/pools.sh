#!/bin/bash
# pools.sh BIN LABEL : the gold-backed seed pools of earlier agents (collected
# under .work/agent-scratch/bridge-self/pools, plus the SELF pool and the m413
# residue pool), routes ht_bridge and auto, release flags, 60 s, two KM runs
# at a time, through diff_run.py (copied from results/agents/2026-11-02/
# bridge-self/tools). Rows go to .work/agent-scratch/cb-s974/pools/LABEL/.
T=$(dirname $(readlink -f $0)); BIN=$1; LABEL=$2
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
D=$A/cb-s974/pools/$LABEL; mkdir -p $D
export TMPDIR=$A/cb-s974/tmp DIFF_THREADS=2 DIFF_KM_TIMEOUT=60
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
for P in $A/bridge-self/pools/* $A/bridge-self/pool $A/bridge-m413/respool; do
  name=$(echo ${P#$A/} | tr / -)
  files=(); for f in $(ls -L $P/seeds/*.ofn); do st=$(basename $f .ofn); [ -s $P/gold/$st.json ] && files+=($f); done
  : > $D/$name.tsv; export DIFF_ERRDIR=$D/err-$name; mkdir -p $DIFF_ERRDIR
  python3 -I $T/diff_run.py $BIN /nonexistent $P/gold $D/$name.tsv ht_bridge,auto "${files[@]}"
  echo "$name $(cut -f2,3 $D/$name.tsv | sort | uniq -c | tr '\n' ' ') guard=$(grep -rl 'coverage guard fired' $DIFF_ERRDIR 2>/dev/null | wc -l)" >> $D/summary.txt
done
