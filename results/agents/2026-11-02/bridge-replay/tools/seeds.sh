#!/bin/bash
# seeds.sh BIN LABEL ROUTES : run every gold-backed seed pool on BIN, 2 at a time.
BIN=$1; LABEL=$2; ROUTES=${3:-ht_bridge,auto}
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
D=$S/bridge-speed/data/seeds-$LABEL; mkdir -p $D
export DIFF_THREADS=${DIFF_THREADS:-2} DIFF_KM_TIMEOUT=${DIFF_KM_TIMEOUT:-60}
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
for pool in bridge-defers bridge-nominal-merge nominal-coverage sameindividual-bridge r3-unannounced; do
  files=()
  for f in $S/$pool/seeds/*.ofn; do
    st=$(basename $f .ofn); [ -f $S/$pool/gold/$st.json ] && files+=($f)
  done
  rm -f $D/$pool.tsv
  python3 -I $S/bridge-speed/tools/diff_run.py $BIN /nonexistent $S/$pool/gold $D/$pool.tsv $ROUTES "${files[@]}"
  echo "$pool $(cut -f3 $D/$pool.tsv | sort | uniq -c | tr '\n' ' ')" >> $D/summary.txt
done
