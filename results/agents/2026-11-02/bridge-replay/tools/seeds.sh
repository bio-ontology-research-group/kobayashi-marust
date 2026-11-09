#!/bin/bash
# seeds.sh BIN LABEL [ROUTES] [POOLS] : every gold-backed seed pool on BIN,
# both routes, through diff_run.py (two KM runs at a time), 60 s cap.
BIN=$1; LABEL=$2; ROUTES=${3:-ht_bridge,auto}
POOLS=${4:-"bridge-replay/pool bridge-defers bridge-nominal-merge nominal-coverage sameindividual-bridge r3-unannounced"}
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
T=$(dirname $(readlink -f $0))
D=$S/bridge-replay/data/seeds-$LABEL; mkdir -p $D
export TMPDIR=$S/bridge-replay/tmp
export DIFF_THREADS=${DIFF_THREADS:-2} DIFF_KM_TIMEOUT=${DIFF_KM_TIMEOUT:-60}
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1${DIFF_EXTRA:+,$DIFF_EXTRA}
for pool in $POOLS; do
  name=$(echo $pool | tr / -)
  files=()
  # R3_FIRST=N limits r3-unannounced to its first N seeds (sorted order).
  list=$(ls $S/$pool/seeds/*.ofn); [ "$pool" = r3-unannounced ] && [ -n "$R3_FIRST" ] && list=$(echo "$list" | head -$R3_FIRST)
  for f in $list; do
    st=$(basename $f .ofn); [ -s $S/$pool/gold/$st.json ] && files+=($f)
  done
  rm -f $D/$name.tsv
  python3 -I $T/diff_run.py $BIN /nonexistent $S/$pool/gold $D/$name.tsv $ROUTES "${files[@]}"
  echo "$name $(cut -f3 $D/$name.tsv | sort | uniq -c | tr '\n' ' ')" >> $D/summary.txt
done
