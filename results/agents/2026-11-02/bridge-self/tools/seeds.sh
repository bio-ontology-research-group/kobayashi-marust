#!/bin/bash
# seeds.sh BIN LABEL [ROUTES] [POOLS] : gold-backed seed pools on BIN, both
# routes, through diff_run.py (two KM runs at a time), 60 s cap. Extra KM_*
# variables for every run go in DIFF_EXTRA (comma-separated K=V). POOLS are
# directories below .work/agent-scratch (or absolute) with seeds/ and gold/.
BIN=$1; LABEL=$2; ROUTES=${3:-ht_bridge,auto}
POOLS=${4:-"bridge-self/pool"}
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
T=$(dirname $(readlink -f $0))
D=$S/bridge-self/data/seeds-$LABEL; mkdir -p $D
export TMPDIR=$S/bridge-self/tmp
export DIFF_THREADS=${DIFF_THREADS:-2} DIFF_KM_TIMEOUT=${DIFF_KM_TIMEOUT:-60}
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1${DIFF_EXTRA:+,$DIFF_EXTRA}
for pool in $POOLS; do
  case $pool in /*) P=$pool ;; *) P=$S/$pool ;; esac
  name=$(echo ${pool#/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/} | tr / -)
  files=()
  list=$(ls $P/seeds/*.ofn); [ "$name" = r3-unannounced ] && [ -n "$R3_FIRST" ] && list=$(echo "$list" | head -$R3_FIRST)
  # RESUME=1 keeps the existing rows and runs only seeds without both routes.
  if [ -n "$RESUME" ] && [ -s $D/$name.tsv ]; then done_list=$(cut -f1 $D/$name.tsv | sort | uniq -c | awk '$1>=2 {print $2}'); else done_list=""; : > $D/$name.tsv; fi
  for f in $list; do
    st=$(basename $f .ofn); [ -s $P/gold/$st.json ] || continue
    [ -n "$done_list" ] && grep -qxF "$f" <<< "$done_list" && continue
    files+=($f)
  done
  python3 -I $T/diff_run.py $BIN /nonexistent $P/gold $D/$name.tsv $ROUTES "${files[@]}"
  echo "$name $(cut -f2,3 $D/$name.tsv | sort | uniq -c | tr '\n' ' ')" >> $D/summary.txt
done
