#!/bin/bash
# pools.sh BIN LABEL [LIST] : the gold-backed seed pools of earlier agents
# (copied from results/agents/2026-11-03/bridge-reflexive/tools; output
# directory changed, the bridge-reflexive family and seeds20 added),
# routes ht_bridge and auto, release flags, 60 s, two KM runs at a time,
# through diff_run.py. LIST (default: every pool below) restricts the run
# to "name<TAB>file" rows (used for the base rerun of the non-ok seeds).
# Rows go to .work/agent-scratch/bridge-nn-rule/pools/LABEL/NAME.tsv.
T=$(dirname $(readlink -f $0)); BIN=$1; LABEL=$2; LIST=$3
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
D=$A/bridge-nn-rule/pools/$LABEL; mkdir -p $D
mkdir -p $A/bridge-nn-rule/tmp; export TMPDIR=$A/bridge-nn-rule/tmp DIFF_THREADS=2 DIFF_KM_TIMEOUT=60
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
POOLS=()
for P in $A/bridge-self/pools/*; do POOLS+=("bridge-self-pools-$(basename $P) $P/seeds $P/gold"); done
POOLS+=("bridge-self-pool $A/bridge-self/pool/seeds $A/bridge-self/pool/gold")
POOLS+=("bridge-self-regress $A/bridge-self/regress/seeds $A/bridge-self/regress/gold")
POOLS+=("bridge-self-micro $A/bridge-self/micro $A/bridge-self/micro/gold")
POOLS+=("bridge-m413-respool $A/bridge-m413/respool/seeds $A/bridge-m413/respool/gold")
POOLS+=("bridge-m413-k $A/bridge-m413/kseeds $A/bridge-m413/kgold")
POOLS+=("bridge-m413-k2 $A/bridge-m413/k2seeds $A/bridge-m413/k2gold")
POOLS+=("cb-s974-merge $A/cb-s974/fam-merge/seeds $A/cb-s974/fam-merge/gold")
POOLS+=("cb-s974-vacuous $A/cb-s974/fam-vacuous/seeds $A/cb-s974/fam-vacuous/gold")
POOLS+=("bridge-reflexive-fam $A/bridge-reflexive/fam/seeds $A/bridge-reflexive/fam/gold")
POOLS+=("bridge-reflexive-seeds20 $A/bridge-reflexive/seeds20 $A/bridge-reflexive/seeds20/gold")
for row in "${POOLS[@]}"; do set -- $row; name=$1; SEEDS=$2; GOLD=$3
  [ -d "$SEEDS" ] || { echo "$name missing $SEEDS" >> $D/summary.txt; continue; }
  files=()
  if [ -n "$LIST" ]; then files=($(awk -F'\t' -v n=$name '$1==n {print $2}' $LIST))
  else for f in $(ls -L $SEEDS/*.ofn); do st=$(basename $f .ofn); [ -s $GOLD/$st.json ] && files+=($f); done; fi
  : > $D/$name.tsv; [ ${#files[@]} -eq 0 ] && continue
  export DIFF_ERRDIR=$D/err-$name; mkdir -p $DIFF_ERRDIR
  python3 -I $T/diff_run.py $BIN /nonexistent $GOLD $D/$name.tsv ht_bridge,auto "${files[@]}"
  echo "$name $(cut -f2,3 $D/$name.tsv | sort | uniq -c | tr '\n' ' ')" >> $D/summary.txt
done
echo DONE >> $D/summary.txt
