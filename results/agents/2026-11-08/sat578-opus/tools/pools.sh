#!/bin/bash
# pools.sh BIN LABEL : the gold-backed seed pools of earlier agents plus the
# sat578 family, routes ht_bridge and auto, release flags, 60 s cap, through
# diff_run.py, DIFF_THREADS KM runs at a time (default 1). Adapted from
# results/agents/2026-11-06/sat578/tools/pools.sh (fix/v155-sat578); writes
# under .work/agent-scratch/sat578-opus/pools/LABEL. With GUARD=1 every run
# records whether a section 25 guard fired (fired-POOL/<stem>.<route>.fired).
T=$(dirname $(readlink -f $0)); BIN=$1; LABEL=$2
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
S=$A/sat578-opus
D=$S/pools/$LABEL; mkdir -p $D
export TMPDIR=$S/tmp DIFF_THREADS=${DIFF_THREADS:-1} DIFF_KM_TIMEOUT=60
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
POOLS=()
POOLS+=("sat578-fam $A/sat578/fam $A/sat578/famgold")
POOLS+=("bridge-satcache-fam $A/bridge-satcache/fam $A/bridge-satcache/famgold")
POOLS+=("bridge-nn-rule-fam $A/bridge-nn-rule/fam/seeds $A/bridge-nn-rule/fam/gold")
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
NNR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-bridge-nn-rule/results/agents/2026-11-04/bridge-nn-rule/data/reductions
POOLS+=("bridge-nn-rule-red $NNR $NNR")
POOLS+=("bridge-satcache-red $A/bridge-satcache/red $A/bridge-satcache/gold")
POOLS+=("bridge-satcache-self $A/bridge-satcache/selffix $A/bridge-satcache/selffix/gold")
for row in "${POOLS[@]}"; do set -- $row; name=$1; SEEDS=$2; GOLD=$3
  [ -d "$SEEDS" ] || { echo "$name missing $SEEDS" >> $D/summary.txt; continue; }
  [ -s $D/$name.tsv ] && continue
  files=()
  for f in $(ls -L $SEEDS/*.ofn); do st=$(basename $f .ofn); [ -s $GOLD/$st.json ] && files+=($f); done
  : > $D/$name.tsv.part; [ ${#files[@]} -eq 0 ] && { mv $D/$name.tsv.part $D/$name.tsv; continue; }
  export DIFF_ERRDIR=$D/err-$name; mkdir -p $DIFF_ERRDIR
  if [ -n "$GUARD" ]; then export DIFF_GUARD_DIR=$D/fired-$name; mkdir -p $DIFF_GUARD_DIR; fi
  python3 -I $T/diff_run.py $BIN /nonexistent $GOLD $D/$name.tsv.part ht_bridge,auto "${files[@]}"
  mv $D/$name.tsv.part $D/$name.tsv
  echo "$name $(cut -f2,3 $D/$name.tsv | sort | uniq -c | tr '\n' ' ')" >> $D/summary.txt
done
echo DONE >> $D/summary.txt
