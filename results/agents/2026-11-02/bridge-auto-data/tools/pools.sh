#!/bin/bash
# pools.sh BIN LABEL [ROUTES] : every gold-backed seed pool on BIN through
# diff_run.py (two KM runs at a time, 60 s cap, release flags). Writes
# .work/agent-scratch/bridge-auto-data/data/pools-LABEL/<pool>.tsv.
BIN=$1; LABEL=$2; ROUTES=${3:-ht_bridge,auto}
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
T=$(dirname $(readlink -f $0))
D=$S/bridge-auto-data/data/pools-$LABEL; mkdir -p $D
export TMPDIR=$S/bridge-auto-data/tmp
export DIFF_THREADS=${DIFF_THREADS:-2} DIFF_KM_TIMEOUT=${DIFF_KM_TIMEOUT:-60}
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
# name:seeds-dir:gold-dir[:first-N or "data" = only seeds whose text has a data
# value or data expression (`Data*` or `^^`), the only inputs on which the
# changed value-helper gate is reachable]
POOLS="${POOLS:-dvprobes:data-values/probes/gen:data-values/probes/gold
fndm:forced-nominal-data-misses/fixtures:forced-nominal-data-misses/gold-fixtures
tnd:top-nominal-data/fresh3:top-nominal-data/gold_fresh3
dcr:data-coverage-regression/seeds:data-coverage-regression/gold-seeds
dec:bridge-defers/seeds:bridge-defers/gold
decf:bridge-defers/fseeds:bridge-defers/fgold
nomcov:nominal-coverage/seeds:nominal-coverage/gold
same:sameindividual-bridge/seeds:sameindividual-bridge/gold:data
replay:bridge-replay/pool/seeds:bridge-replay/pool/gold:200
bnm:bridge-nominal-merge/seeds:bridge-nominal-merge/gold:200
r3:r3-unannounced/seeds:r3-unannounced/gold:200}"
for spec in $POOLS; do
  IFS=: read name seeds gold first <<< "$spec"
  files=()
  list=$(ls $S/$seeds/*.ofn 2>/dev/null)
  if [ "$first" = data ]; then list=$(grep -l -E "Data[A-Z]|\^\^" $list)
  elif [ -n "$first" ]; then list=$(echo "$list" | head -$first); fi
  for f in $list; do st=$(basename $f .ofn); [ -s $S/$gold/$st.json ] && files+=($f); done
  [ ${#files[@]} = 0 ] && { echo "$name: no gold-backed seeds" >> $D/summary.txt; continue; }
  rm -f $D/$name.tsv
  python3 -I $T/diff_run.py $BIN /nonexistent $S/$gold $D/$name.tsv $ROUTES "${files[@]}"
  echo "$name $(cut -f3 $D/$name.tsv | sort | uniq -c | tr '\n' ' ')" >> $D/summary.txt
done
echo DONE >> $D/summary.txt
