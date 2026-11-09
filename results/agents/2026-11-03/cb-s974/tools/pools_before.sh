#!/bin/bash
# pools_before.sh BASE_BIN : rerun on the base binary every pool seed whose
# answer after the fix was not `ok` on some route (WRONG, ERR, TIMEOUT), so a
# non-ok row after the fix can be classified as new or pre-existing. A seed
# that is `ok` after the fix on every route agrees with HermiT and cannot be
# a new difference, so the base is not rerun on it.
T=$(dirname $(readlink -f $0)); BIN=$1
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
D=$A/cb-s974/pools/before; mkdir -p $D
export TMPDIR=$A/cb-s974/tmp DIFF_THREADS=2 DIFF_KM_TIMEOUT=60
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
for f in $A/cb-s974/pools/after/*.tsv; do name=$(basename $f .tsv)
  P=$A/${name//-//}; [ -d "$P" ] || P=$(ls -d $A/bridge-self/pools/${name#bridge-self-pools-} 2>/dev/null)
  case $name in bridge-self-pool) P=$A/bridge-self/pool ;; bridge-m413-respool) P=$A/bridge-m413/respool ;; esac
  files=($(awk -F'\t' '$3!="ok" {print $1}' $f | sort -u))
  : > $D/$name.tsv
  [ ${#files[@]} -gt 0 ] && python3 -I $T/diff_run.py $BIN /nonexistent $P/gold $D/$name.tsv ht_bridge,auto "${files[@]}"
  echo "$name rerun=${#files[@]} $(cut -f2,3 $D/$name.tsv | sort | uniq -c | tr '\n' ' ')" >> $D/summary.txt
done
