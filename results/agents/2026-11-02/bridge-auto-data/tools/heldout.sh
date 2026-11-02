#!/bin/bash
# heldout.sh BIN LABEL [IDS...] : the 16 held-out inputs of docs/V1.5.5-STATUS.md
# ("Konclude coverage gap") on the automatic route, release flags, one core,
# timeout 240, two runs at a time; compares each answer with its pinned
# references (compare_ref.py). Writes .work/agent-scratch/bridge-auto-data/data/heldout-LABEL/.
BIN=$1; LABEL=$2; shift 2
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust
S=$R/.work/agent-scratch/bridge-auto-data/data/heldout-$LABEL; mkdir -p $S
T=$(dirname $(readlink -f $0))
export TMPDIR=$R/.work/agent-scratch/bridge-auto-data/tmp
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1
one() { n=$1; s=$(date +%s.%N); /usr/bin/time -v -o $S/$n.time timeout -k 5 240 $BIN classify $R/v150-corpus/files/ore_ont_$n.owl > $S/$n.json 2> $S/$n.err; rc=$?
  w=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-6); rss=$(awk '/Maximum resident/ {printf "%.2f", $NF/1048576}' $S/$n.time)
  agree=""; [ $rc = 0 ] && agree=$(python3 -I $T/compare_ref.py ore_ont_$n $S/$n.json $S/cmp-$n 2>&1 | grep -oE '"reference": "[a-z]+", "status": "[a-z_]+"' | sed 's/"reference": //; s/, "status": /=/; s/"//g' | tr '\n' ' ')
  echo -e "$n\trc=$rc\twall=$w\trss_gib=$rss\t$agree" >> $S/summary.tsv; }
[ $# = 0 ] && set -- 4903 11647 4796 3917 11378 12191 9151 9577 6132 9899 16315 10838 3087 7557 12128 10926
: > $S/summary.tsv
while [ $# -gt 0 ]; do one $1 & [ $# -gt 1 ] && one $2 & wait; shift 2 2>/dev/null || shift; done
echo DONE >> $S/summary.tsv
