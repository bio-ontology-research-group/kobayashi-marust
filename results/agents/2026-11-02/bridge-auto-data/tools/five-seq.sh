#!/bin/bash
# five.sh BIN LABEL N : N automatic-route runs each of ore_ont_6132 and
# ore_ont_9899 (one at a time when SEQ=1), release flags, KM_TIMING for the route
# trace, timeout 240; compares each answer with its pinned references.
BIN=$1; LABEL=$2; N=${3:-5}
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust
S=$R/.work/agent-scratch/bridge-auto-data/data/five-$LABEL; mkdir -p $S
T=$(dirname $(readlink -f $0))
export TMPDIR=$R/.work/agent-scratch/bridge-auto-data/tmp
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_TIMING=1
one() { n=$1; i=$2; s=$(date +%s.%N); /usr/bin/time -v -o $S/$n.$i.time timeout -k 5 240 $BIN classify $R/v150-corpus/files/ore_ont_$n.owl > $S/$n.$i.json 2> $S/$n.$i.err; rc=$?
  w=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-6); rss=$(awk '/Maximum resident/ {printf "%.2f", $NF/1048576}' $S/$n.$i.time)
  via=$(grep -oE "automatic data source accepted: [A-Z_]+|bounded bridge-first[a-z() ]* accepted|answer published by the bridge arm|CB slot filled" $S/$n.$i.err | head -1)
  agree=""; [ $rc = 0 ] && agree=$(python3 -I $T/compare_ref.py ore_ont_$n $S/$n.$i.json $S/cmp-$n.$i 2>&1 | grep -oE '"reference": "[a-z]+", "status": "[a-z_]+"' | sed 's/"reference": //; s/, "status": /=/; s/"//g' | tr '\n' ' ')
  echo -e "$n\trun=$i\trc=$rc\twall=$w\trss_gib=$rss\tvia=$via\t$agree" >> $S/summary.tsv; }
: > $S/summary.tsv
for i in $(seq 1 $N); do one 6132 $i; one 9899 $i; done
echo DONE >> $S/summary.tsv
