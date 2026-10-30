#!/bin/bash
# usage: tab.sh BIN INPUT.json OUTPREFIX [ENV=VAL...]; runs the rules-consistency worker alone
bin=$1; in=$2; out=$3; shift 3
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1 KM_THREADS=1 RAYON_NUM_THREADS=1 OMP_NUM_THREADS=1 KM_ROUTE=auto KM_ROUTING_POLICY=${POL:-v153}
export KM_RULES_CONSISTENCY=1 KM_TRANSITIVE_RULE_REDUCE=1 KM_RULE_JOIN_ORDER=1
export TMPDIR=$HOME/tmp
for kv in "$@"; do export "$kv"; done
s=$(date +%s.%N)
timeout ${TO:-600} taskset -c ${CPU:-40} "$bin" tableau < "$in" > "$out.out" 2> "$out.err"
rc=$?
e=$(date +%s.%N)
printf "%s\t%s\t%s\t%.2f\n" "$(basename $bin)" "$(basename $(dirname $in))" "$rc" "$(echo "$e - $s" | bc)"
