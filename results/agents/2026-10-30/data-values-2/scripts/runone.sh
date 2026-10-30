#!/bin/bash
# usage: runone.sh <km-binary> <ontology-name> <outdir> [timeout_s]
set -u
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-2
km=$1; o=$2; out=$3; to=${4:-600}
mkdir -p "$out"; out=$(readlink -f "$out")
src=$S/inputs/$o.owl; [ -f "$src" ] || src=$5
export OMP_NUM_THREADS=1 RAYON_NUM_THREADS=1 KM_THREADS=1 KM_ROUTE=${KM_ROUTE:-auto} KM_TIMING=1
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1
export TMPDIR=$out/tmp; mkdir -p $TMPDIR
start=$(date +%s.%N)
/usr/bin/time -f %M -o "$out/maxrss" timeout -k 5 $to "$km" classify "$src" > "$out/taxonomy.raw" 2> "$out/stderr"
rc=$?
end=$(date +%s.%N)
wall=$(python3 -c "print(round($end-$start,2))")
verdict=none
[ $rc -eq 0 ] && verdict=$($S/bin/audit.sh "$out" $o)
rm -rf $out/tmp
dropped=$(python3 -c "import json;d=json.load(open('$out/taxonomy.raw'));print('dropped='+str(d.get('dropped',0)),'consistent='+str(d.get('consistent')))" 2>/dev/null)
route=$(grep -o "route=[a-z_]*" "$out/stderr" | tail -1)
echo -e "$o\trc=$rc\twall=$wall\trss_kib=$(cat $out/maxrss 2>/dev/null|tail -1)\t$dropped\t$route\t$verdict"
