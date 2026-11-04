#!/bin/bash
# run1.sh (scratch copy) BIN FILE ROUTE [CAP] [extra env...]: release flags, prints status, time, subsumptions
BIN=$1; F=$2; RT=$3; CAP=${4:-60}; shift 4
E=(env -i PATH=$PATH HOME=$HOME TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-nn1811/tmp KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1)
[ "$RT" != auto ] && E+=(KM_ROUTE=$RT)
E+=("$@")
s=$(date +%s.%N)
out=$(timeout -k 5 $CAP "${E[@]}" $BIN classify $F 2>$F.$RT.err); rc=$?
w=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-5)
subs=$(echo "$out" | python3 -c "import json,sys
try:
  d=json.load(sys.stdin); l=lambda x:x.split('#')[-1]
  print('cons=%s'%d.get('consistent'), sorted((l(a),l(b)) for a,b in d.get('subsumptions',[]) if l(b)!='Thing' and l(a)!=l(b)), 'unsat=',[l(x) for x in d.get('unsatisfiable',[])])
except Exception as e: print('NOJSON')")
echo -e "$(basename $F)\t$RT\trc=$rc\t$w\t$subs"
