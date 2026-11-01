#!/bin/bash
# usage: frontend_check.sh BIN NAME OUTDIR -- frontend-only (km ofn) drop reasons and exit status
B=$1; n=$2; o=$3; f=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/$n.owl
d=$o/$n; mkdir -p $d
( cd $d && timeout 300 prlimit --as=$((20*1024*1024*1024)) -- $B ofn $f --meta meta.json > /dev/null 2> err.txt; echo $? > rc.txt; rm -f /dev/null.tmp )
python3 -c "
import json,sys
d='$d'
rc=open(d+'/rc.txt').read().strip()
try: m=json.load(open(d+'/meta.json'))['dropped_source_axioms']
except Exception: m=None
print('$n', rc, json.dumps({k:v for k,v in (m or {}).items() if 'data' in k.lower()}) if m is not None else 'no-meta', open(d+'/err.txt').read()[:200].replace(chr(10),' '))
"
rm -f $d/meta.json
