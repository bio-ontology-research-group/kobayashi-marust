#!/bin/bash
# usage: probe.sh KM_BIN  -- compare each p2/*.ofn against its .hermit.json on 5 configurations
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-inverse-top; KM=$1; cd $S/p2
norm(){ python3 -c "
import json,sys
d=json.load(open(sys.argv[1])); u=sorted(d['unsatisfiable']); s=sorted(a+'<'+b for a,b in d['subsumptions'] if a!=b and a not in u and b not in u)
print(('C' if d['consistent'] else 'INC'),'U='+','.join(u),'S='+','.join(s))" $1; }
kmn(){ python3 -c "
import sys
c=None;u=[];s=[]
for l in sys.stdin:
  t=l.rstrip().split('\t')
  if t[0].startswith('CONSISTENT'): c=t[0].endswith('1')
  elif t[0]=='UNSAT': u.append(t[1].lstrip(':'))
  elif t[0]=='SUB': s.append((t[1].lstrip(':'),t[2].lstrip(':')))
if c is None: print('NOANSWER'); sys.exit()
u=sorted(u); ss=sorted(a+'<'+b for a,b in s if a!=b and a not in u and b not in u)
print(('C' if c else 'INC'),'U='+','.join(u),'S='+','.join(ss))"; }
for f in *.ofn; do m=${f%.ofn}; g=$(norm $m.hermit.json); echo "== $m gold: $g"
 for cfg in "ht_bridge|" "ht_bridge|KM_NO_SOURCE_TBOX=1" "ht_bridge|KM_HT_NO_SATURATION=1" "ht_bridge|KM_NO_SOURCE_TBOX=1 KM_HT_NO_SATURATION=1" "auto|" "cb_plain1|"; do r=${cfg%|*}; e=${cfg#*|}; o=$(env $e timeout 60 $KM classify --lines --route $r $f 2>/dev/null | kmn); [ "$o" = "$g" ] && v=ok || v="DIFF: $o"; echo "   $r $e: $v"; done; done
