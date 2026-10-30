#!/bin/bash
# chk.sh KM FILE... : per route, compare with cached HermiT (gold json next to file or in r3 gold dir)
K=$1; shift
G=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/gold
for f in "$@"; do
  stem=$(basename $f .ofn); stem=${stem#open_}
  gold=$G/$stem.json; [ -f ${f%.ofn}.hermit.json ] && gold=${f%.ofn}.hermit.json; [ -f ${f%.ofn}.json ] && gold=${f%.ofn}.json
  for r in nominals auto certified_nominals; do
    s=$(date +%s.%N)
    if [ $r = auto ]; then out=$(env -u KM_ROUTE timeout ${CHK_T:-60} $K classify --lines $f 2>/dev/null); else out=$(KM_ROUTE=$r timeout ${CHK_T:-60} $K classify --lines $f 2>/dev/null); fi
    rc=$?; t=$(echo "$(date +%s.%N)-$s" | bc)
    v=$(python3 -I -c "
import json,sys
g=json.load(open('$gold')); s=lambda n:n.lstrip(':').split('#')[-1]
uns={s(c) for c in g['unsatisfiable']}
gs={(s(a),s(b)) for a,b in g['subsumptions'] if s(a) not in uns and s(b) not in uns and a!=b}
ks=set();ku=set();cons=None
for l in sys.stdin.read().splitlines():
  t=l.split('\t')
  if t[0].startswith('CONSISTENT'): cons=t[0].endswith('1')
  elif t[0]=='SUB' and len(t)==3: ks.add((s(t[1]),s(t[2])))
  elif t[0]=='UNSAT': ku.add(s(t[1]))
ks={x for x in ks if x[0] not in ku and x[1] not in ku and x[0]!=x[1] and 'Thing' not in x[1]}
if cons is None: print('ERR'); sys.exit()
print('ok' if (ks==gs and ku==uns and cons==g['consistent']) else 'WRONG miss=%s extra=%s'%(sorted(gs-ks),sorted(ks-gs)))
" <<< "$out")
    printf "%s\t%s\trc=%s\t%.2f\t%s\n" $stem $r $rc $t "$v"
  done
done
