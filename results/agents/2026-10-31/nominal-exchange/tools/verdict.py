import json,sys
g=json.load(open(sys.argv[1])); s=lambda n:n.lstrip(':').split('#')[-1]
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
if cons is False and g['consistent'] is False: print('ok'); sys.exit()
print('ok' if (ks==gs and ku==uns and cons==g['consistent']) else 'WRONG miss=%s extra=%s'%(sorted(gs-ks),sorted(ks-gs)))
