import json,sys
d=json.load(open(sys.argv[1]))
def t(x):
  k=x['kind']
  if k in('var','ind','aux'): return x.get('name','?')
  if k=='fun': return x['function']+'('+t(x['arg'])+')'
  return str(x)
def f(a):
  k=a['kind']
  if k=='concept': return a['concept']+'('+t(a['term'])+')'
  if k=='role': return a['role']+'('+t(a['source'])+','+t(a['target'])+')'
  return 'EQ('+','.join(t(v) for kk,v in a.items() if kk!='kind')+')'
for c in d['clauses']: print(' & '.join(map(f,c['body'])),'->',' | '.join(map(f,c['head'])))
print({k:v for k,v in d.items() if k!='clauses'})
