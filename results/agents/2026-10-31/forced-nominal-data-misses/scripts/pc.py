import json,sys
d=json.load(open(sys.argv[1]))
def t(x):
    k=x['kind']
    if k in('var','ind'): return x['name'].split('#')[-1]
    if k=='fun': return x.get('name',x.get('fun','f'))+'('+','.join(t(a) for a in x.get('args',[]))+')'
    if k=='aux': return 'aux'+str(x.get('name',x))
    return json.dumps(x)
def a(x):
    k=x['kind']
    if k=='concept': return x['concept'].split('#')[-1]+'('+t(x['term'])+')'
    if k=='role': return x['role'].split('#')[-1]+'('+t(x['source'])+','+t(x['target'])+')'
    if k=='eq': return t(x['left'])+'='+t(x['right'])
    if k=='neq': return t(x['left'])+'!='+t(x['right'])
    return json.dumps(x)
for c in d['clauses']:
    print(' & '.join(a(x) for x in c['body']),'->',' | '.join(a(x) for x in c['head']))
