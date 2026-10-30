import json,sys
def t(x):
    k=x['kind']
    if k=='var': return x['name']
    if k in('ind','individual','const'): return x.get('name',str(x))
    if k=='fn' or k=='func': return x.get('name','f')+'('+','.join(t(a) for a in x.get('args',[]))+')'
    return json.dumps(x)
def a(x):
    k=x['kind']
    if k=='concept': return f"{x['concept']}({t(x['term'])})"
    if k=='role': return f"{x['role']}({t(x['source'])},{t(x['target'])})"
    if k=='eq': return f"{t(x['left'])}={t(x['right'])}"
    return json.dumps(x)
d=json.load(open(sys.argv[1]))
for c in d['clauses']:
    print(' & '.join(a(x) for x in c['body']) + ' -> ' + (' | '.join(a(x) for x in c['head']) or 'F'))
print({k:(v if len(json.dumps(v))<400 else '...') for k,v in d.items() if k!='clauses'})
