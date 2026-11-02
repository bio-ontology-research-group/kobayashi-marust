import json,sys,collections
t=json.load(open(sys.argv[1])); C=t['concepts']; R=t['roles']
target=sys.argv[2]; ids={i for i,n in enumerate(C) if n==target}
def nm(a):
    k=a.get('k')
    if k=='c': return ('¬' if a.get('neg') else '')+C[a['c']]+f"(x{a['t']})"
    if k=='r': return f"{R[a['r']]}(x{a['s']},x{a['t']})"
    if k=='e': return f"∃{R[a['r']]}.{'¬' if a.get('neg') else ''}{C[a['c']]}(x{a['t']})"
    return json.dumps(a)
shapes=collections.Counter(); ex={}
n=0
for c in t['clauses']:
    if any(a.get('c') in ids for a in c['body']+c['head']):
        s=' ∧ '.join(map(nm,c['body']))+' → '+' ∨ '.join(map(nm,c['head']))
        n+=1
        if n<=int(sys.argv[3]) : print(s[:300])
print('total',n, 'query?', any(q in ids for q in t['queries']) if t['queries'] and isinstance(t['queries'][0],int) else t['queries'][:3])
for k in ['definers','source_axioms']:
    for d in t.get(k,[]):
        if target in json.dumps(d): print(k, json.dumps(d)[:300])
