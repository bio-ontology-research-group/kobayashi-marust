import json,re,sys
def internal(n):
    s=re.split('[#/]',n)[-1]
    if s.startswith('Q_'): return s[2:].isdigit() and len(s)>2
    return s.startswith(('__','_aux','aux_','def_'))
d=json.load(sys.stdin)
ind=False; on=False
for c in d['clauses']:
    con=0; intl=False
    for a in c['head']:
        if a['kind']=='concept':
            con+=1; intl|=internal(a['concept'])
    if con>=2 and intl: on=True
    for a in c['body']+c['head']:
        ts=[a['term']] if a['kind']=='concept' else ([a['source'],a['target']] if a['kind']=='role' else [a['left'],a['right']])
        if any(t['kind']=='ind' for t in ts): ind=True
print(int(ind), int(on))
