import json,sys,collections
def load(p):
    d=json.load(open(p)); C=d['concepts']; Rl=d['roles']
    def atom(x):
        x=dict(x)
        if 'c' in x: x['c']=C[x['c']]
        if 'r' in x and isinstance(x['r'],int): x['r']=Rl[x['r']]
        return json.dumps(x,sort_keys=True)
    out=collections.Counter()
    for cl in d['clauses']:
        out[(tuple(sorted(atom(a) for a in cl['body'])),tuple(sorted(atom(a) for a in cl['head'])))]+=1
    return d,out
a,ca=load(sys.argv[1]); b,cb=load(sys.argv[2])
extra=cb-ca; miss=ca-cb
print('extra',sum(extra.values()),'missing',sum(miss.values()))
shape=collections.Counter()
for (bd,hd),n in extra.items():
    shape[(len(bd),len(hd),tuple(sorted(json.loads(x)['k'] for x in bd)),tuple(sorted(json.loads(x)['k'] for x in hd)))]+=n
for s,n in shape.most_common(): print(n,s)
for i,((bd,hd),n) in enumerate(extra.items()):
    if i<12: print(n,bd,'->',hd)
for i,((bd,hd),n) in enumerate(miss.items()):
    if i<5: print('MISS',n,bd,'->',hd)
