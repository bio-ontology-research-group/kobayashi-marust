import json,sys
src,dst,mode=sys.argv[1:4]
d=json.load(open(src)); C=d['concepts']
D=C.index('__data__')
def isD(a): return a['k']=='c' and a['c']==D
out=[]
for cl in d['clauses']:
    bD=any(isD(a) for a in cl['body']); hD=any(isD(a) for a in cl['head'])
    if mode=='nodisj':   # drop __data__ disjunct from multi-head clauses
        if hD and len(cl['head'])>1:
            cl=dict(cl); cl['head']=[a for a in cl['head'] if not isD(a)]
    elif mode=='nosort':  # drop every clause mentioning __data__, fix disjunctions
        if hD and len(cl['head'])>1:
            cl=dict(cl); cl['head']=[a for a in cl['head'] if not isD(a)]
        elif bD or hD: continue
    elif mode=='nodisjoint': # drop C∧D→⊥ only
        if bD and not cl['head'] and len(cl['body'])==2 and all(a['k']=='c' for a in cl['body']): continue
    elif mode=='norole': # drop R∧D→⊥
        if bD and not cl['head'] and any(a['k']=='r' for a in cl['body']): continue
    out.append(cl)
print(len(d['clauses']),'->',len(out))
d['clauses']=out
json.dump(d,open(dst,'w'))
