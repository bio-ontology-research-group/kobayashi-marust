import json,sys
src,dst=sys.argv[1:3]
d=json.load(open(src)); C=d['concepts']
D=C.index('__data__')
isD=lambda a: a['k']=='c' and a['c']==D
poly=set()
for cl in d['clauses']:
    if len(cl['head'])==2 and any(isD(a) for a in cl['head']):
        poly |= {a['c'] for a in cl['head'] if not isD(a)}
print('poly',[C[i] for i in poly])
out=[]
for cl in d['clauses']:
    if len(cl['head'])==2 and any(isD(a) for a in cl['head']):
        cl=dict(cl); cl['head']=[a for a in cl['head'] if not isD(a)]
    elif not cl['head'] and len(cl['body'])==2 and any(isD(a) for a in cl['body']) and any(a['k']=='c' and a['c'] in poly for a in cl['body']):
        continue
    out.append(cl)
print(len(d['clauses']),'->',len(out)); d['clauses']=out; json.dump(d,open(dst,'w'))
