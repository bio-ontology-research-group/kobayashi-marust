import sys,collections,statistics
def load(p):
    d={}
    for l in open(p):
        f=l.rstrip('\n').split('\t')
        if len(f)>=4: d[f[0].split('/')[-1]]=(f[2],float(f[3]))
    return d
names=sys.argv[1::2]; paths=sys.argv[2::2]
ds=[load(p) for p in paths]
keys=set(ds[0]);
for d in ds[1:]: keys&=set(d)
print('common',len(keys))
for n,d in zip(names,ds):
    c=collections.Counter(d[k][0] for k in keys); print(n,dict(c), 'wrong:',sorted(k for k in keys if d[k][0]=='WRONG'))
a=ds[0]
for n,d in zip(names[1:],ds[1:]):
    both=[k for k in keys if a[k][0]=='ok' and d[k][0]=='ok']
    ta=sum(a[k][1] for k in both); tb=sum(d[k][1] for k in both)
    r=[d[k][1]/max(a[k][1],0.01) for k in both]
    print(f'{names[0]} vs {n}: both ok {len(both)}, total {ta:.0f} vs {tb:.0f} s (ratio {tb/max(ta,1e-9):.2f}), median ratio {statistics.median(r):.2f}; only {names[0]} {sum(1 for k in keys if a[k][0]=="ok" and d[k][0]!="ok")}, only {n} {sum(1 for k in keys if d[k][0]=="ok" and a[k][0]!="ok")}')
