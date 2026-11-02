import json,sys,re,collections
t=json.load(open(sys.argv[1]))
C=t['concepts']; cl=t['clauses']
AUX='__dt__aux__'
def nm(a):
    if a.get('k')=='c': return ('¬' if a.get('neg') else '')+C[a['c']]+f"(x{a['t']})"
    return json.dumps(a)
shapes=collections.Counter(); ex={}
for c in cl:
    b,h=c['body'],c['head']
    if not any(a.get('k')=='c' and C[a['c']].startswith(AUX) for a in b+h): continue
    names=[nm(a) for a in b]+['->']+[nm(a) for a in h]
    k=tuple(re.sub(r'__[^_(]{6,}','__V',re.sub(r'[0-9]+','N',n))[:50] for n in names)
    shapes[k]+=1; ex.setdefault(k,names)
for k,v in shapes.most_common(40): print(v,[s[:110] for s in ex[k]])
