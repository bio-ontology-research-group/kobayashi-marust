import sys,random,itertools
src=open(sys.argv[1]).read().splitlines()
n=int(sys.argv[2]); out=sys.argv[3]
head=[l for l in src if l.startswith(('Prefix','Ontology','Declaration'))]
ax=[l for l in src if l and not l.startswith(('Prefix','Ontology','Declaration',')'))]
R=random.Random(1)
seen=set()
for k in range(n):
    p=ax[:]; R.shuffle(p)
    open(f'{out}_{k}.ofn','w').write('\n'.join(head+p+[')'])+'\n')
