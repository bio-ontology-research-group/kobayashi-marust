import csv, random, sys
rows=list(csv.DictReader(open('/mnt/data1/leechuck/km-work/v170/reports/census-per-input.tsv'),delimiter='\t'))
def n(r,k): return int(r.get(k) or 0)
def inds(r): return n(r,'ClassAssertion')+n(r,'ObjectPropertyAssertion')+n(r,'DataPropertyAssertion')+n(r,'SameIndividual')+n(r,'DifferentIndividuals')>0
def dprop(r): return any(n(r,k)>0 for k in ['DataSomeValuesFrom','DataAllValuesFrom','DataHasValue','DataPropertyDomain','DataPropertyRange','DataPropertyAssertion','SubDataPropertyOf','FunctionalDataProperty','DisjointDataProperties','EquivalentDataProperties','DataMinCardinality','DataMaxCardinality','DataExactCardinality'])
def rules(r): return n(r,'DLSafeRule')>0
def inv(r): return n(r,'ObjectInverseOf')>0 or n(r,'InverseObjectProperties')>0
cand=[r for r in rows if r['admission']=='checks_passed' and 30000<=n(r,'bytes')<=2000000 and n(r,'classes')>=10]
print(len(cand),file=sys.stderr)
quota={'EL':7,'ALC':2,'SHI':6,'SHIQ':6,'SHIQ+ABox':7,'SHOIQ':7,'SROIQ':5}
random.seed(170)
chosen=[]
for f,q in quota.items():
    pool=[r for r in cand if r['fragment']==f]
    random.shuffle(pool)
    # prefer variety of features: sort by feature score stable after shuffle
    pool.sort(key=lambda r: -(inds(r)+dprop(r)+inv(r)) if f in('SHIQ+ABox','SHOIQ','SROIQ','SHI','SHIQ') else 0)
    chosen+=pool[:q]
    if '--round2' not in sys.argv:
        print(f,len(pool),file=sys.stderr)
if '--round2' in sys.argv:
    r1={r['ontology'] for r in chosen}
    cand2=[r for r in cand if r['ontology'] not in r1 and (inds(r) or dprop(r) or rules(r))]
    quota2={'EL':4,'SHIQ':6,'SHIQ+ABox':14,'SHOIQ':10,'SROIQ':6}
    random.seed(171)
    chosen=[]
    for f,q in quota2.items():
        pool=[r for r in cand2 if r['fragment']==f]
        random.shuffle(pool)
        pool.sort(key=lambda r: -(2*rules(r)+inds(r)+dprop(r)+inv(r)))
        chosen+=pool[:q]
        print(f,len(pool),file=sys.stderr)
print('ind',sum(inds(r) for r in chosen),'dprop',sum(dprop(r) for r in chosen),'rules',sum(rules(r) for r in chosen),'inv',sum(inv(r) for r in chosen),file=sys.stderr)
for r in chosen:
    print('/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/%s.owl'%r['ontology'])
    print(r['ontology'],r['fragment'],r['bytes'],r['classes'],'I' if inds(r) else '-','D' if dprop(r) else '-','R' if rules(r) else '-','V' if inv(r) else '-',file=sys.stderr)
