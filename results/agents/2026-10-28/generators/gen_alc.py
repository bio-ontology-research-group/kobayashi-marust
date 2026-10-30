import random,sys
def gen(seed):
    R=random.Random(seed)
    C=['A','B','C','D']; Q=['Q1','Q2','Q3']; OP=['r','s','t']
    def role():
        p=R.choice(OP)
        return f'ObjectInverseOf(:{p})' if R.random()<.2 else f':{p}'
    def cls(d=0):
        k=R.randrange(10 if d<2 else 3)
        if k<3: return ':'+R.choice(C)
        if k==3: return f'ObjectSomeValuesFrom({role()} {cls(d+1)})'
        if k==4: return f'ObjectAllValuesFrom({role()} {cls(d+1)})'
        if k==5: return f'ObjectComplementOf({cls(d+1)})'
        if k==6: return f'ObjectIntersectionOf({cls(d+1)} {cls(d+1)})'
        if k==7: return f'ObjectUnionOf({cls(d+1)} {cls(d+1)})'
        if k==8:
            n=R.randrange(0,3); kind=R.choice(['ObjectMinCardinality','ObjectMaxCardinality'])
            return f'{kind}({n} {role()} {cls(d+1)})'
        return f'ObjectUnionOf({cls(d+1)} ObjectComplementOf({cls(d+1)}))'
    ax=[]
    for _ in range(R.randrange(3,9)):
        k=R.randrange(10)
        if k<5: ax.append(f'SubClassOf({cls()} {cls()})')
        elif k==5: ax.append(f'SubClassOf(owl:Thing {cls()})')
        elif k==6: ax.append(f'DisjointClasses({cls()} {cls()})')
        elif k==7: ax.append(f'SubObjectPropertyOf(:{R.choice(OP)} :{R.choice(OP)})')
        elif k==8: ax.append(f'FunctionalObjectProperty(:{R.choice(OP)})')
        else: ax.append(f'EquivalentClasses(:{R.choice(C)} {cls()})')
    for q in Q: ax.append(f'EquivalentClasses(:{q} {cls()})')
    decl=' '.join([f'Declaration(Class(:{c}))' for c in C+Q]+[f'Declaration(ObjectProperty(:{p}))' for p in OP])
    return f'Prefix(:=<http://example.org/g#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nOntology(<http://example.org/g>\n{decl}\n'+'\n'.join(ax)+'\n)\n'
if __name__=='__main__':
    open(sys.argv[2],'w').write(gen(int(sys.argv[1])))
