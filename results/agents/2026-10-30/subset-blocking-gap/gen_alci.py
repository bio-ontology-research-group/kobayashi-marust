# usage: python3 -I gen_alci.py SEED OUT.ofn
# Nominal-free ALCI generator around the subset-blocking pattern: existentials
# and universals over inverse roles, so that an existential can be satisfied
# through the inverse edge to the predecessor, and disjunctions / excluded
# middles so that blocker and blocked labels differ.
import random, sys
def gen(seed):
    R = random.Random(seed)
    C = ['A', 'B', 'C', 'D', 'E']; Q = ['Q1', 'Q2', 'Q3']; OP = ['r', 's']
    def role(pinv=.5):
        p = R.choice(OP)
        return f'ObjectInverseOf(:{p})' if R.random() < pinv else f':{p}'
    def atom():
        c = ':' + R.choice(C)
        return f'ObjectComplementOf({c})' if R.random() < .2 else c
    def cls(d=0):
        k = R.randrange(9 if d < 2 else 2)
        if k < 2: return atom()
        if k in (2, 3): return f'ObjectSomeValuesFrom({role()} {cls(d+1)})'
        if k == 4: return f'ObjectAllValuesFrom({role()} {cls(d+1)})'
        if k == 5: return f'ObjectIntersectionOf({cls(d+1)} {cls(d+1)})'
        if k == 6: return f'ObjectUnionOf({cls(d+1)} {cls(d+1)})'
        if k == 7: return f'ObjectComplementOf({cls(d+1)})'
        return f'ObjectUnionOf({atom()} ObjectComplementOf({cls(d+1)}))'
    ax = []
    # Pattern axioms: A ⊑ ∃u.C witnessed through the predecessor.
    if R.random() < .7:
        u = role(.5); a = R.choice(C); c = R.choice(C)
        ax.append(f'SubClassOf(:{a} ObjectSomeValuesFrom({u} :{c}))')
    if R.random() < .6:
        u = role(.5); ax.append(f'SubClassOf({cls(1)} ObjectAllValuesFrom({u} {cls(1)}))')
    for _ in range(R.randrange(2, 7)):
        k = R.randrange(10)
        if k < 6: ax.append(f'SubClassOf({cls()} {cls()})')
        elif k < 8: ax.append(f'SubClassOf(owl:Thing {cls()})')
        elif k == 8: ax.append(f'DisjointClasses({cls()} {cls()})')
        else: ax.append(f'EquivalentClasses(:{R.choice(C)} {cls()})')
    for q in Q: ax.append(f'EquivalentClasses(:{q} {cls()})')
    decl = ' '.join([f'Declaration(Class(:{c}))' for c in C + Q] + [f'Declaration(ObjectProperty(:{p}))' for p in OP])
    return ('Prefix(:=<http://example.org/g#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'
            'Ontology(<http://example.org/g>\n' + decl + '\n' + '\n'.join(ax) + '\n)\n')
if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
