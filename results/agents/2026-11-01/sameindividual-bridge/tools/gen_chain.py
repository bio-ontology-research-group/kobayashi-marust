"""Random small ABox ontologies around complex roles: a transitive role t,
a property chain r o s <= t (and sometimes s o r <= u), inverses, universal
restrictions over the complex roles (as TBox axioms and as class
assertions), hub individuals with many asserted edges, SameIndividual
classes, nominals in the TBox and disjointness that can make the ABox
inconsistent. Query classes expose the propagated labels.

usage: python3 -I gen_chain.py SEED OUT.ofn
"""
import random
import sys


def gen(seed):
    R = random.Random(seed)
    n = R.randint(5, 12)
    IND = [f'i{k}' for k in range(n)]
    C = ['A', 'B', 'C', 'D', 'E']
    Q = ['Q1', 'Q2', 'Q3', 'Q4']
    simple = ['r', 's', 'p']
    complex_ = ['t', 'u']
    ax = ['TransitiveObjectProperty(:t)',
          'SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)']
    if R.random() < .5:
        ax.append('SubObjectPropertyOf(ObjectPropertyChain(:s :r) :u)')
    if R.random() < .4:
        ax.append('TransitiveObjectProperty(:u)')
    if R.random() < .4:
        ax.append('SubObjectPropertyOf(:p :t)')
    if R.random() < .3:
        ax.append('InverseObjectProperties(:p :q)')
    if R.random() < .3:
        ax.append('DisjointClasses(:A :B)')
    if R.random() < .2:
        ax.append('DisjointClasses(:C :E)')

    def role(cplx=None):
        if cplx is None:
            cplx = R.random() < .5
        name = R.choice(complex_ if cplx else simple + ['q'])
        if R.random() < .2:
            return f'ObjectInverseOf(:{name})'
        return f':{name}'

    def atom():
        return ':' + R.choice(C)

    def ind():
        return ':' + R.choice(IND)

    def filler(d=0):
        k = R.randrange(6 if d < 1 else 3)
        if k < 2:
            return atom()
        if k == 2:
            return 'ObjectOneOf(' + ind() + ')'
        if k == 3:
            return f'ObjectUnionOf({filler(d + 1)} {filler(d + 1)})'
        if k == 4:
            return f'ObjectAllValuesFrom({role(True)} {filler(d + 1)})'
        return f'ObjectSomeValuesFrom({role()} {filler(d + 1)})'

    # hubs and paths
    hubs = R.sample(IND, R.randint(1, 2))
    for h in hubs:
        for o in R.sample(IND, R.randint(2, min(8, n - 1))):
            if o != h:
                ax.append(f'ObjectPropertyAssertion(:{R.choice(simple)} :{h} :{o})')
    for _ in range(R.randint(2, 6)):
        x, y = R.sample(IND, 2)
        ax.append(f'ObjectPropertyAssertion(:{R.choice(simple)} :{x} :{y})')
    for _ in range(R.randint(0, 2)):
        k = R.randint(2, 3)
        ax.append('SameIndividual(' + ' '.join(':' + i for i in R.sample(IND, k)) + ')')
    if R.random() < .2:
        x, y = R.sample(IND, 2)
        ax.append(f'DifferentIndividuals(:{x} :{y})')
    if R.random() < .2:
        x, y = R.sample(IND, 2)
        ax.append(f'NegativeObjectPropertyAssertion(:t :{x} :{y})')
    for _ in range(R.randint(2, 5)):
        x = R.choice(IND)
        if R.random() < .5:
            ax.append(f'ClassAssertion({atom()} :{x})')
        else:
            ax.append(f'ClassAssertion(ObjectAllValuesFrom({role(True)} {filler(1)}) :{x})')
    for _ in range(R.randint(2, 5)):
        k = R.randrange(4)
        if k == 0:
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({role(True)} {filler(1)}))')
        elif k == 1:
            ax.append(f'SubClassOf(ObjectSomeValuesFrom({role()} {atom()}) {atom()})')
        elif k == 2:
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role(False)} {atom()}))')
        else:
            ax.append(f'SubClassOf(ObjectOneOf({ind()}) {filler()})')
    for q in Q:
        k = R.randrange(4)
        o = ind()
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectOneOf({o}))')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom({role(True)} ObjectOneOf({o})))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} ObjectSomeValuesFrom({role()} {atom()})))')
        else:
            ax.append(f'EquivalentClasses(:{q} ObjectAllValuesFrom({role(True)} {atom()}))')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    decl = [f'Declaration(Class(:{c}))' for c in C + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in simple + complex_ + ['q']]
    decl += [f'Declaration(NamedIndividual(:{i}))' for i in IND]
    return ('Prefix(:=<http://x#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'
            'Ontology(<http://x/c' + str(seed) + '>\n' + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    with open(sys.argv[2], 'w') as f:
        f.write(gen(int(sys.argv[1])))
