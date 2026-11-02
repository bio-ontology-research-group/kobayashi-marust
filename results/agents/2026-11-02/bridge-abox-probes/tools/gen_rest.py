"""Seed families that stress the restricted automaton re-fire
(KM_HT_AUTOMAT_REST_LINK): run-time merges that relocate links while
universal restrictions over complex roles (transitive roles, property
chains, inverses) are armed on the endpoints.

family 0  merges under transitive roles and chains: a functional role f
          below the transitive t (or inside a chain), two f-successors
          (named or anonymous) that must merge, universal restrictions over
          t / u / inverses on the predecessors and on the merged nodes.
family 1  nominal merges: anonymous f-successors forced onto a nominal
          (ObjectSomeValuesFrom(f ObjectOneOf(a)) with functional f, or
          {a} subsumptions), universal restrictions reaching the nominal
          through chains.
family 2  at-most merges relocating links: ObjectMaxCardinality(1 r)
          (qualified and unqualified) with several r-successors, the
          successors carrying their own outgoing chain edges, inverse
          functional roles merging predecessors.
family 3  hub merges: a hub with many asserted edges under an at-most
          restriction that merges ABox individuals, plus
          DifferentIndividuals that can make it inconsistent.

usage: python3 -I gen_rest.py SEED OUT.ofn   (family = SEED mod 4)
"""
import random
import sys


def gen(seed):
    R = random.Random(seed * 7919 + 13)
    fam = seed % 4
    n = R.randint(4, 10)
    IND = [f'i{k}' for k in range(n)]
    C = ['A', 'B', 'C', 'D', 'E']
    Q = ['Q1', 'Q2', 'Q3', 'Q4', 'Q5']
    ax = ['TransitiveObjectProperty(:t)',
          'SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)',
          'SubObjectPropertyOf(:f :r)' if R.random() < .5 else 'SubObjectPropertyOf(:f :t)']
    if R.random() < .6:
        ax.append('SubObjectPropertyOf(ObjectPropertyChain(:s :f) :u)')
    if R.random() < .5:
        ax.append('TransitiveObjectProperty(:u)')
    if R.random() < .5:
        ax.append('InverseObjectProperties(:s :si)')
    if R.random() < .4:
        ax.append('SubObjectPropertyOf(:g :t)')
    if fam in (0, 1) or R.random() < .5:
        ax.append('FunctionalObjectProperty(:f)')
    if fam == 2 or R.random() < .3:
        ax.append('InverseFunctionalObjectProperty(:g)')
    if R.random() < .3:
        ax.append('DisjointClasses(:A :B)')
    if R.random() < .2:
        ax.append('DisjointClasses(:C :E)')

    def role(cplx=None):
        if cplx is None:
            cplx = R.random() < .6
        name = R.choice(['t', 'u'] if cplx else ['r', 's', 'f', 'g', 'si'])
        if R.random() < .25:
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

    def edge(p, x, y):
        ax.append(f'ObjectPropertyAssertion(:{p} :{x} :{y})')

    for _ in range(R.randint(2, 6)):
        x, y = R.sample(IND, 2)
        edge(R.choice(['r', 's', 'g', 't']), x, y)
    if fam == 0:
        for _ in range(R.randint(1, 3)):
            x, y, z = R.sample(IND, 3)
            edge('f', x, y)
            if R.random() < .6:
                edge('f', x, z)
            else:
                ax.append(f'SubClassOf(ObjectOneOf(:{x}) ObjectSomeValuesFrom(:f {atom()}))')
            edge('s', y, R.choice(IND))
        ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom(:f ObjectSomeValuesFrom(:s {atom()})))')
    elif fam == 1:
        for _ in range(R.randint(1, 3)):
            a = R.choice(IND)
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom(:f ObjectOneOf(:{a})))')
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom(:f {atom()}))')
        if R.random() < .5:
            a, b = R.sample(IND, 2)
            ax.append(f'SubClassOf(ObjectOneOf(:{a}) ObjectOneOf(:{b} :{R.choice(IND)}))')
        x = R.choice(IND)
        ax.append(f'ClassAssertion({atom()} :{x})')
        edge('f', x, R.choice(IND))
    elif fam == 2:
        ax.append(f'SubClassOf({atom()} ObjectMaxCardinality(1 :r))')
        if R.random() < .5:
            ax.append(f'SubClassOf({atom()} ObjectMaxCardinality(1 :s {atom()}))')
        for _ in range(R.randint(1, 3)):
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom(:r {filler(1)}))')
        x = R.choice(IND)
        ax.append(f'ClassAssertion({atom()} :{x})')
        for y in R.sample(IND, R.randint(1, 3)):
            if y != x:
                edge(R.choice(['r', 'f']), x, y)
                edge('s', y, R.choice(IND))
        for _ in range(R.randint(1, 2)):
            x, y, z = R.sample(IND, 3)
            edge('g', x, z)
            edge('g', y, z)
    else:
        h = R.choice(IND)
        ax.append(f'ClassAssertion(ObjectMaxCardinality({R.randint(1, 2)} :r) :{h})')
        for o in R.sample(IND, R.randint(2, n - 1)):
            if o != h:
                edge('r', h, o)
                if R.random() < .5:
                    edge('s', o, R.choice(IND))
        if R.random() < .4:
            x, y = R.sample(IND, 2)
            ax.append(f'DifferentIndividuals(:{x} :{y})')
    for _ in range(R.randint(0, 1)):
        ax.append('SameIndividual(' + ' '.join(':' + i for i in R.sample(IND, 2)) + ')')
    for _ in range(R.randint(2, 4)):
        x = R.choice(IND)
        if R.random() < .4:
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
        k = R.randrange(5)
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom({role(True)} ObjectOneOf({ind()})))')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{q} ObjectAllValuesFrom({role(True)} {atom()}))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} ObjectSomeValuesFrom(:f {atom()})))')
        elif k == 3:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom({role()} ObjectAllValuesFrom({role(True)} {atom()})))')
        else:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} ObjectMaxCardinality(1 :r)))')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    decl = [f'Declaration(Class(:{c}))' for c in C + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in ['r', 's', 't', 'u', 'f', 'g', 'si']]
    decl += [f'Declaration(NamedIndividual(:{i}))' for i in IND]
    return ('Prefix(:=<http://x#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'
            'Ontology(<http://x/m' + str(seed) + '>\n' + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    with open(sys.argv[2], 'w') as f:
        f.write(gen(int(sys.argv[1])))
