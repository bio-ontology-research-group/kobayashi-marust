"""Random small nominal ontologies around the bridge merge defect
(bridge_merge_min.ofn, r2730, r3086): individuals that are merged by a
nominal subsumption between enumerations, by an enumeration assertion, or by
a functional role, with role assertions among the merged individuals and
universal / existential restrictions on one of them. Query classes
Qi = {o} or Qi <= {o} expose the merged individuals' labels in the taxonomy.

usage: python3 -I gen_merge.py SEED OUT.ofn [--no-inverse]

No axiom is repeated (the bridge refuses repeated assertions).
"""
import random
import sys


def gen(seed, inverse=True):
    R = random.Random(seed)
    n_ind = R.randint(3, 5)
    IND = ['a', 'b', 'c', 'd', 'e'][:n_ind]
    C = ['A', 'B', 'C', 'D', 'E']
    OP = ['r', 's', 't']
    Q = ['Q1', 'Q2', 'Q3']

    def role():
        p = R.choice(OP)
        if inverse and R.random() < .1:
            return f'ObjectInverseOf(:{p})'
        return f':{p}'

    def atom():
        return ':' + R.choice(C)

    def ind():
        return ':' + R.choice(IND)

    def nom(k=None):
        k = k or R.choice([1, 2, 2, 3])
        k = min(k, len(IND))
        return 'ObjectOneOf(' + ' '.join(':' + i for i in R.sample(IND, k)) + ')'

    def filler(d=0):
        k = R.randrange(6 if d < 1 else 3)
        if k < 2:
            return atom()
        if k == 2:
            return nom()
        if k == 3:
            return f'ObjectUnionOf({filler(d + 1)} {filler(d + 1)})'
        if k == 4:
            return f'ObjectAllValuesFrom({role()} {filler(d + 1)})'
        return f'ObjectSomeValuesFrom({role()} {filler(d + 1)})'

    ax = []
    # merge sources (at least one)
    for _ in range(R.randint(1, 3)):
        k = R.randrange(6)
        x, y = R.sample(IND, 2)
        if k == 0:
            ax.append(f'SubClassOf(ObjectOneOf(:{x} :{y}) ObjectOneOf(:{x}))')
        elif k == 1:
            z = R.choice(IND)
            ax.append(f'SubClassOf({nom(2)} {nom(R.choice([1, 2]))})')
        elif k == 2:
            ax.append(f'ClassAssertion({nom(R.choice([1, 2]))} :{x})')
        elif k == 3:
            p = R.choice(OP)
            ax.append(f'FunctionalObjectProperty(:{p})')
            z = R.choice(IND)
            ax.append(f'ObjectPropertyAssertion(:{p} :{z} :{x})')
            ax.append(f'ObjectPropertyAssertion(:{p} :{z} :{y})')
        elif k == 4:
            p = R.choice(OP)
            ax.append(f'InverseFunctionalObjectProperty(:{p})' if inverse else f'FunctionalObjectProperty(:{p})')
            z = R.choice(IND)
            if inverse:
                ax.append(f'ObjectPropertyAssertion(:{p} :{x} :{z})')
                ax.append(f'ObjectPropertyAssertion(:{p} :{y} :{z})')
            else:
                ax.append(f'ObjectPropertyAssertion(:{p} :{z} :{x})')
                ax.append(f'ObjectPropertyAssertion(:{p} :{z} :{y})')
        else:
            ax.append(f'ClassAssertion(ObjectMaxCardinality(1 {role()}) :{x})')
    # role assertions among individuals
    for _ in range(R.randint(1, 4)):
        ax.append(f'ObjectPropertyAssertion({R.choice([":" + p for p in OP])} {ind()} {ind()})')
    # restrictions on individuals
    for _ in range(R.randint(1, 3)):
        k = R.randrange(5)
        if k == 0:
            ax.append(f'ClassAssertion(ObjectAllValuesFrom({role()} {filler(1)}) {ind()})')
        elif k == 1:
            ax.append(f'ClassAssertion(ObjectSomeValuesFrom({role()} {filler(1)}) {ind()})')
        elif k == 2:
            ax.append(f'ClassAssertion(ObjectUnionOf({nom(1)} {atom()}) {ind()})')
        elif k == 3:
            ax.append(f'ClassAssertion({atom()} {ind()})')
        else:
            ax.append(f'ClassAssertion(ObjectMaxCardinality(1 {role()} {atom()}) {ind()})')
    # TBox noise
    for _ in range(R.randint(0, 3)):
        k = R.randrange(5)
        if k == 0:
            ax.append(f'SubClassOf({atom()} ObjectMaxCardinality(1 {role()} {atom()}))')
        elif k == 1:
            ax.append(f'SubClassOf(ObjectSomeValuesFrom({role()} {atom()}) {atom()})')
        elif k == 2:
            ax.append(f'SubClassOf({atom()} {atom()})')
        elif k == 3:
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({role()} {atom()}))')
        else:
            ax.append(f'SubClassOf({atom()} {filler()})')
    # query classes
    for q in R.sample(Q, R.randint(1, 3)):
        if R.random() < .6:
            ax.append(f'EquivalentClasses(:{q} {nom(1)})')
        else:
            ax.append(f'SubClassOf(:{q} {nom(1)})')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    R.shuffle(ax)
    out = ['Prefix(:=<http://example.org/r3#>)', 'Ontology(<http://example.org/r3>']
    out += [f'Declaration(Class(:{c}))' for c in C + Q]
    out += [f'Declaration(ObjectProperty(:{p}))' for p in OP]
    out += [f'Declaration(NamedIndividual(:{i}))' for i in IND]
    out += ax + [')']
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    seed, path = int(sys.argv[1]), sys.argv[2]
    with open(path, 'w') as f:
        f.write(gen(seed, inverse='--no-inverse' not in sys.argv))
