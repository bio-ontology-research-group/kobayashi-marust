"""Random small ontologies around SameIndividual: equality classes of named
individuals (chains and stars), class assertions on different members that
conflict through disjointness, DifferentIndividuals inside and across merged
classes, nominals of merged members in the TBox ({b} on either side,
ObjectHasValue, enumerations), functional and inverse-functional roles that
force further merges, role, negative role and data assertions on members.
Query classes Qi = {o}, Qi <= {o} and Qi = EXISTS r.{o} expose the merged
labels in the taxonomy.

usage: python3 -I gen_same.py SEED OUT.ofn

No axiom is repeated.
"""
import random
import sys


def gen(seed):
    R = random.Random(seed)
    n_ind = R.randint(4, 7)
    IND = ['a', 'b', 'c', 'd', 'e', 'f', 'g'][:n_ind]
    C = ['A', 'B', 'C', 'D', 'E']
    OP = ['r', 's', 't']
    Q = ['Q1', 'Q2', 'Q3', 'Q4']

    def role():
        p = R.choice(OP)
        if R.random() < .15:
            return f'ObjectInverseOf(:{p})'
        return f':{p}'

    def atom():
        return ':' + R.choice(C)

    def ind():
        return ':' + R.choice(IND)

    def nom():
        k = min(R.choice([1, 1, 2, 3]), len(IND))
        return 'ObjectOneOf(' + ' '.join(':' + i for i in R.sample(IND, k)) + ')'

    def filler(d=0):
        k = R.randrange(7 if d < 1 else 3)
        if k < 2:
            return atom()
        if k == 2:
            return nom()
        if k == 3:
            return f'ObjectUnionOf({filler(d + 1)} {filler(d + 1)})'
        if k == 4:
            return f'ObjectAllValuesFrom({role()} {filler(d + 1)})'
        if k == 5:
            return f'ObjectHasValue({role()} {ind()})'
        return f'ObjectSomeValuesFrom({role()} {filler(d + 1)})'

    ax = []
    # SameIndividual: one or two equality classes, chains or stars
    for _ in range(R.randint(1, 3)):
        k = R.randint(2, 3)
        ax.append('SameIndividual(' + ' '.join(':' + i for i in R.sample(IND, k)) + ')')
    if R.random() < .3:
        ax.append('FunctionalObjectProperty(:r)')
    if R.random() < .15:
        ax.append('InverseFunctionalObjectProperty(:s)')
    if R.random() < .2:
        ax.append('SubClassOf(:A ObjectMaxCardinality(1 :t owl:Thing))')
    if R.random() < .4:
        ax.append('DisjointClasses(:A :B)')
    if R.random() < .2:
        ax.append('DisjointClasses(:C :D)')
    if R.random() < .2:
        ax.append(f'SubObjectPropertyOf(:s :t)')
    if R.random() < .15:
        ax.append('TransitiveObjectProperty(:t)')
    use_data = R.random() < .2
    if use_data:
        ax.append('FunctionalDataProperty(:p)')
    # ABox
    for _ in range(R.randint(2, 6)):
        k = R.randrange(10)
        x, y = R.sample(IND, 2)
        if k < 4:
            ax.append(f'ClassAssertion({atom()} :{x})')
        elif k < 6:
            ax.append(f'ClassAssertion({filler()} :{x})')
        elif k < 8:
            ax.append(f'ObjectPropertyAssertion(:{R.choice(OP)} :{x} :{y})')
        elif k == 8:
            ax.append(f'NegativeObjectPropertyAssertion(:{R.choice(OP)} :{x} :{y})')
        else:
            ax.append(f'DifferentIndividuals(:{x} :{y})')
    if use_data:
        for _ in range(R.randint(1, 2)):
            ax.append(f'DataPropertyAssertion(:p {ind()} "{R.randint(1, 2)}"^^xsd:integer)')
    # TBox
    for _ in range(R.randint(2, 5)):
        k = R.randrange(6)
        if k == 0:
            ax.append(f'SubClassOf({nom()} {filler()})')
        elif k == 1:
            ax.append(f'SubClassOf({atom()} {filler()})')
        elif k == 2:
            ax.append(f'SubClassOf(ObjectSomeValuesFrom({role()} {atom()}) {atom()})')
        elif k == 3:
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role()} {atom()}))')
        elif k == 4:
            ax.append(f'SubClassOf(ObjectHasValue({role()} {ind()}) {atom()})')
        else:
            ax.append(f'SubClassOf({nom()} {nom()})')
    for q in Q:
        k = R.randrange(4)
        o = ind()
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectOneOf({o}))')
        elif k == 1:
            ax.append(f'SubClassOf(:{q} ObjectOneOf({o}))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom({role()} ObjectOneOf({o})))')
        else:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} ObjectOneOf({o} {ind()})))')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    decl = [f'Declaration(Class(:{c}))' for c in C + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in OP]
    decl += [f'Declaration(NamedIndividual(:{i}))' for i in IND]
    if use_data:
        decl.append('Declaration(DataProperty(:p))')
    return ('Prefix(:=<http://x#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'
            'Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n'
            'Ontology(<http://x/s' + str(seed) + '>\n' + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    with open(sys.argv[2], 'w') as f:
        f.write(gen(int(sys.argv[1])))
