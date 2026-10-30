"""Random small nominal ontologies that produce disjunctive ground equalities
across individuals that a query context does not announce.

usage: python3 -I gen_r3.py SEED OUT.ofn [--no-inverse]

Ingredients: 3 to 5 individuals; at-most restrictions (qualified and not) on
individuals, alone or inside unions; functional and inverse-functional roles;
enumerations ObjectOneOf(o o'); unions on individuals; universal and
existential restrictions; and query classes Qi with SubClassOf(Qi {o}) or
EquivalentClasses(Qi {o}), so the context of Qi announces one individual.
Axiom order is shuffled, which changes the interning order of individuals
and therefore the orientation of ground equalities.
"""
import random
import sys


def gen(seed, inverse=True):
    R = random.Random(seed)
    n_ind = R.randint(3, 5)
    IND = ['a', 'b', 'c', 'd', 'e'][:n_ind]
    C = ['A', 'B', 'C', 'D', 'E']
    OP = ['r', 's']
    Q = ['Q1', 'Q2', 'Q3']

    def role():
        p = R.choice(OP)
        if inverse and R.random() < .1:
            return f'ObjectInverseOf(:{p})'
        return f':{p}'

    def atom():
        return ':' + R.choice(C)

    def nom(k=None):
        k = k or R.choice([1, 2, 2])
        return 'ObjectOneOf(' + ' '.join(':' + i for i in R.sample(IND, k)) + ')'

    def lhs():
        k = R.randrange(6)
        if k < 3:
            return atom()
        if k == 3:
            return nom()
        if k == 4:
            return f'ObjectSomeValuesFrom({role()} {atom()})'
        return f'ObjectIntersectionOf({atom()} {atom()})'

    def cls(d=0):
        k = R.randrange(10 if d < 1 else 4)
        if k < 3:
            return atom()
        if k == 3:
            return nom()
        if k == 4:
            return f'ObjectMaxCardinality(1 {role()}{" " + atom() if R.random() < .5 else ""})'
        if k == 5:
            return f'ObjectUnionOf({cls(d + 1)} {cls(d + 1)})'
        if k == 6:
            return f'ObjectAllValuesFrom({role()} {cls(d + 1)})'
        if k == 7:
            return f'ObjectSomeValuesFrom({role()} {cls(d + 1)})'
        if k == 8:
            return f'ObjectHasValue({role()} :{R.choice(IND)})'
        return f'ObjectIntersectionOf({cls(d + 1)} {cls(d + 1)})'

    def disj_eq_source():
        # A shape that yields a ground disjunctive equality.
        k = R.randrange(4)
        o = R.choice(IND)
        if k == 0:
            q = f'ObjectMaxCardinality(1 {role()}{" " + atom() if R.random() < .6 else ""})'
            return f'ClassAssertion(ObjectUnionOf({q} {atom()}) :{o})'
        if k == 1:
            return f'ClassAssertion(ObjectUnionOf({nom(1)} {atom()}) :{o})'
        if k == 2:
            return f'ClassAssertion({nom(2)} :{o})'
        return f'SubClassOf({atom()} {nom(2)})'

    ax = []
    for _ in range(R.randint(1, 3)):
        ax.append(disj_eq_source())
    for _ in range(R.randint(2, 5)):
        ax.append(f'ObjectPropertyAssertion(:{R.choice(OP)} :{R.choice(IND)} :{R.choice(IND)})')
    for _ in range(R.randint(1, 3)):
        ax.append(f'ClassAssertion({cls()} :{R.choice(IND)})')
    for _ in range(R.randint(1, 3)):
        ax.append(f'SubClassOf({lhs()} {cls()})')
    if R.random() < .4:
        ax.append(f'FunctionalObjectProperty(:{R.choice(OP)})')
    if inverse and R.random() < .1:
        ax.append(f'InverseFunctionalObjectProperty(:{R.choice(OP)})')
    for q in Q[:R.randint(1, 3)]:
        o = R.choice(IND)
        if R.random() < .5:
            ax.append(f'SubClassOf(:{q} ObjectOneOf(:{o}))')
        else:
            ax.append(f'EquivalentClasses(:{q} ObjectOneOf(:{o}))')
    R.shuffle(ax)
    decl = ([f'Declaration(Class(:{c}))' for c in C + Q]
            + [f'Declaration(ObjectProperty(:{p}))' for p in OP]
            + [f'Declaration(NamedIndividual(:{i}))' for i in IND])
    return ('Prefix(:=<http://example.org/r3#>)\nOntology(<http://example.org/r3>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    seed = int(sys.argv[1])
    with open(sys.argv[2], 'w') as f:
        f.write(gen(seed, inverse='--no-inverse' not in sys.argv))
