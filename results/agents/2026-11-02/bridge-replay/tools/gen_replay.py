"""Seed family for the retained consistency leaf (docs/HYBRID-CB-HT.md §16).

Small ontologies whose ABox consistency completion is nondeterministic
(disjunctive and nominal-disjunctive class assertions, at-most restrictions
that force merges between individuals) and whose classes reach the ABox by
ObjectHasValue (and chains of them), so that class jobs run on the leaf and
some of them contradict the leaf's decisions: e.g. both disjuncts of an
individual imply a consequence for its r-predecessors, so `Q = r value a`
is subsumed by it only when every choice for `a` is considered.

usage: python3 -I gen_replay.py SEED OUT.ofn
No axiom is repeated (the bridge refuses repeated assertions).
"""
import random
import sys


def gen(seed):
    R = random.Random(seed)
    IND = ['a', 'b', 'c', 'd', 'e', 'f'][:R.randint(3, 6)]
    C = ['A', 'B', 'C', 'D', 'E', 'F']
    OP = ['r', 's', 't']
    Q = ['Q%d' % i for i in range(1, R.randint(3, 7))]

    def role(inv=0.15):
        p = R.choice(OP)
        return f'ObjectInverseOf(:{p})' if R.random() < inv else f':{p}'

    def atom():
        return ':' + R.choice(C)

    def ind():
        return ':' + R.choice(IND)

    def lit():
        return f'ObjectComplementOf({atom()})' if R.random() < .2 else atom()

    def nom(k=None):
        k = min(k or R.choice([1, 1, 2]), len(IND))
        return 'ObjectOneOf(' + ' '.join(':' + i for i in R.sample(IND, k)) + ')'

    def hv(depth=0):
        # ObjectHasValue chains: r value a, or r some (s value b)
        if depth < 2 and R.random() < .35:
            return f'ObjectSomeValuesFrom({role(0.1)} {hv(depth + 1)})'
        return f'ObjectHasValue({role(0.1)} {ind()})'

    ax = []
    # nondeterministic ABox: disjunctions, nominal disjunctions, merges
    for _ in range(R.randint(2, 5)):
        k = R.randrange(5)
        x = ind()
        if k == 0:
            ax.append(f'ClassAssertion(ObjectUnionOf({lit()} {lit()}) {x})')
        elif k == 1:
            ax.append(f'ClassAssertion(ObjectUnionOf({nom(1)} {nom(1)}) {x})')
        elif k == 2:
            ax.append(f'ClassAssertion(ObjectUnionOf({atom()} {nom(1)}) {x})')
        elif k == 3:
            ax.append(f'ClassAssertion(ObjectMaxCardinality(1 {role(0)}) {x})')
        else:
            ax.append(f'ClassAssertion(ObjectMaxCardinality({R.choice([1, 2])} {role(0)} {atom()}) {x})')
    for _ in range(R.randint(2, 6)):
        ax.append(f'ObjectPropertyAssertion(:{R.choice(OP)} {ind()} {ind()})')
    for _ in range(R.randint(0, 3)):
        ax.append(f'ClassAssertion({lit()} {ind()})')
    # TBox: consequences of each disjunct, propagated to neighbours
    for _ in range(R.randint(2, 6)):
        k = R.randrange(6)
        if k == 0:
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({role()} {atom()}))')
        elif k == 1:
            ax.append(f'SubClassOf({atom()} {atom()})')
        elif k == 2:
            ax.append(f'SubClassOf(ObjectSomeValuesFrom({role()} {atom()}) {atom()})')
        elif k == 3:
            ax.append(f'SubClassOf({atom()} ObjectUnionOf({atom()} {atom()}))')
        elif k == 4:
            ax.append(f'SubClassOf({atom()} ObjectMaxCardinality(1 {role(0)}))')
        else:
            ax.append(f'DisjointClasses({atom()} {atom()})')
    if R.random() < .3:
        ax.append(f'FunctionalObjectProperty(:{R.choice(OP)})')
    # query classes reaching the ABox
    for q in Q:
        k = R.randrange(5)
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} {hv()})')
        elif k == 1:
            ax.append(f'SubClassOf(:{q} {hv()})')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} {hv()}))')
        elif k == 3:
            ax.append(f'EquivalentClasses(:{q} {nom()})')
        else:
            ax.append(f'SubClassOf(:{q} ObjectUnionOf({hv()} {atom()}))')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    R.shuffle(ax)
    decl = [f'Declaration(Class(:{c}))' for c in C + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in OP]
    decl += [f'Declaration(NamedIndividual(:{i}))' for i in IND]
    return ('Prefix(:=<http://example.org/replay#>)\nOntology(<http://example.org/replay>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
