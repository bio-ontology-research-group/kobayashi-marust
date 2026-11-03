"""Sibling family of seed s974: successors merged into their predecessor.

The s974 shape: `Q ⊑ ≥ n r.C` together with role axioms that force an
r-successor to equal its predecessor (Reflexive + InverseFunctional r), so
that distinct successors collapse and the cardinality clashes. The family
varies the forcing axioms (reflexive, inverse-functional, functional,
functional inverses, inverse pairs, symmetric roles, `≤ 1 R⁻` and
`∃ R⁻.Self` style class axioms, Self restrictions), the cardinalities and
the fillers, and mixes in ordinary TBox axioms, disjunctions and a few
nominals so that many seeds stay satisfiable. Simple roles only appear in
cardinality and Self restrictions (OWL 2 DL global restrictions).

usage: python3 -I gen_merge.py SEED OUT.ofn
"""
import random
import sys


def gen(seed):
    R = random.Random(seed * 7919 + 974)
    C = ['A', 'B', 'C', 'D', 'E', 'F']
    S = ['r', 's', 'p']
    Q = ['Q%d' % i for i in range(1, R.randint(3, 7))]
    nominals = R.random() < .15

    def role(inv=.3):
        x = R.choice(S)
        return f'ObjectInverseOf(:{x})' if R.random() < inv else f':{x}'

    def atom():
        return ':' + R.choice(C)

    def lit():
        return f'ObjectComplementOf({atom()})' if R.random() < .1 else atom()

    def expr(d=0):
        k = R.randrange(11 if d < 2 else 3)
        if k == 0:
            return lit()
        if k == 1:
            return atom()
        if k == 2:
            return f'ObjectHasSelf(:{R.choice(S)})'
        if k == 3:
            return f'ObjectSomeValuesFrom({role()} {expr(d + 1)})'
        if k == 4:
            return f'ObjectAllValuesFrom({role()} {expr(d + 1)})'
        if k == 5:
            return f'ObjectIntersectionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 6:
            return f'ObjectUnionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 7:
            return f'ObjectMinCardinality({R.choice([1, 2, 2, 3])} {role()} {expr(d + 1)})'
        if k == 8:
            return f'ObjectMinCardinality({R.choice([2, 2, 3])} {role()})'
        if k == 9:
            return f'ObjectMaxCardinality({R.choice([0, 1, 1, 2])} {role()} {expr(d + 1)})'
        if nominals:
            return f'ObjectOneOf(:{R.choice(["a", "b"])})'
        return f'ObjectMaxCardinality(1 {role(.6)})'

    ax = []
    # The merge-forcing core: at least one axiom that makes successors equal
    # to their predecessor or to each other.
    for _ in range(R.randint(1, 4)):
        k = R.randrange(9)
        a, b = R.sample(S, 2)
        if k == 0:
            ax.append(f'ReflexiveObjectProperty(:{a})')
        elif k == 1:
            ax.append(f'InverseFunctionalObjectProperty(:{a})')
        elif k == 2:
            ax.append(f'FunctionalObjectProperty(:{a})')
        elif k == 3:
            ax.append(f'InverseObjectProperties(:{a} :{b})')
        elif k == 4:
            ax.append(f'SymmetricObjectProperty(:{a})')
        elif k == 5:
            ax.append(f'SubObjectPropertyOf(:{a} :{b})')
        elif k == 6:
            ax.append(f'SubClassOf(owl:Thing ObjectMaxCardinality(1 ObjectInverseOf(:{a})))')
        elif k == 7:
            ax.append(f'SubClassOf({atom()} ObjectHasSelf(:{a}))')
        else:
            ax.append(f'ObjectPropertyDomain(:{a} {lit()})')
    if R.random() < .5:
        a = R.choice(S)
        ax.append(f'ReflexiveObjectProperty(:{a})')
        ax.append(f'InverseFunctionalObjectProperty(:{a})')
    for _ in range(R.randint(2, 6)):
        k = R.randrange(5)
        if k == 0:
            ax.append(f'SubClassOf({atom()} {expr()})')
        elif k == 1:
            ax.append(f'SubClassOf({expr()} {atom()})')
        elif k == 2:
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role()} {expr(1)}))')
        elif k == 3:
            ax.append(f'DisjointClasses({atom()} {atom()})')
        else:
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({role()} {lit()}))')
    if nominals:
        ax.append(f'ClassAssertion({atom()} :{R.choice(["a", "b"])})')
    for q in Q:
        k = R.randrange(5)
        n = R.choice([1, 2, 2, 3])
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} '
                      f'ObjectMinCardinality({n} {role()} {expr(1)})))')
        elif k == 1:
            ax.append(f'SubClassOf(:{q} ObjectMinCardinality({n} {role()}))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom({role()} '
                      f'ObjectMinCardinality({n} {role()} {expr(1)})))')
        elif k == 3:
            ax.append(f'EquivalentClasses(:{q} {expr()})')
        else:
            ax.append(f'SubClassOf(:{q} {expr()})')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    R.shuffle(ax)
    decl = [f'Declaration(Class(:{c}))' for c in C + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in S]
    if nominals:
        decl += ['Declaration(NamedIndividual(:a))', 'Declaration(NamedIndividual(:b))']
    return ('Prefix(:=<http://example.org/merge#>)\nOntology(<http://example.org/merge>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
