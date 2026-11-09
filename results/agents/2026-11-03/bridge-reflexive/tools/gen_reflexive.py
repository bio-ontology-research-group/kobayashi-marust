"""Sibling family of the bridge misses min1722 and min526.

Both reductions combine a reflexive role (directly or through an inverse
pair) with functionality or inverse functionality, so that every
neighbour along the role collapses into the node, and an at-least or
at-most restriction on the role or its inverse that counts the collapsed
neighbours. The family varies: reflexive, irreflexive, functional and
inverse-functional roles and their inverses (InverseObjectProperties and
ObjectInverseOf), ObjectHasSelf and its complement, at-least and at-most
restrictions (qualified and unqualified) on the role and its inverse,
`≤ n R⁻ ⊑ B` / `B ⊑ ≥ m R` cores in the shape of min1722, `∀R.Self(R) ⊓ ≤1 R⁻`
definitions in the shape of min526, and nominals (ObjectOneOf, class and
role assertions). All roles are simple (no transitivity, chains or
sub-properties), so every axiom is inside OWL 2 DL.

usage: python3 -I gen_reflexive.py SEED OUT.ofn
"""
import random
import sys


def gen(seed):
    R = random.Random(seed * 104729 + 1722)
    C = ['A', 'B', 'C', 'D', 'E', 'F']
    S = ['r', 's', 'p']
    Q = ['Q%d' % i for i in range(1, R.randint(2, 6))]
    nominals = R.random() < .25
    inds = ['a', 'b', 'c']

    def rname():
        return R.choice(S)

    def role(inv=.45):
        x = rname()
        return f'ObjectInverseOf(:{x})' if R.random() < inv else f':{x}'

    def atom():
        return ':' + R.choice(C)

    def lit():
        return f'ObjectComplementOf({atom()})' if R.random() < .15 else atom()

    def self_(neg=.15):
        e = f'ObjectHasSelf(:{rname()})'
        return f'ObjectComplementOf({e})' if R.random() < neg else e

    def expr(d=0):
        k = R.randrange(12 if d < 2 else 4)
        if k == 0:
            return lit()
        if k == 1:
            return self_()
        if k == 2:
            return atom()
        if k == 3:
            return f'ObjectOneOf(:{R.choice(inds)})' if nominals else atom()
        if k == 4:
            return f'ObjectSomeValuesFrom({role()} {expr(d + 1)})'
        if k == 5:
            return f'ObjectAllValuesFrom({role()} {expr(d + 1)})'
        if k == 6:
            return f'ObjectIntersectionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 7:
            return f'ObjectUnionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 8:
            return f'ObjectMinCardinality({R.choice([2, 2, 3])} {role()})'
        if k == 9:
            return f'ObjectMinCardinality({R.choice([1, 2, 3])} {role()} {expr(d + 1)})'
        if k == 10:
            return f'ObjectMaxCardinality({R.choice([0, 1, 1, 2])} {role()} {expr(d + 1)})'
        return f'ObjectMaxCardinality({R.choice([1, 1, 2])} {role(.6)})'

    ax = []
    # Role characteristics: a reflexive role in most seeds, functional or
    # inverse-functional roles, inverse pairs, sometimes an irreflexive role.
    refl = R.sample(S, R.choice([1, 1, 1, 2])) if R.random() < .8 else []
    for a in refl:
        ax.append(f'ReflexiveObjectProperty(:{a})')
    for _ in range(R.randint(1, 3)):
        k = R.randrange(6)
        a, b = R.sample(S, 2)
        if k in (0, 1):
            ax.append(f'InverseFunctionalObjectProperty(:{a})')
        elif k in (2, 3):
            ax.append(f'FunctionalObjectProperty(:{a})')
        elif k == 4:
            ax.append(f'InverseObjectProperties(:{a} :{b})')
        else:
            ax.append(f'SubClassOf(owl:Thing ObjectMaxCardinality(1 {role(.5)}))')
    if R.random() < .4:
        a, b = R.sample(S, 2)
        ax.append(f'InverseObjectProperties(:{a} :{b})')
    if R.random() < .25:
        cand = [x for x in S if x not in refl]
        if cand:
            ax.append(f'IrreflexiveObjectProperty(:{R.choice(cand)})')
    if R.random() < .3:
        ax.append(f'SubClassOf({atom()} {self_(.3)})')
    # Cores in the shape of the two reductions.
    for _ in range(R.randint(1, 3)):
        k = R.randrange(6)
        if k == 0:  # min1722: ≤n R⁻ ⊑ B, B ⊑ ≥m R
            b = atom()
            ax.append(f'SubClassOf(ObjectMaxCardinality({R.choice([1, 1, 2])} {role(.7)}) {b})')
            ax.append(f'SubClassOf({b} ObjectMinCardinality({R.choice([2, 3])} {role(.3)}))')
        elif k == 1:  # min1722: E ⊑ ∃R⁻.X
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role(.7)} {expr(1)}))')
        elif k == 2:  # min526: Q ≡ ∀R.Self(R) ⊓ ≤1 R⁻
            x = rname()
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectIntersectionOf('
                      f'ObjectAllValuesFrom({role(.5)} ObjectHasSelf(:{x})) '
                      f'ObjectMaxCardinality(1 {role(.5)})))')
        elif k == 3:  # min526: F ⊑ ∃R.(C ⊓ Self(S)), E ⊑ ∀S.F
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role()} '
                      f'ObjectIntersectionOf({atom()} {self_(0)})))')
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({role()} {atom()}))')
        elif k == 4:
            ax.append(f'SubClassOf({atom()} ObjectMinCardinality({R.choice([2, 3])} {role()} {expr(1)}))')
        else:
            ax.append(f'SubClassOf(ObjectMaxCardinality({R.choice([0, 1])} {role()} {expr(1)}) {atom()})')
    for _ in range(R.randint(1, 4)):
        k = R.randrange(4)
        if k == 0:
            ax.append(f'SubClassOf({atom()} {expr()})')
        elif k == 1:
            ax.append(f'SubClassOf({expr()} {atom()})')
        elif k == 2:
            ax.append(f'DisjointClasses({atom()} {atom()})')
        else:
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({role()} {lit()}))')
    if nominals:
        for _ in range(R.randint(1, 3)):
            k = R.randrange(4)
            a, b = R.choice(inds), R.choice(inds)
            if k == 0:
                ax.append(f'ClassAssertion({expr(1)} :{a})')
            elif k == 1:
                ax.append(f'ObjectPropertyAssertion(:{rname()} :{a} :{b})')
            elif k == 2:
                ax.append(f'ClassAssertion({atom()} :{a})')
            else:
                ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role()} ObjectOneOf(:{a})))')
    for q in Q:
        k = R.randrange(5)
        n = R.choice([1, 2, 2, 3])
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} '
                      f'ObjectMinCardinality({n} {role()} {expr(1)})))')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{q} ObjectMaxCardinality({R.choice([0, 1])} {role()}))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom({role()} {self_()}))')
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
        decl += [f'Declaration(NamedIndividual(:{i}))' for i in inds]
    return ('Prefix(:=<http://example.org/refl#>)\nOntology(<http://example.org/refl>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
