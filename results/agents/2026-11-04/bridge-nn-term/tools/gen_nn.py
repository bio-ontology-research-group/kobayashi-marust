"""Sibling family of the NN-rule misses f1008 and f439.

Both reductions put an at-most restriction (directly or through
functionality / inverse functionality) at a nominal, over a blockable
neighbour that the nominal did not create: an element reaches the nominal
through `∃p.{c}` (or `∃r⁻.∀r⁻.{c}` with a reflexive `r`), and a sibling of
that element is blocked by it. The family varies: nominals in `ObjectOneOf`
and `ObjectHasValue`, nested `∃p.{c}` under at-least and at-most
restrictions (`≥n s.∃p.{c}`, `≤n s.∃p.{c}`), functional and inverse
functional roles and their inverses, `≤n p⁻` asserted on a nominal or
reached by a class, at-most restrictions at nominals by class assertion,
role assertions between nominals, reflexive roles, `∀r⁻.{c}`
collapses, and disjunctions. All roles are simple (no transitivity,
chains or sub-properties), so every axiom is inside OWL 2 DL.

usage: python3 -I gen_nn.py SEED OUT.ofn
"""
import random
import sys


def gen(seed):
    R = random.Random(seed * 7919 + 1008)
    C = ['A', 'B', 'C', 'D', 'E', 'F']
    S = ['r', 's', 'p']
    Q = ['Q%d' % i for i in range(1, R.randint(3, 6))]
    inds = ['a', 'b', 'c']

    def rname():
        return R.choice(S)

    def role(inv=.4):
        x = rname()
        return f'ObjectInverseOf(:{x})' if R.random() < inv else f':{x}'

    def atom():
        return ':' + R.choice(C)

    def lit():
        return f'ObjectComplementOf({atom()})' if R.random() < .2 else atom()

    def nom(k=1):
        return 'ObjectOneOf(%s)' % ' '.join(':' + i for i in R.sample(inds, k))

    def reach():
        # an element that reaches a nominal
        k = R.randrange(6)
        if k == 0:
            return f'ObjectSomeValuesFrom({role(.3)} {nom()})'
        if k == 1:
            return f'ObjectHasValue({role(.3)} :{R.choice(inds)})'
        if k == 2:
            return f'ObjectSomeValuesFrom({role(.5)} ObjectAllValuesFrom({role(.5)} {nom()}))'
        if k == 3:
            return f'ObjectSomeValuesFrom({role(.3)} ObjectIntersectionOf({nom()} {lit()}))'
        if k == 4:
            return f'ObjectSomeValuesFrom({role(.3)} {reach()})' if R.random() < .5 else \
                f'ObjectSomeValuesFrom({role(.3)} {nom(2)})'
        return f'ObjectIntersectionOf({lit()} {reach()})'

    def expr(d=0):
        k = R.randrange(11 if d < 2 else 4)
        if k == 0:
            return lit()
        if k == 1:
            return reach()
        if k == 2:
            return atom()
        if k == 3:
            return nom(R.choice([1, 1, 2]))
        if k == 4:
            return f'ObjectSomeValuesFrom({role()} {expr(d + 1)})'
        if k == 5:
            return f'ObjectAllValuesFrom({role()} {expr(d + 1)})'
        if k == 6:
            return f'ObjectIntersectionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 7:
            return f'ObjectUnionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 8:
            return f'ObjectMinCardinality({R.choice([2, 2, 3])} {role()} {expr(d + 1)})'
        if k == 9:
            return f'ObjectMaxCardinality({R.choice([1, 1, 2])} {role()} {expr(d + 1)})'
        return f'ObjectMaxCardinality({R.choice([1, 1, 2])} {role(.6)})'

    ax = []
    # Role characteristics: functional / inverse functional roles in every
    # seed, reflexive roles in some.
    for _ in range(R.randint(1, 3)):
        k = R.randrange(6)
        a, b = R.sample(S, 2)
        if k in (0, 1, 2):
            ax.append(f'InverseFunctionalObjectProperty(:{a})')
        elif k == 3:
            ax.append(f'FunctionalObjectProperty(:{a})')
        elif k == 4:
            ax.append(f'InverseObjectProperties(:{a} :{b})')
        else:
            ax.append(f'SubClassOf(owl:Thing ObjectMaxCardinality({R.choice([1, 1, 2])} {role(.6)}))')
    if R.random() < .35:
        ax.append(f'ReflexiveObjectProperty(:{rname()})')
    # Cores in the shape of the two reductions.
    for _ in range(R.randint(1, 3)):
        k = R.randrange(8)
        if k == 0:  # f1008: ≤n s.(∃p.{c}) ⊑ C
            ax.append(f'SubClassOf(ObjectMaxCardinality({R.choice([1, 1, 2])} {role(.3)} {reach()}) {atom()})')
        elif k == 1:  # ≥n s.(∃p.{c}) in a class
            ax.append(f'SubClassOf({atom()} ObjectMinCardinality({R.choice([2, 2, 3])} {role(.3)} {reach()}))')
        elif k == 2:  # f439: Q ≡ {c} ⊓ ≤n r
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectIntersectionOf({nom()} '
                      f'ObjectMaxCardinality({R.choice([1, 1, 2])} {role(.5)})))')
        elif k == 3:  # f439: E ⊑ ∃r⁻.∀r⁻.{c}
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role(.6)} '
                      f'ObjectAllValuesFrom({role(.6)} {nom()})))')
        elif k == 4:  # at-most at a nominal by assertion
            ax.append(f'ClassAssertion(ObjectMaxCardinality({R.choice([1, 1, 2])} {role(.5)}'
                      f'{" " + expr(1) if R.random() < .5 else ""}) :{R.choice(inds)})')
        elif k == 5:  # Q ≡ ≤n s⁻.(∃p.E)
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectMaxCardinality({R.choice([1, 1, 2])} '
                      f'{role(.6)} ObjectSomeValuesFrom({role(.3)} {atom()})))')
        elif k == 6:  # nominal reaching back through a blockable element
            ax.append(f'SubClassOf({nom()} ObjectSomeValuesFrom({role()} {reach()}))')
        else:
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role()} {reach()}))')
    for _ in range(R.randint(1, 3)):
        k = R.randrange(4)
        if k == 0:
            ax.append(f'SubClassOf({atom()} {expr()})')
        elif k == 1:
            ax.append(f'SubClassOf({expr()} {atom()})')
        elif k == 2:
            ax.append(f'DisjointClasses({atom()} {atom()})')
        else:
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({role()} {lit()}))')
    for _ in range(R.randint(0, 3)):
        k = R.randrange(5)
        a, b = R.choice(inds), R.choice(inds)
        if k == 0:
            ax.append(f'ClassAssertion({expr(1)} :{a})')
        elif k == 1:
            ax.append(f'ObjectPropertyAssertion(:{rname()} :{a} :{b})')
        elif k == 2:
            ax.append(f'ClassAssertion({atom()} :{a})')
        elif k == 3 and a != b:
            ax.append(f'DifferentIndividuals(:{a} :{b})')
        else:
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role()} ObjectOneOf(:{a})))')
    for q in Q:
        k = R.randrange(6)
        n = R.choice([1, 1, 2, 3])
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectMaxCardinality({n} {role()} {reach()}))')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{q} ObjectMaxCardinality({R.choice([0, 1])} {role()}))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectMinCardinality({n} {role()} {expr(1)}))')
        elif k == 3:
            ax.append(f'EquivalentClasses(:{q} {expr()})')
        elif k == 4:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({nom()} {expr(1)}))')
        else:
            ax.append(f'SubClassOf(:{q} {expr()})')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    R.shuffle(ax)
    decl = [f'Declaration(Class(:{c}))' for c in C + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in S]
    decl += [f'Declaration(NamedIndividual(:{i}))' for i in inds]
    return ('Prefix(:=<http://example.org/nn#>)\nOntology(<http://example.org/nn>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
