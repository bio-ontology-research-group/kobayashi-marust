"""Sibling family of the satisfiable-expander-cache misses nn1064min,
nn1313min and nn1348min (docs/HYBRID-CB-HT.md section 23).

The three reductions share one shape: a successor `y` whose label holds an
at-most (or functional / inverse functional) restriction on a role `R` and
an existential on `R` (a plain `∃R.C`, an `ObjectHasValue`, or a nested
`∃R.∃R.{b}`), while the node that created `y` is itself an `R`-neighbour of
`y`. The existential must then be satisfied by the creator, which every
earlier probe that saw the same label without such a creator did not need.
The family varies: nominals in `ObjectOneOf` and `ObjectHasValue`, at-most
and functional or inverse functional roles and their inverses, inverse role
pairs, reflexive roles, nested existentials whose successors meet the bound,
`DifferentIndividuals`, `≤0 R`, `≥n R.(∃R⁻.{a})`, `≤n R⁻.(∃R.∃R.{b})`,
complements next to nominals, and assertions. All roles are simple, so each
seed is inside OWL 2 DL.

usage: python3 -I gen_sat.py SEED OUT.ofn
"""
import random
import sys


def gen(seed):
    R = random.Random(seed * 104729 + 1348)
    C = ['A', 'B', 'C', 'D', 'E', 'F']
    S = ['r', 's', 'p']
    Q = ['Q%d' % i for i in range(1, R.randint(3, 6))]
    inds = ['a', 'b', 'c']

    def rname():
        return R.choice(S)

    def role(inv=.45):
        x = rname()
        return f'ObjectInverseOf(:{x})' if R.random() < inv else f':{x}'

    def atom():
        return ':' + R.choice(C)

    def lit():
        return f'ObjectComplementOf({atom()})' if R.random() < .25 else atom()

    def ind():
        return ':' + R.choice(inds)

    def nom(k=1):
        return 'ObjectOneOf(%s)' % ' '.join(':' + i for i in R.sample(inds, k))

    def reach(d=0):
        # an element that reaches a nominal, possibly through nested steps
        k = R.randrange(7 if d < 2 else 3)
        if k == 0:
            return f'ObjectHasValue({role()} {ind()})'
        if k == 1:
            return f'ObjectSomeValuesFrom({role()} {nom()})'
        if k == 2:
            return f'ObjectSomeValuesFrom({role()} ObjectIntersectionOf({nom()} {lit()}))'
        if k == 3:
            return f'ObjectSomeValuesFrom({role()} {reach(d + 1)})'
        if k == 4:
            return f'ObjectSomeValuesFrom({role()} ObjectIntersectionOf({lit()} {reach(d + 1)}))'
        if k == 5:
            return f'ObjectSomeValuesFrom({role()} ObjectAllValuesFrom({role()} {nom()}))'
        return f'ObjectIntersectionOf({lit()} {reach(d + 1)})'

    def expr(d=0):
        k = R.randrange(11 if d < 2 else 4)
        if k == 0:
            return lit()
        if k == 1:
            return reach(d)
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
            return f'ObjectMaxCardinality({R.choice([0, 1, 1, 2])} {role()} {expr(d + 1)})'
        return f'ObjectMaxCardinality({R.choice([0, 1, 1, 2])} {role()})'

    ax = []
    # Role characteristics: every seed bounds some role by one.
    for _ in range(R.randint(1, 3)):
        k = R.randrange(7)
        a, b = R.sample(S, 2)
        if k in (0, 1):
            ax.append(f'InverseFunctionalObjectProperty(:{a})')
        elif k in (2, 3):
            ax.append(f'FunctionalObjectProperty(:{a})')
        elif k == 4:
            ax.append(f'InverseObjectProperties(:{a} :{b})')
        elif k == 5:
            ax.append(f'SubClassOf(owl:Thing ObjectMaxCardinality(1 {role()}))')
        else:
            ax.append(f'SubClassOf({atom()} ObjectMaxCardinality(1 {role()}))')
    if R.random() < .5:
        a, b = R.sample(S, 2)
        ax.append(f'InverseObjectProperties(:{a} :{b})')
    if R.random() < .3:
        ax.append(f'ReflexiveObjectProperty(:{rname()})')
    # Cores in the shape of the three reductions.
    for _ in range(R.randint(1, 3)):
        k = R.randrange(9)
        n = R.choice([1, 1, 2])
        if k == 0:  # nn1064min: Q ≡ {b} ⊓ ≥2 p.B, Q' ≡ ≤1 r⁻.(∃r.{a})
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectIntersectionOf({nom()} '
                      f'ObjectMinCardinality({R.choice([1, 2, 2])} {role()} {atom()})))')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectMaxCardinality({n} {role()} '
                      f'ObjectHasValue({role()} {ind()})))')
        elif k == 2:  # nn1313min: ≤1 p⁻.(∃s⁻.({a} ⊓ ¬A)) ⊑ E
            ax.append(f'SubClassOf(ObjectMaxCardinality({n} {role()} ObjectSomeValuesFrom({role()} '
                      f'ObjectIntersectionOf({nom()} {lit()}))) {atom()})')
        elif k == 3:  # nn1348min: F ⊑ ≤1 s⁻.(E ⊓ ∃r⁻.{c})
            ax.append(f'SubClassOf({atom()} ObjectMaxCardinality({n} {role()} '
                      f'ObjectIntersectionOf({atom()} ObjectHasValue({role()} {ind()}))))')
        elif k == 4:  # nn1348min: Q ≡ ≤1 r⁻.(∃r.∃r.{b})
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectMaxCardinality({n} {role()} '
                      f'ObjectSomeValuesFrom({role()} ObjectHasValue({role()} {ind()}))))')
        elif k == 5:  # nn1348min: Q ≡ ≤0 r
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectMaxCardinality(0 {role()}))')
        elif k == 6:  # nn1313min: Q ≡ ≤1 r⁻.B ⊔ (∃r⁻.{c} ⊓ B)
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectUnionOf(ObjectMaxCardinality({n} {role()} {atom()}) '
                      f'ObjectIntersectionOf(ObjectSomeValuesFrom({role()} {nom()}) {atom()})))')
        elif k == 7:  # an existential whose successor meets the bound through the creator
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role()} ObjectIntersectionOf('
                      f'ObjectMaxCardinality(1 {role()}) {reach(1)})))')
        else:
            ax.append(f'SubClassOf({atom()} ObjectMinCardinality({R.choice([2, 2, 3])} {role()} {reach(1)}))')
    for _ in range(R.randint(0, 3)):
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
        elif a != b:
            ax.append(f'DifferentIndividuals(:{a} :{b})')
    for q in Q:
        k = R.randrange(6)
        n = R.choice([0, 1, 1, 2])
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectMaxCardinality({n} {role()} {reach(1)}))')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{q} ObjectMaxCardinality({R.choice([0, 1])} {role()}))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectMinCardinality({R.choice([1, 2])} {role()} {expr(1)}))')
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
    return ('Prefix(:=<http://example.org/sat#>)\nOntology(<http://example.org/sat>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
