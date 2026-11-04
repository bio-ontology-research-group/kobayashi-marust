"""Sibling family of the nn1811 reduction r19.

r19: InverseObjectProperties(r s), DisjointClasses(A C), ⊤ ⊑ ≤1 s,
¬Q4 ⊑ ∃r.∃s.C. The r-successor y of an A element has its parent as an
s-neighbour, ⊤ ⊑ ≤1 s merges y's s-successor in C into the parent, so
A ⊑ Q4 (HermiT). The bridge misses it when the satisfiable expander cache
answers for y.

The family varies the parts: how the at-most on the inverse link arises
(⊤ ⊑ ≤n R, ObjectPropertyDomain(R ≤1 R), FunctionalObjectProperty,
InverseFunctionalObjectProperty, an at-most in a class, with R a name or
an inverse), how the two-step path is written (named inverse roles,
ObjectInverseOf, InverseObjectProperties to several names, as in nn1811
where r⁻ = s = p), how the left side reaches it (¬Q ⊑ ∃r.∃s.X,
Q ≡ ≤n r.(∃s.X), Q ≡ ≤0 r, ∃/∀/≥n over the path), disjointness and
complements, and in 40 % of the seeds nominals (ObjectHasValue,
ObjectOneOf, class and role assertions) as in nn1811, so that the
`nominals` route runs the nominal CB stack. All roles are simple; every
axiom is in OWL 2 DL.

usage: python3 -I gen_fx.py SEED OUT.ofn
"""
import random
import sys


def gen(seed):
    R = random.Random(seed * 104729 + 1811)
    C = ['A', 'B', 'C', 'D', 'E']
    S = ['r', 's', 'p']
    Q = ['Q%d' % i for i in range(1, R.randint(3, 5))]
    inds = ['a', 'b', 'c']
    nominal = R.random() < .4

    def role(inv=.35):
        x = R.choice(S)
        return f'ObjectInverseOf(:{x})' if R.random() < inv else f':{x}'

    def atom():
        return ':' + R.choice(C)

    def lit():
        return f'ObjectComplementOf({atom()})' if R.random() < .2 else atom()

    def filler(d=0):
        k = R.randrange(8 if d == 0 else 4)
        if k <= 1:
            return lit()
        if k == 2:
            return atom()
        if k == 3 and nominal:
            return R.choice([f'ObjectOneOf(:{R.choice(inds)})',
                             f'ObjectHasValue({role()} :{R.choice(inds)})'])
        if k == 4:
            return f'ObjectSomeValuesFrom({role()} {filler(d + 1)})'
        if k == 5:
            return f'ObjectIntersectionOf({lit()} {filler(d + 1)})'
        if k == 6:
            return f'ObjectAllValuesFrom({role()} {filler(d + 1)})'
        return f'ObjectUnionOf({lit()} {filler(d + 1)})'

    def path():
        # ∃R.∃S.X, the two-step path of r19 (R and S often inverse).
        return f'ObjectSomeValuesFrom({role(.25)} ObjectSomeValuesFrom({role(.4)} {filler(1)}))'

    ax = []
    # Inverse links: r19 has one, nn1811 two (r⁻ = s = p).
    a, b, c = R.sample(S, 3)
    ax.append(f'InverseObjectProperties(:{a} :{b})')
    if R.random() < .4:
        ax.append(f'InverseObjectProperties(:{a} :{c})')
    # At-most restrictions on an inverse link, in several encodings.
    for _ in range(R.randint(1, 2)):
        k = R.randrange(7)
        rl = role(.5)
        n = R.choice([1, 1, 1, 2])
        if k <= 1:
            ax.append(f'SubClassOf(owl:Thing ObjectMaxCardinality({n} {rl}))')
        elif k == 2:
            x = R.choice(S)
            ax.append(f'ObjectPropertyDomain(:{x} ObjectMaxCardinality(1 :{x}))')
        elif k in (3, 4):
            # KM's parser takes named roles only in these axioms; write
            # Functional(x⁻) as InverseFunctional(x) and vice versa.
            inv = rl.startswith('ObjectInverseOf')
            x = rl[len('ObjectInverseOf('):-1] if inv else rl
            fn = (k == 3) != inv
            ax.append(f'{"" if fn else "Inverse"}FunctionalObjectProperty({x})')
        elif k == 5:
            ax.append(f'SubClassOf({atom()} ObjectMaxCardinality({n} {rl}))')
        else:
            ax.append(f'SubClassOf(owl:Thing ObjectMaxCardinality({n} {rl} {lit()}))')
    # Cores in the shape of r19, r13 and nn1811.
    for _ in range(R.randint(1, 3)):
        k = R.randrange(9)
        q = ':' + R.choice(Q)
        n = R.choice([0, 1, 1, 2, 3])
        if k == 0:  # r19
            ax.append(f'SubClassOf(ObjectComplementOf({q}) {path()})')
        elif k == 1:  # r13
            ax.append(f'SubClassOf(ObjectMaxCardinality({R.choice([1, 1, 2])} {role(.25)} '
                      f'ObjectSomeValuesFrom({role(.4)} {filler(1)})) {q})')
        elif k == 2:  # nn1811: Q ≡ ≤n R.(∃S.X)
            ax.append(f'EquivalentClasses({q} ObjectMaxCardinality({n} {role(.4)} '
                      f'ObjectSomeValuesFrom({role(.4)} {filler(1)})))')
        elif k == 3:  # nn1811: Q ≡ ≤0 r / ≤1 r
            ax.append(f'EquivalentClasses({q} ObjectMaxCardinality({R.choice([0, 0, 1])} {role(.3)}))')
        elif k == 4:
            ax.append(f'SubClassOf({atom()} {path()})')
        elif k == 5:
            ax.append(f'EquivalentClasses({q} {path()})')
        elif k == 6:
            ax.append(f'SubClassOf({q} ObjectMinCardinality({R.choice([1, 2])} {role(.3)} '
                      f'ObjectSomeValuesFrom({role(.4)} {filler(1)})))')
        elif k == 7:
            ax.append(f'SubClassOf({path()} {atom()})')
        else:
            ax.append(f'EquivalentClasses({q} ObjectAllValuesFrom({role(.3)} {filler(1)}))')
    for _ in range(R.randint(1, 2)):
        k = R.randrange(3)
        if k == 0:
            x, y = R.sample(C, 2)
            ax.append(f'DisjointClasses(:{x} :{y})')
        elif k == 1:
            ax.append(f'SubClassOf({atom()} {filler()})')
        else:
            ax.append(f'SubClassOf({filler()} {atom()})')
    if nominal:
        for _ in range(R.randint(1, 3)):
            k = R.randrange(5)
            i, j = R.choice(inds), R.choice(inds)
            if k == 0:
                ax.append(f'ClassAssertion({filler()} :{i})')
            elif k == 1:
                ax.append(f'ObjectPropertyAssertion(:{R.choice(S)} :{i} :{j})')
            elif k == 2:
                ax.append(f'SubClassOf(ObjectOneOf(:{i}) {path()})')
            elif k == 3:
                ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectMaxCardinality({R.choice([1, 2, 3])} '
                          f'{role(.5)} ObjectHasValue({role(.3)} :{i})))')
            else:
                ax.append(f'ClassAssertion(ObjectMaxCardinality(1 {role(.4)} {lit()}) :{i})')
    seen = set()
    ax = [x for x in ax if not (x in seen or seen.add(x))]
    R.shuffle(ax)
    decl = [f'Declaration(Class(:{x}))' for x in C + Q]
    decl += [f'Declaration(ObjectProperty(:{x}))' for x in S]
    if nominal:
        decl += [f'Declaration(NamedIndividual(:{x}))' for x in inds]
    return ('Prefix(:=<http://example.org/fx#>)\nOntology(<http://example.org/fx>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
