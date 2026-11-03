"""Sibling family of seed s1966: names that occur only next to head-free roles.

The s1966 shape: a class C mentioned only in clauses over a role that never
occurs in a clause head (`ObjectPropertyDomain(:t :C)` with no assertion
of t), so that the certified EL worker's vacuous-role pruning deletes every
clause naming C, while some axiom gives owl:Thing a nontrivial superclass
(`Reflexive(r)` with `Q ≡ Self(r)`, `owl:Thing ⊑ X`, a role whose domain
covers everything). Non-EL axioms (cardinalities, disjunctions, Self,
disjoint roles) push the certificate into its repair and partial modes.
The family varies the vacuous roles (domain, range, existential and
universal positions, inverse pairs of unused roles, chains of sub-roles)
and the source of top-level superclasses.

usage: python3 -I gen_vacuous.py SEED OUT.ofn
"""
import random
import sys


def gen(seed):
    R = random.Random(seed * 104729 + 1966)
    C = ['A', 'B', 'C', 'D', 'E', 'F']
    S = ['r', 's', 'p']          # used roles
    V = ['t', 'u', 'v']          # head-free roles (never asserted)
    Q = ['Q%d' % i for i in range(1, R.randint(3, 6))]
    lone = R.sample(C, R.randint(1, 3))       # classes kept next to V only
    rest = [c for c in C if c not in lone]

    def role(inv=.2):
        x = R.choice(S)
        return f'ObjectInverseOf(:{x})' if R.random() < inv else f':{x}'

    def atom():
        return ':' + R.choice(rest)

    def expr(d=0):
        k = R.randrange(10 if d < 2 else 2)
        if k == 0:
            return atom()
        if k == 1:
            return f'ObjectHasSelf(:{R.choice(S)})'
        if k == 2:
            return f'ObjectSomeValuesFrom({role()} {expr(d + 1)})'
        if k == 3:
            return f'ObjectAllValuesFrom({role()} {expr(d + 1)})'
        if k == 4:
            return f'ObjectIntersectionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 5:
            return f'ObjectUnionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 6:
            return f'ObjectMinCardinality({R.choice([1, 2])} {role()} {expr(d + 1)})'
        if k == 7:
            return f'ObjectMaxCardinality({R.choice([1, 2])} {role()} {expr(d + 1)})'
        if k == 8:
            return f'ObjectComplementOf({atom()})'
        return atom()

    ax = []
    # vacuous-role clauses around the lone classes
    for c in lone:
        for _ in range(R.randint(1, 2)):
            v = R.choice(V)
            k = R.randrange(6)
            if k == 0:
                ax.append(f'ObjectPropertyDomain(:{v} :{c})')
            elif k == 1:
                ax.append(f'ObjectPropertyRange(:{v} :{c})')
            elif k == 2:
                ax.append(f'SubClassOf(ObjectSomeValuesFrom(:{v} owl:Thing) :{c})')
            elif k == 3:
                ax.append(f'SubClassOf(ObjectSomeValuesFrom(:{v} :{c}) {atom()})')
            elif k == 4:
                ax.append(f'SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(:{v}) {atom()}) :{c})')
            else:
                ax.append(f'SubClassOf(:{c} ObjectAllValuesFrom(:{v} {atom()}))')
    for _ in range(R.randint(0, 2)):
        a, b = R.sample(V, 2)
        k = R.randrange(3)
        if k == 0:
            ax.append(f'InverseObjectProperties(:{a} :{b})')
        elif k == 1:
            ax.append(f'SubObjectPropertyOf(:{a} :{b})')
        else:
            ax.append(f'ObjectPropertyDomain(:{a} {atom()})')
    # sources of owl:Thing superclasses
    for _ in range(R.randint(1, 2)):
        k = R.randrange(5)
        if k == 0:
            r = R.choice(S)
            ax.append(f'ReflexiveObjectProperty(:{r})')
            ax.append(f'EquivalentClasses(:{R.choice(Q)} ObjectHasSelf(:{r}))')
        elif k == 1:
            ax.append(f'SubClassOf(owl:Thing {atom()})')
        elif k == 2:
            r = R.choice(S)
            ax.append(f'ReflexiveObjectProperty(:{r})')
            ax.append(f'ObjectPropertyDomain(:{r} {atom()})')
        elif k == 3:
            ax.append(f'SubClassOf(owl:Thing ObjectSomeValuesFrom({role()} {atom()}))')
            ax.append(f'SubClassOf(ObjectSomeValuesFrom({role()} {atom()}) {atom()})')
        else:
            r = R.choice(S)
            ax.append(f'ReflexiveObjectProperty(:{r})')
            ax.append(f'SubClassOf(ObjectHasSelf(:{r}) {atom()})')
    # ordinary and non-EL axioms over the other classes
    for _ in range(R.randint(2, 6)):
        k = R.randrange(5)
        if k == 0:
            ax.append(f'SubClassOf({atom()} {expr()})')
        elif k == 1:
            ax.append(f'SubClassOf({expr()} {atom()})')
        elif k == 2:
            ax.append(f'DisjointObjectProperties(:{R.choice(S)} :{R.choice(S)})')
        elif k == 3:
            ax.append(f'SubClassOf({atom()} ObjectUnionOf({atom()} {atom()}))')
        else:
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({role()} {expr(1)}))')
    for q in Q:
        k = R.randrange(4)
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectHasSelf(:{R.choice(S)}))')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} {expr(1)}))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} {expr()})')
        else:
            ax.append(f'SubClassOf(:{q} {expr()})')
    ax = [a.replace('DisjointObjectProperties(:r :r)', 'IrreflexiveObjectProperty(:r)')
           .replace('DisjointObjectProperties(:s :s)', 'IrreflexiveObjectProperty(:s)')
           .replace('DisjointObjectProperties(:p :p)', 'IrreflexiveObjectProperty(:p)') for a in ax]
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    R.shuffle(ax)
    decl = [f'Declaration(Class(:{c}))' for c in C + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in S + V]
    return ('Prefix(:=<http://example.org/vac#>)\nOntology(<http://example.org/vac>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
