"""Seed family for the saturation SELF rule (docs/HYBRID-CB-HT.md section 20).

Small TBox-centred ontologies with ObjectHasSelf: self-restrictions under
existentials, universals and cardinalities, on inverse roles, combined with
role hierarchies (sub-, inverse- and equivalent properties), a transitive
role, domains and ranges, functional / inverse-functional, reflexive,
irreflexive and asymmetric roles, disjoint roles, nominals (ObjectOneOf,
ObjectHasValue) and disjunctions. Most seeds carry no ABox so that the
classification runs through the concept saturation; about a quarter add a
few assertions.

Even seeds are Horn ("decidable by saturation"): no unions, no negated
atoms or self restrictions, no at-most restrictions inside class expressions, and irreflexive / asymmetric / disjoint roles
only rarely, so that the concept saturation decides most classes. Odd seeds
use the full mix (negated self restrictions, unions, all role axioms).

OWL 2 DL global restrictions: only the simple roles r, s, p (never a
super-property of t, never in a chain) occur in self restrictions, number
restrictions, functional, irreflexive, asymmetric and disjointness axioms.
The transitive role t has sub-properties among the simple roles only.

usage: python3 -I gen_self.py SEED OUT.ofn
"""
import random
import sys


def gen(seed):
    R = random.Random(seed)
    C = ['A', 'B', 'C', 'D', 'E', 'F']
    SIMPLE = ['r', 's', 'p']
    ALLR = SIMPLE + ['t']
    IND = ['a', 'b', 'c']
    Q = ['Q%d' % i for i in range(1, R.randint(4, 8))]
    horn = seed % 2 == 0
    nominals = R.random() < .25
    abox = R.random() < .25

    def srole(inv=.25):
        x = R.choice(SIMPLE)
        return f'ObjectInverseOf(:{x})' if R.random() < inv else f':{x}'

    def arole(inv=.2):
        x = R.choice(ALLR)
        return f'ObjectInverseOf(:{x})' if R.random() < inv else f':{x}'

    def atom():
        return ':' + R.choice(C)

    def lit():
        return f'ObjectComplementOf({atom()})' if not horn and R.random() < .2 else atom()

    def selfc():
        # The frontend takes a named role in ObjectHasSelf (Self(R-) is
        # Self(R)); srole(0) keeps the random sequence of srole().
        e = f'ObjectHasSelf({srole(0)})'
        return f'ObjectComplementOf({e})' if not horn and R.random() < .15 else e

    def expr(d=0):
        k = R.randrange(12 if d < 2 else 3)
        if k == 0:
            return lit()
        if k == 1 or k == 2:
            return selfc()
        if k == 3:
            return f'ObjectSomeValuesFrom({arole()} {expr(d + 1)})'
        if k == 4:
            return f'ObjectAllValuesFrom({arole()} {expr(d + 1)})'
        if k == 5:
            return f'ObjectIntersectionOf({expr(d + 1)} {expr(d + 1)})'
        if k == 6 and horn:
            return f'ObjectIntersectionOf({atom()} {selfc()})'
        if k == 6:
            return f'ObjectUnionOf({expr(d + 1)} {expr(d + 1)})'
        if horn and k in (7, 11):
            return f'ObjectMinCardinality(1 {srole()} {selfc()})'
        if k == 7:
            return f'ObjectMaxCardinality({R.choice([0, 1, 1, 2])} {srole()} {expr(d + 1)})'
        if k == 8:
            return f'ObjectMinCardinality({R.choice([1, 2])} {srole()} {expr(d + 1)})'
        if k == 9:
            return f'ObjectSomeValuesFrom({srole()} {selfc()})'
        if k == 10:
            if nominals:
                return (f'ObjectHasValue({arole(0.1)} :{R.choice(IND)})' if R.random() < .5
                        else f'ObjectOneOf(:{R.choice(IND)})')
            return f'ObjectAllValuesFrom({srole()} {selfc()})'
        return f'ObjectMaxCardinality(1 {srole()})'

    ax = []
    for _ in range(R.randint(3, 8)):
        k = R.randrange(7)
        if k == 0:
            ax.append(f'SubClassOf({atom()} {expr()})')
        elif k == 1:
            ax.append(f'SubClassOf({expr()} {atom()})')
        elif k == 2:
            ax.append(f'SubClassOf({atom()} {selfc()})')
        elif k == 3:
            ax.append(f'SubClassOf({selfc()} {atom()})')
        elif k == 4 and horn:
            ax.append(f'SubClassOf(ObjectIntersectionOf({atom()} {selfc()}) {atom()})')
        elif k == 4:
            ax.append(f'SubClassOf({atom()} ObjectUnionOf({atom()} {selfc()}))')
        elif k == 5:
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({arole()} {lit()}))')
        else:
            ax.append(f'SubClassOf({atom()} ObjectSomeValuesFrom({arole()} {expr(1)}))')
    # RBox
    for _ in range(R.randint(1, 5)):
        k = R.randrange(13)
        if horn and k >= 10 and R.random() < .85:
            k = R.randrange(10)
        a, b = R.sample(SIMPLE, 2)
        if k == 0:
            ax.append(f'SubObjectPropertyOf(:{a} :{b})')
        elif k == 1:
            # the frontend takes named roles in SubObjectPropertyOf
            ax.append(f'EquivalentObjectProperties(:{a} :{b})')
        elif k == 2:
            ax.append(f'InverseObjectProperties(:{a} :{b})')
        elif k == 3:
            ax.append(f'SubObjectPropertyOf(:{a} :t)')
        elif k == 4:
            ax.append('TransitiveObjectProperty(:t)')
        elif k == 5:
            ax.append(f'ObjectPropertyDomain({arole(0)} {lit()})')
        elif k == 6:
            ax.append(f'ObjectPropertyRange({arole(0)} {lit()})')
        elif k == 7:
            ax.append(f'FunctionalObjectProperty(:{a})')
        elif k == 8:
            ax.append(f'InverseFunctionalObjectProperty(:{a})')
        elif k == 9:
            ax.append(f'ReflexiveObjectProperty({arole(0)})')
        elif k == 10:
            ax.append(f'IrreflexiveObjectProperty(:{a})')
        elif k == 11:
            ax.append(f'AsymmetricObjectProperty(:{a})')
        else:
            ax.append(f'DisjointObjectProperties(:{a} :{b})')
    if abox:
        for _ in range(R.randint(1, 3)):
            ax.append(f'ClassAssertion({lit()} :{R.choice(IND)})')
        for _ in range(R.randint(0, 2)):
            ax.append(f'ObjectPropertyAssertion(:{R.choice(SIMPLE)} :{R.choice(IND)} :{R.choice(IND)})')
    # query classes
    for q in Q:
        k = R.randrange(5)
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} {selfc()})')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{q} ObjectIntersectionOf({atom()} {expr(1)}))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} {expr()})')
        elif k == 3:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom({arole()} {expr(1)}))')
        else:
            ax.append(f'SubClassOf(:{q} {expr()})')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    R.shuffle(ax)
    decl = [f'Declaration(Class(:{c}))' for c in C + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in ALLR]
    decl += [f'Declaration(NamedIndividual(:{i}))' for i in IND]
    return ('Prefix(:=<http://example.org/self#>)\nOntology(<http://example.org/self>\n'
            + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    open(sys.argv[2], 'w').write(gen(int(sys.argv[1])))
