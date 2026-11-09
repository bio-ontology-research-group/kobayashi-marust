"""Hand-built motifs that put a disjunctive ground equality o = o' (or
o = o' or C(p)) into the ground context while the query context of Q
announces only o; individual names, axiom order (hence interning order and
equality orientation) and a few noise axioms are randomised.

usage: python3 -I gen_tpl.py SEED OUT.ofn

Motifs (entailment Q SubClassOf E in each, checked by HermiT anyway):
 m1  p: <=1 r.B, r(p,o), r(p,o'), o: B or C, B(o'), D(o'), C,D => E
 m2  Functional(r), r(p,o'), p: C' or (r value o), C' => all s.E, s(p,o), D(o')
 m3  o: {o'} or {o2} or C, D(o'), D(o2)
 m4  p: (<=1 r) or M, M => all r.E, r(p,o), r(p,o'), D(o')
 m5  m2 with InverseFunctional(r) and r(o',p) / r(o,p) (inverse roles)
 m6  p: (<=1 r) or M, M => all s.E, s(p,o), r(p,o1), r(p,o2), o1 != o2
     (ground equality between two unannounced individuals: E(o) or o1 = o2)
 m7  p: (<=1 r) or (<=1 s), r(p,o), r(p,o'), s(p,o1), s(p,o2), o1 != o2,
     D(o') (o = o' or o1 = o2)
With --family2 the motif is drawn from m6 and m7 only.
"""
import random
import sys


def gen(seed, family2=False):
    R = random.Random(seed)
    names = R.sample(['a', 'b', 'c', 'd', 'e', 'f'], 5)
    o, o1, p, o2, z = names
    m = R.choice(['m6', 'm7'] if family2 else ['m1', 'm2', 'm3', 'm4', 'm5'])
    ax = ['SubClassOf(:D :E)', f'SubClassOf(:Q ObjectOneOf(:{o}))']
    if m == 'm1':
        ax += [f'ClassAssertion(ObjectMaxCardinality(1 :r :B) :{p})',
               f'ObjectPropertyAssertion(:r :{p} :{o})', f'ObjectPropertyAssertion(:r :{p} :{o1})',
               f'ClassAssertion(ObjectUnionOf(:B :C) :{o})', f'ClassAssertion(:B :{o1})',
               f'ClassAssertion(:D :{o1})', 'SubClassOf(:C :E)']
    elif m in ('m2', 'm5'):
        ax += ['FunctionalObjectProperty(:r)', f'ObjectPropertyAssertion(:r :{p} :{o1})',
               f'ClassAssertion(ObjectUnionOf(:C ObjectHasValue(:r :{o})) :{p})',
               'SubClassOf(:C ObjectAllValuesFrom(:s :E))', f'ObjectPropertyAssertion(:s :{p} :{o})',
               f'ClassAssertion(:D :{o1})']
        if m == 'm5':
            ax[2:4] = ['InverseFunctionalObjectProperty(:t)', f'ObjectPropertyAssertion(:t :{o1} :{p})']
            ax[4] = f'ClassAssertion(ObjectUnionOf(:C ObjectHasValue(ObjectInverseOf(:t) :{o})) :{p})'
            ax.insert(2, 'FunctionalObjectProperty(:r)')
    elif m == 'm3':
        ax += [f'ClassAssertion(ObjectUnionOf(ObjectOneOf(:{o1} :{o2}) :C) :{o})',
               f'ClassAssertion(:D :{o1})', f'ClassAssertion(:D :{o2})', 'SubClassOf(:C :E)']
    elif m == 'm6':
        ax += [f'ClassAssertion(ObjectUnionOf(ObjectMaxCardinality(1 :r) :M) :{p})',
               'SubClassOf(:M ObjectAllValuesFrom(:s :E))', f'ObjectPropertyAssertion(:s :{p} :{o})',
               f'ObjectPropertyAssertion(:r :{p} :{o1})', f'ObjectPropertyAssertion(:r :{p} :{o2})',
               f'DifferentIndividuals(:{o1} :{o2})']
    elif m == 'm7':
        ax += [f'ClassAssertion(ObjectUnionOf(ObjectMaxCardinality(1 :r) ObjectMaxCardinality(1 :s)) :{p})',
               f'ObjectPropertyAssertion(:r :{p} :{o})', f'ObjectPropertyAssertion(:r :{p} :{z})',
               f'ObjectPropertyAssertion(:s :{p} :{o1})', f'ObjectPropertyAssertion(:s :{p} :{o2})',
               f'DifferentIndividuals(:{o1} :{o2})', f'ClassAssertion(:D :{z})']
    else:
        ax += [f'ClassAssertion(ObjectUnionOf(ObjectMaxCardinality(1 :r) :M) :{p})',
               'SubClassOf(:M ObjectAllValuesFrom(:r :E))',
               f'ObjectPropertyAssertion(:r :{p} :{o})', f'ObjectPropertyAssertion(:r :{p} :{o1})',
               f'ClassAssertion(:D :{o1})']
    # Noise: unrelated facts that change interning and context traffic.
    for _ in range(R.randint(0, 3)):
        k = R.randrange(4)
        i, j = R.sample(names, 2)
        if k == 0:
            ax.append(f'ObjectPropertyAssertion(:s :{i} :{j})')
        elif k == 1:
            ax.append(f'ClassAssertion(:{R.choice("ABCDM")} :{i})')
        elif k == 2:
            ax.append(f'SubClassOf(:Q2 ObjectOneOf(:{i}))')
        else:
            ax.append(f'SubClassOf(:{R.choice("ABM")} ObjectSomeValuesFrom(:s :{R.choice("BCD")}))')
    R.shuffle(ax)
    decl = ([f'Declaration(Class(:{c}))' for c in 'ABCDEMQ'] + ['Declaration(Class(:Q2))']
            + [f'Declaration(ObjectProperty(:{r}))' for r in 'rst']
            + [f'Declaration(NamedIndividual(:{i}))' for i in names])
    R.shuffle(decl)
    return ('Prefix(:=<http://example.org/tpl#>)\nOntology(<http://example.org/tpl>\n'
            + '\n'.join(decl + ax) + '\n)\n'), m


if __name__ == '__main__':
    text, motif = gen(int(sys.argv[1]), '--family2' in sys.argv)
    with open(sys.argv[2], 'w') as f:
        f.write(text)
    print(motif)
