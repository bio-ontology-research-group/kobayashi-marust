"""Seed families around m413 (agent bridge-m413, 2026-11-02): merges of
ABox nominals that only a class probe triggers, while the merged
individuals carry asserted edges into property chains and transitive
roles, and universal restrictions over those roles sit on the nominals.

family 0  functional role f below r (or t) with r o s -> t, t transitive;
          a probe class P with P <= some f.{a} and P <= some f.P (or
          P <= some f.X, X <= {a}) so that a P element pulls P onto a;
          a has an asserted f edge to b, so a and b merge in the probe;
          asserted s/t/r edges among the nominals; forall over t-, u or
          chain inverses on the nominals.
family 1  inverse-functional g: a probe class P <= some g.{a}, g(b, a)
          asserted, so the P element merges with b (or b's merge with a
          nominal follows); chain and transitive edges around b.
family 2  at-most on nominals: a hub h with an asserted r (or f) edge to b
          and h : (<= 1 r) or <= 1 r.C; a probe P <= some r-.{h} (P is an
          r-successor of h) merges P's element with b; or P <= {h}-style
          hooks; chains through b.
family 3  mixtures of 0-2 on the same ABox, with DisjointClasses,
          SameIndividual and DifferentIndividuals that can make probes
          unsatisfiable or the ABox inconsistent.

usage: python3 -I gen_m413.py SEED OUT.ofn   (family = SEED mod 4)
"""
import random
import sys


def gen(seed):
    R = random.Random(seed * 104729 + 7)
    fam = seed % 4
    n = R.randint(3, 7)
    IND = [f'i{k}' for k in range(n)]
    C = ['A', 'B', 'C', 'D', 'E']
    P = ['P1', 'P2', 'P3']
    Q = ['Q1', 'Q2', 'Q3', 'Q4']
    ax = ['TransitiveObjectProperty(:t)']
    if R.random() < .8:
        ax.append('SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)')
    else:
        ax.append('SubObjectPropertyOf(ObjectPropertyChain(:s :r) :t)')
    ax.append(R.choice(['SubObjectPropertyOf(:f :r)', 'SubObjectPropertyOf(:f :r)',
                        'SubObjectPropertyOf(:f :t)', 'SubObjectPropertyOf(:f :s)']))
    if R.random() < .4:
        ax.append('SubObjectPropertyOf(ObjectPropertyChain(:f :t) :u)')
    if R.random() < .3:
        ax.append('TransitiveObjectProperty(:u)')
    if R.random() < .4:
        ax.append('SubObjectPropertyOf(:g ' + R.choice([':t', ':r', ':s']) + ')')
    if R.random() < .3:
        ax.append('InverseObjectProperties(:s :si)')
    if fam in (0, 3) or R.random() < .5:
        ax.append('FunctionalObjectProperty(:f)')
    if fam in (1, 3) or R.random() < .3:
        ax.append('InverseFunctionalObjectProperty(:g)')
    if R.random() < .25:
        ax.append('DisjointClasses(:' + ' :'.join(R.sample(C, 2)) + ')')

    def ind():
        return R.choice(IND)

    def edge(p, x, y):
        ax.append(f'ObjectPropertyAssertion(:{p} :{x} :{y})')

    def crole():
        name = R.choice(['t', 't', 'u', 'r', 's'])
        if R.random() < .5:
            return f'ObjectInverseOf(:{name})'
        return f':{name}'

    def atom():
        return ':' + R.choice(C)

    for _ in range(R.randint(2, 5)):
        x, y = R.sample(IND, 2)
        edge(R.choice(['s', 't', 'r', 's', 'si']), x, y)

    def fam0(p):
        a, b = R.sample(IND, 2)
        ax.append(f'SubClassOf(:{p} ObjectSomeValuesFrom(:f ObjectOneOf(:{a})))')
        if R.random() < .6:
            ax.append(f'SubClassOf(:{p} ObjectSomeValuesFrom(:f :{p}))')
        else:
            x = R.choice(C)
            ax.append(f'SubClassOf(:{p} ObjectSomeValuesFrom(:f :{x}))')
            ax.append(f'SubClassOf(:{x} :{p})')
        edge('f', a, b)
        if R.random() < .7:
            edge('s', a, R.choice([x for x in IND if x != a]))
        if R.random() < .7:
            edge('t', R.choice(IND), b)

    def fam1(p):
        a, b = R.sample(IND, 2)
        ax.append(f'SubClassOf(:{p} ObjectSomeValuesFrom(:g ObjectOneOf(:{a})))')
        edge('g', b, a)
        if R.random() < .7:
            edge('s', b, R.choice(IND))
        if R.random() < .5:
            edge('t', R.choice(IND), b)
        if R.random() < .4:
            ax.append(f'SubClassOf(:{p} ObjectSomeValuesFrom(:f ObjectOneOf(:{b})))')

    def fam2(p):
        h, b = R.sample(IND, 2)
        rr = R.choice(['r', 'f', 's'])
        if R.random() < .5:
            ax.append(f'ClassAssertion(ObjectMaxCardinality(1 :{rr}) :{h})')
        else:
            c = R.choice(C)
            ax.append(f'ClassAssertion(ObjectMaxCardinality(1 :{rr} :{c}) :{h})')
            ax.append(f'ClassAssertion(:{c} :{b})')
            ax.append(f'SubClassOf(:{p} :{c})')
        edge(rr, h, b)
        ax.append(f'SubClassOf(:{p} ObjectSomeValuesFrom(ObjectInverseOf(:{rr}) ObjectOneOf(:{h})))')
        if R.random() < .7:
            edge('s', b, R.choice(IND))
        if R.random() < .5:
            edge('t', R.choice(IND), h)

    fams = [fam0, fam1, fam2]
    for p in P:
        if fam == 3:
            R.choice(fams)(p)
        elif R.random() < .75:
            fams[fam](p)
        else:
            R.choice(fams)(p)
    for _ in range(R.randint(1, 4)):
        x = ind()
        k = R.randrange(4)
        if k == 0:
            ax.append(f'ClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(:t) {atom()}) :{x})')
        elif k == 1:
            ax.append(f'ClassAssertion(ObjectAllValuesFrom({crole()} {atom()}) :{x})')
        elif k == 2:
            ax.append(f'ClassAssertion({atom()} :{x})')
        else:
            ax.append(f'ClassAssertion(ObjectAllValuesFrom(:t ObjectAllValuesFrom(ObjectInverseOf(:s) {atom()})) :{x})')
    for _ in range(R.randint(0, 3)):
        k = R.randrange(4)
        if k == 0:
            ax.append(f'SubClassOf({atom()} ObjectAllValuesFrom({crole()} {atom()}))')
        elif k == 1:
            ax.append(f'SubClassOf(ObjectSomeValuesFrom({crole()} {atom()}) {atom()})')
        elif k == 2:
            ax.append(f'SubClassOf(ObjectOneOf(:{ind()}) {atom()})')
        else:
            ax.append(f'SubClassOf({atom()} ObjectUnionOf({atom()} {atom()}))')
    if fam == 3 or R.random() < .15:
        if R.random() < .5:
            ax.append('SameIndividual(' + ' '.join(':' + i for i in R.sample(IND, 2)) + ')')
        else:
            ax.append('DifferentIndividuals(' + ' '.join(':' + i for i in R.sample(IND, 2)) + ')')
    for q in Q:
        k = R.randrange(4)
        if k == 0:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom(:t ObjectOneOf(:{ind()})))')
        elif k == 1:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom(:u ObjectOneOf(:{ind()})))')
        elif k == 2:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom(:f {atom()}))')
        else:
            ax.append(f'EquivalentClasses(:{q} ObjectSomeValuesFrom(:s ObjectOneOf(:{ind()})))')
    seen = set()
    ax = [a for a in ax if not (a in seen or seen.add(a))]
    decl = [f'Declaration(Class(:{c}))' for c in C + P + Q]
    decl += [f'Declaration(ObjectProperty(:{p}))' for p in ['r', 's', 't', 'u', 'f', 'g', 'si']]
    decl += [f'Declaration(NamedIndividual(:{i}))' for i in IND]
    return ('Prefix(:=<http://x#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'
            'Ontology(<http://x/k' + str(seed) + '>\n' + '\n'.join(decl + ax) + '\n)\n')


if __name__ == '__main__':
    with open(sys.argv[2], 'w') as f:
        f.write(gen(int(sys.argv[1])))
