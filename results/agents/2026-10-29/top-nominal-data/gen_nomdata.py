"""Random OWL 2 functional-syntax ontologies mixing nominals, data values,
at-most restrictions and disjunctions (per-context-order differential).

usage: python3 gen_nomdata.py SEED OUT.ofn [--no-inverse]

With --no-inverse no inverse role is generated (nominals, data values, at-most
restrictions and disjunctions without the inverse-role interaction that makes
the nominal CB route slow in every literal-order regime).
"""
import random
import sys


def gen(seed, inverse=True):
    R = random.Random(seed)
    C = ['A', 'B', 'C', 'D']
    Q = ['Q1', 'Q2', 'Q3']
    OP = ['r', 's', 't']
    DP = ['u', 'v']
    IND = ['a', 'b', 'c']

    def lit():
        if R.random() < .5:
            return f'"{R.randrange(0, 3)}"^^xsd:integer'
        return f'"{R.choice("xy")}"^^xsd:string'

    def drange():
        k = R.randrange(5)
        if k == 0:
            return 'xsd:integer'
        if k == 1:
            return 'xsd:string'
        if k == 2:
            return f'DataOneOf({lit()} {lit()})'
        if k == 3:
            return 'DataComplementOf(xsd:integer)'
        return 'rdfs:Literal'

    def role():
        p = R.choice(OP)
        return f'ObjectInverseOf(:{p})' if inverse and R.random() < .15 else f':{p}'

    def nom():
        n = R.randrange(1, 3)
        return 'ObjectOneOf(' + ' '.join(':' + i for i in R.sample(IND, n)) + ')'

    def cls(d=0):
        k = R.randrange(17 if d < 2 else 6)
        if k < 3:
            return ':' + R.choice(C)
        if k == 3:
            return nom()
        if k == 4:
            return f'ObjectHasValue({role()} :{R.choice(IND)})'
        if k == 5:
            return f'DataHasValue(:{R.choice(DP)} {lit()})'
        if k == 6:
            return f'ObjectSomeValuesFrom({role()} {cls(d + 1)})'
        if k == 7:
            return f'ObjectAllValuesFrom({role()} {cls(d + 1)})'
        if k == 8:
            return f'ObjectComplementOf({cls(d + 1)})'
        if k == 9:
            return f'ObjectIntersectionOf({cls(d + 1)} {cls(d + 1)})'
        if k in (10, 11):
            return f'ObjectUnionOf({cls(d + 1)} {cls(d + 1)})'
        if k == 12:
            n = R.randrange(0, 3)
            return f'ObjectMaxCardinality({n} {role()} {cls(d + 1)})'
        if k == 13:
            n = R.randrange(1, 3)
            return f'ObjectMinCardinality({n} {role()} {cls(d + 1)})'
        if k == 14:
            return f'DataSomeValuesFrom(:{R.choice(DP)} {drange()})'
        if k == 15:
            n = R.randrange(0, 3)
            return f'DataMaxCardinality({n} :{R.choice(DP)})'
        return f'DataMinCardinality({R.randrange(1, 3)} :{R.choice(DP)})'

    ax = []
    for _ in range(R.randrange(4, 10)):
        k = R.randrange(14)
        if k < 5:
            ax.append(f'SubClassOf({cls()} {cls()})')
        elif k == 5:
            ax.append(f'SubClassOf(owl:Thing {cls()})')
        elif k == 6:
            ax.append(f'DisjointClasses({cls()} {cls()})')
        elif k == 7:
            ax.append(f'FunctionalObjectProperty(:{R.choice(OP)})')
        elif k == 8:
            ax.append(f'ClassAssertion({cls()} :{R.choice(IND)})')
        elif k == 9:
            ax.append(f'ObjectPropertyAssertion(:{R.choice(OP)} :{R.choice(IND)} :{R.choice(IND)})')
        elif k == 10:
            ax.append(f'DataPropertyAssertion(:{R.choice(DP)} :{R.choice(IND)} {lit()})')
        elif k == 11:
            ax.append(f'DataPropertyDomain(:{R.choice(DP)} {cls(1)})')
        elif k == 12:
            ax.append(f'FunctionalDataProperty(:{R.choice(DP)})')
        else:
            ax.append(f'EquivalentClasses(:{R.choice(C)} {cls()})')
    for q in Q:
        ax.append(f'EquivalentClasses(:{q} {cls()})')
    decl = ' '.join([f'Declaration(Class(:{c}))' for c in C + Q]
                    + [f'Declaration(ObjectProperty(:{p}))' for p in OP]
                    + [f'Declaration(DataProperty(:{p}))' for p in DP]
                    + [f'Declaration(NamedIndividual(:{i}))' for i in IND])
    return ('Prefix(:=<http://example.org/g#>)\n'
            'Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'
            'Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n'
            'Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n'
            f'Ontology(<http://example.org/g>\n{decl}\n' + '\n'.join(ax) + '\n)\n')


if __name__ == '__main__':
    with open(sys.argv[2], 'w') as out:
        out.write(gen(int(sys.argv[1]), inverse='--no-inverse' not in sys.argv[3:]))
