"""Rule-consistency seeds in the finite data-rule fragment (the ore_ont_7278
shape): full IRIs, an object TBox with nominals, an ABox with object and data
assertions, DataPropertyRange/Domain/Functional axioms, and DL-safe rules
whose data atoms are compared with swrlb builtins. The frontend grounds the
rules over the asserted values, which turns on nominal clausification and the
sort encoding, and the automatic route runs the rule-consistency worker.

usage: python3 -I gen_finite_rules.py SEED OUT.ofn
"""
import random
import sys

NS = 'http://example.org/f#'
SWRLB = 'http://www.w3.org/2003/11/swrlb#'


def gen(seed):
    R = random.Random(seed)
    C = ['A', 'B', 'C', 'D', 'E']
    OP = ['r', 's', 't']
    DP = {'u': 'integer', 'v': 'integer', 'w': 'integer'}
    IND = ['a', 'b', 'c', 'd']
    iri = lambda n: f'<{NS}{n}>'
    var = lambda n: f'Variable(<{NS}var_{n}>)'

    def lit(p):
        # Integer literals only: a string value defers the rule grounding.
        return f'"{R.randrange(0, 5)}"^^xsd:integer'

    def cls(d=0):
        k = R.randrange(11 if d < 2 else 3)
        if k < 3:
            return iri(R.choice(C))
        if k == 3:
            return 'ObjectOneOf(' + ' '.join(iri(i) for i in R.sample(IND, R.randrange(1, 3))) + ')'
        if k == 4:
            return f'ObjectSomeValuesFrom({iri(R.choice(OP))} {cls(d + 1)})'
        if k == 5:
            return f'ObjectAllValuesFrom({iri(R.choice(OP))} {cls(d + 1)})'
        if k == 6:
            return f'ObjectComplementOf({cls(d + 1)})'
        if k == 7:
            return f'ObjectIntersectionOf({cls(d + 1)} {cls(d + 1)})'
        if k == 8:
            return f'ObjectUnionOf({cls(d + 1)} {cls(d + 1)})'
        if k == 9:
            return f'ObjectMaxCardinality({R.randrange(0, 3)} {iri(R.choice(OP))} {cls(d + 1)})'
        return f'ObjectHasValue({iri(R.choice(OP))} {iri(R.choice(IND))})'

    ax = []
    for _ in range(R.randrange(3, 8)):
        k = R.randrange(10)
        if k < 4:
            ax.append(f'SubClassOf({cls()} {cls()})')
        elif k == 4:
            ax.append(f'SubClassOf(owl:Thing {cls(1)})')
        elif k == 5:
            ax.append(f'DisjointClasses({cls(1)} {cls(1)})')
        elif k == 6:
            ax.append(f'FunctionalObjectProperty({iri(R.choice(OP))})')
        elif k == 7:
            ax.append(f'ObjectPropertyDomain({iri(R.choice(OP))} {cls(1)})')
        else:
            ax.append(f'EquivalentClasses({iri(R.choice(C))} {cls()})')
    for p, kind in DP.items():
        if R.random() < .8:
            ax.append(f'DataPropertyRange({iri(p)} xsd:{kind if R.random() < .85 else "double"})')
        if R.random() < .3:
            ax.append(f'DataPropertyDomain({iri(p)} {iri(R.choice(C))})')
        if R.random() < .3:
            ax.append(f'FunctionalDataProperty({iri(p)})')
    for _ in range(R.randrange(2, 7)):
        ax.append(f'ClassAssertion({iri(R.choice(C))} {iri(R.choice(IND))})')
    for _ in range(R.randrange(2, 7)):
        ax.append(f'ObjectPropertyAssertion({iri(R.choice(OP))} {iri(R.choice(IND))} {iri(R.choice(IND))})')
    for _ in range(R.randrange(2, 8)):
        p = R.choice(list(DP))
        ax.append(f'DataPropertyAssertion({iri(p)} {iri(R.choice(IND))} {lit(p)})')
    for _ in range(R.randrange(1, 4)):
        p = R.choice(list(DP))
        body = [f'ObjectPropertyAtom({iri(R.choice(OP))} {var("x")} {var("y")})',
                f'DataPropertyAtom({iri(p)} {var(R.choice("xy"))} {var("n")})']
        if R.random() < .5:
            body.append(f'ClassAtom({iri(R.choice(C))} {var(R.choice("xy"))})')
        op = R.choice(['equal', 'notEqual', 'lessThan', 'greaterThan', 'greaterThanOrEqual'])
        value = f'"{R.randrange(0, 5)}"^^xsd:integer'
        body.append(f'BuiltInAtom(<{SWRLB}{op}> {var("n")} {value})')
        if R.random() < .7:
            head = f'ClassAtom({iri(R.choice(C))} {var(R.choice("xy"))})'
        else:
            head = f'ObjectPropertyAtom({iri(R.choice(OP))} {var("y")} {var("x")})'
        ax.append(f'DLSafeRule(Body({" ".join(body)}) Head({head}))')
    decl = ' '.join([f'Declaration(Class({iri(c)}))' for c in C]
                    + [f'Declaration(ObjectProperty({iri(p)}))' for p in OP]
                    + [f'Declaration(DataProperty({iri(p)}))' for p in DP]
                    + [f'Declaration(NamedIndividual({iri(i)}))' for i in IND])
    return ('Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'
            'Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n'
            'Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n'
            f'Ontology(<http://example.org/f>\n{decl}\n' + '\n'.join(ax) + '\n)\n')


if __name__ == '__main__':
    with open(sys.argv[2], 'w') as out:
        out.write(gen(int(sys.argv[1])))
