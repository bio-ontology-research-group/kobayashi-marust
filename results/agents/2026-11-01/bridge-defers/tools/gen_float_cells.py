"""Random probes for the IEEE cell path of the native bridge.

usage: python3 -I gen_float_cells.py OUTDIR N [FIRST]

Most seeds put 17 to 22 overlapping xsd:float facet intervals on one data
property (EquivalentClasses with DataSomeValuesFrom; ore_ont_11647 puts all
its float ranges on muo:numericalValue), so that one width carries more than
sixteen ranges; one seed in five spreads them over two properties, whose
cells then overlap across role groups (the bridge must defer or decide them
by the label enumeration). It adds functional properties, counts, data
assertions, value restrictions and an object part with ObjectHasValue.
All endpoints are exact binary32 values.
"""
import os, random, sys

out, n = sys.argv[1], int(sys.argv[2])
first = int(sys.argv[3]) if len(sys.argv) > 3 else 0
os.makedirs(out, exist_ok=True)
PROPS = ['p', 'q', 's', 'u']
POINTS = ['-12.0', '-6.0', '0.0', '0.5', '1.0', '2.5', '10.0', '20.0', '25.0', '30.0']
H = """Prefix(:=<http://e.org/f#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://e.org/f/%s>
""" + "".join(f"Declaration(DataProperty(:{p}))\n" for p in PROPS) + """Declaration(ObjectProperty(:r))
Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:o))
"""


def lit(v):
    return f'"{v}"^^xsd:float'


def facet(rng, pts):
    shape = rng.choice(['lo', 'hi', 'closed', 'half', 'open'])
    lo, hi = sorted(rng.sample(pts, 2), key=float)
    if shape == 'lo':
        return f'DatatypeRestriction(xsd:float xsd:{rng.choice(["minInclusive", "minExclusive"])} {lit(lo)})'
    if shape == 'hi':
        return f'DatatypeRestriction(xsd:float xsd:{rng.choice(["maxInclusive", "maxExclusive"])} {lit(hi)})'
    if shape == 'closed':
        return f'DatatypeRestriction(xsd:float xsd:minInclusive {lit(lo)} xsd:maxInclusive {lit(hi)})'
    if shape == 'open':
        return f'DatatypeRestriction(xsd:float xsd:minExclusive {lit(lo)} xsd:maxExclusive {lit(hi)})'
    return f'DatatypeRestriction(xsd:float xsd:minInclusive {lit(lo)} xsd:maxExclusive {lit(hi)})'


for i in range(first, first + n):
    rng = random.Random(f"flt-{i}")
    axioms, classes = [], []
    split = rng.random() < 0.2
    for p in (PROPS[:2] if split else PROPS[:1]):
        pts = rng.sample(POINTS, 7)
        for k in range(rng.randint(9, 11) if split else rng.randint(17, 22)):
            c = f'{p.upper()}{k}'
            classes.append(c)
            axioms.append(f'EquivalentClasses(:{c} DataSomeValuesFrom(:{p} {facet(rng, pts)}))')
        if rng.random() < 0.6:
            axioms.append(f'FunctionalDataProperty(:{p})')
        if rng.random() < 0.3:
            axioms.append(f'DataPropertyRange(:{p} xsd:float)')
    for _ in range(rng.randint(3, 7)):
        r = rng.random()
        c, d = rng.choice(classes), rng.choice(classes)
        p = rng.choice(PROPS[:2] if split else PROPS[:1])
        if r < 0.25:
            axioms.append(f'SubClassOf(:{c} :{d})')
        elif r < 0.4:
            axioms.append(f'SubClassOf(:{c} DataAllValuesFrom(:{p} {facet(rng, POINTS)}))')
        elif r < 0.5:
            axioms.append(f'SubClassOf(:{c} DataMinCardinality(2 :{p} {facet(rng, POINTS)}))')
        elif r < 0.65:
            axioms.append(f'DataPropertyAssertion(:{p} :{rng.choice("ab")} {lit(rng.choice(POINTS))})')
        elif r < 0.75:
            axioms.append(f'ClassAssertion(:{c} :{rng.choice("ab")})')
        elif r < 0.85:
            axioms.append(f'EquivalentClasses(:{c} DataHasValue(:{p} {lit(rng.choice(POINTS))}))')
        else:
            axioms.append(f'SubClassOf(:{c} ObjectHasValue(:r :o))')
    decl = "".join(f"Declaration(Class(:{c}))\n" for c in classes)
    name = f"flt{i:04d}"
    with open(os.path.join(out, name + ".ofn"), "w") as f:
        f.write(H % name + decl + "\n".join(axioms) + "\n)\n")
