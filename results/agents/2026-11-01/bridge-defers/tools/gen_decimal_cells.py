"""Random probes for dense decimal-tower cells on the native bridge.

usage: python3 -I gen_decimal_cells.py OUTDIR N [FIRST]

Each seed declares two data properties and mixes overlapping decimal facet
intervals (closed, open, half-bounded, a DataIntersectionOf of two facets of
one base), integer facet intervals, the named types xsd:decimal and
xsd:integer, integer and decimal values, counts, functional properties and
data assertions with ObjectHasValue/ObjectOneOf object content, so that the
frontend emits ordered decimal cells whose covers mix open gaps and point
values (the shape of ore_ont_4903 and ore_ont_11647).
"""
import os, random, sys

out, n = sys.argv[1], int(sys.argv[2])
first = int(sys.argv[3]) if len(sys.argv) > 3 else 0
os.makedirs(out, exist_ok=True)
H = """Prefix(:=<http://e.org/d#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://e.org/d/%s>
Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D)) Declaration(Class(:E))
Declaration(DataProperty(:p)) Declaration(DataProperty(:q)) Declaration(ObjectProperty(:r))
Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:o))
"""
CLASSES = ['A', 'B', 'C', 'D', 'E']
POINTS = ['-2', '0', '1', '1.5', '3', '12']


def num(rng, integral=False):
    v = rng.choice(['-2', '0', '1', '3', '12'] if integral else POINTS)
    if integral or '.' not in v and rng.random() < 0.5:
        return f'"{v}"^^xsd:integer'
    return f'"{v}"^^xsd:decimal'


def facet_range(rng, base):
    integral = base == 'xsd:integer'
    shape = rng.choice(['closed', 'open', 'lo', 'hi', 'half', 'half'])
    lo, hi = sorted(rng.sample(['-2', '0', '1', '3', '12'] if integral else POINTS, 2), key=float)
    lit = (lambda v: f'"{v}"^^xsd:integer') if integral or '.' not in lo + hi and rng.random() < 0.4 else (lambda v: f'"{v}"^^xsd:decimal')
    if shape == 'closed':
        f = f'xsd:minInclusive {lit(lo)} xsd:maxInclusive {lit(hi)}'
    elif shape == 'open':
        f = f'xsd:minExclusive {lit(lo)} xsd:maxExclusive {lit(hi)}'
    elif shape == 'lo':
        f = f'xsd:{rng.choice(["minInclusive", "minExclusive"])} {lit(lo)}'
    elif shape == 'hi':
        f = f'xsd:{rng.choice(["maxInclusive", "maxExclusive"])} {lit(hi)}'
    else:
        f = f'xsd:minInclusive {lit(lo)} xsd:maxExclusive {lit(hi)}'
    return f'DatatypeRestriction({base} {f})'


def data_range(rng):
    r = rng.random()
    if r < 0.5:
        return facet_range(rng, 'xsd:decimal')
    if r < 0.62:
        return facet_range(rng, 'xsd:integer')
    if r < 0.77:
        lo, hi = sorted(rng.sample(POINTS, 2), key=float)
        return (f'DataIntersectionOf(DatatypeRestriction(xsd:decimal xsd:maxInclusive "{hi}"^^xsd:decimal) '
                f'DatatypeRestriction(xsd:decimal xsd:minInclusive "{lo}"^^xsd:decimal))')
    if r < 0.85:
        return rng.choice(['xsd:decimal', 'xsd:integer'])
    return 'DataOneOf(' + ' '.join(num(rng) for _ in range(rng.choice([1, 2]))) + ')'


def axiom(rng):
    c = rng.choice(CLASSES)
    p = rng.choice([':p', ':p', ':q'])
    r = rng.random()
    if r < 0.22:
        return f"SubClassOf(:{c} DataSomeValuesFrom({p} {data_range(rng)}))"
    if r < 0.32:
        return f"SubClassOf(:{c} DataAllValuesFrom({p} {data_range(rng)}))"
    if r < 0.47:
        return f"EquivalentClasses(:{c} DataSomeValuesFrom({p} {data_range(rng)}))"
    if r < 0.52:
        return f"DataPropertyRange({p} {data_range(rng)})"
    if r < 0.57:
        return f"FunctionalDataProperty({p})"
    if r < 0.61:
        return f"SubClassOf(:{c} DataMinCardinality(2 {p} {data_range(rng)}))"
    if r < 0.65:
        return f"SubClassOf(:{c} DataMaxCardinality(1 {p} {data_range(rng)}))"
    if r < 0.73:
        return f"DataPropertyAssertion({p} :{rng.choice('ab')} {num(rng)})"
    if r < 0.79:
        return f"ClassAssertion(:{c} :{rng.choice('ab')})"
    if r < 0.85:
        return f"EquivalentClasses(:{c} DataHasValue({p} {num(rng)}))"
    if r < 0.9:
        return f"SubClassOf(:{c} ObjectHasValue(:r :o))"
    if r < 0.94:
        return f"SubClassOf(:{c} ObjectSomeValuesFrom(:r ObjectOneOf(:{rng.choice('abo')})))"
    return f"SubClassOf(:{c} :{rng.choice(CLASSES)})"


for i in range(first, first + n):
    rng = random.Random(f"dec-{i}")
    body = "\n".join(axiom(rng) for _ in range(rng.randint(4, 8)))
    name = f"dec{i:04d}"
    with open(os.path.join(out, name + ".ofn"), "w") as f:
        f.write(H % name + body + "\n)\n")
