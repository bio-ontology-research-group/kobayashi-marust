"""Random probes for dateTime bounds and rdf:XMLLiteral values.

usage: python3 -I gen_seeds.py OUTDIR KIND N [FIRST]
KIND is `dt` (dateTime facets, timezone mixes near the fourteen-hour rule,
cells, counts) or `xml` (XMLLiteral identity against strings and other
XMLLiterals). The bounds and values avoid midnight and zero seconds (HermiT
counts `T24:00:00` as a value of its own, XSD 1.1 does not) and use at most
millisecond fractions (HermiT keeps milliseconds).
"""
import os, random, sys

out, kind, n = sys.argv[1], sys.argv[2], int(sys.argv[3])
first = int(sys.argv[4]) if len(sys.argv) > 4 else 0
os.makedirs(out, exist_ok=True)
H = """Prefix(:=<http://e.org/s#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
Ontology(<http://e.org/s/%s>
Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D)) Declaration(Class(:E))
Declaration(DataProperty(:p)) Declaration(DataProperty(:q))
Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
"""
CLASSES = ['A', 'B', 'C', 'D', 'E']


def civil(days):
    """Proleptic Gregorian date of a day number (days since 1970-01-01)."""
    z = days + 719468
    era = z // 146097
    doe = z - era * 146097
    yoe = (doe - doe // 1460 + doe // 36524 - doe // 146096) // 365
    y = yoe + era * 400
    doy = doe - (365 * yoe + yoe // 4 - yoe // 100)
    mp = (5 * doy + 2) // 153
    d = doy - (153 * mp + 2) // 5 + 1
    m = mp + 3 if mp < 10 else mp - 9
    return y + (m <= 2), m, d


def dt_literal(rng, zoned=False):
    # Local wall-clock seconds around 2020-06-15T10:20:15 (never midnight,
    # never zero seconds), and a timezone form.
    base = 18428 * 86400 + 10 * 3600 + 20 * 60 + 15
    shift = rng.choice([-30, -15, -14, -13, -2, -1, 0, 0, 1, 2, 13, 14, 15, 30]) * 3600
    shift += rng.choice([0, 0, 0, 1, -1, 1800])
    secs = base + shift
    frac = rng.choice(['', '', '', '.5', '.25', '.125'])
    days, sod = divmod(secs, 86400)
    y, m, d = civil(days)
    zone = rng.choice(([] if zoned else ['', '']) + ['Z', 'Z', '+01:00', '-05:00', '+14:00', '-14:00', '+05:30'])
    return f'"{y:04d}-{m:02d}-{d:02d}T{sod // 3600:02d}:{sod // 60 % 60:02d}:{sod % 60:02d}{frac}{zone}"^^xsd:dateTime'


def dt_range(rng, depth=0):
    r = rng.random()
    if r < 0.45 or depth > 1:
        base = rng.choice(['xsd:dateTime', 'xsd:dateTime', 'xsd:dateTimeStamp'])
        facets = rng.sample(['minInclusive', 'minExclusive', 'maxInclusive', 'maxExclusive'], rng.choice([1, 1, 2]))
        return f"DatatypeRestriction({base} " + " ".join(f"xsd:{f} {dt_literal(rng, base == 'xsd:dateTimeStamp')}" for f in facets) + ")"
    if r < 0.55:
        return rng.choice(['xsd:dateTime', 'xsd:dateTimeStamp'])
    if r < 0.7:
        return f"DataComplementOf({dt_range(rng, depth + 1)})"
    if r < 0.82:
        return f"DataIntersectionOf({dt_range(rng, depth + 1)} {dt_range(rng, depth + 1)})"
    if r < 0.9:
        return f"DataUnionOf({dt_range(rng, depth + 1)} {dt_range(rng, depth + 1)})"
    return "DataOneOf(" + " ".join(dt_literal(rng) for _ in range(rng.choice([1, 2]))) + ")"


XML = ['"a"^^rdf:XMLLiteral', '"b"^^rdf:XMLLiteral', '"<b>x</b>"^^rdf:XMLLiteral', '"<b>y</b>"^^rdf:XMLLiteral',
       '"x &amp; y"^^rdf:XMLLiteral', '"wèi le"^^rdf:XMLLiteral', '"\n <i>g</i>\n"^^rdf:XMLLiteral']
STR = ['"a"', '"b"', '"wèi le"', '"a"^^xsd:string']


def xml_literal(rng):
    return rng.choice(XML + XML + STR)


def xml_range(rng, depth=0):
    r = rng.random()
    if r < 0.3 or depth > 1:
        return rng.choice(['rdf:XMLLiteral', 'rdf:XMLLiteral', 'xsd:string', 'rdf:PlainLiteral'])
    if r < 0.55:
        return "DataOneOf(" + " ".join(xml_literal(rng) for _ in range(rng.choice([1, 2, 3]))) + ")"
    if r < 0.75:
        return f"DataComplementOf({xml_range(rng, depth + 1)})"
    if r < 0.88:
        return f"DataIntersectionOf({xml_range(rng, depth + 1)} {xml_range(rng, depth + 1)})"
    return f"DataUnionOf({xml_range(rng, depth + 1)} {xml_range(rng, depth + 1)})"


def axiom(rng, lit, rng_range):
    c = rng.choice(CLASSES)
    p = rng.choice([':p', ':p', ':q'])
    r = rng.random()
    if r < 0.18:
        return f"SubClassOf(:{c} DataSomeValuesFrom({p} {rng_range(rng)}))"
    if r < 0.3:
        return f"SubClassOf(:{c} DataAllValuesFrom({p} {rng_range(rng)}))"
    if r < 0.45:
        return f"EquivalentClasses(:{c} DataSomeValuesFrom({p} {rng_range(rng)}))"
    if r < 0.52:
        return f"DataPropertyRange({p} {rng_range(rng)})"
    if r < 0.58:
        return f"FunctionalDataProperty({p})"
    if r < 0.63:
        return f"SubClassOf(:{c} DataMinCardinality(2 {p} {rng_range(rng)}))"
    if r < 0.68:
        return f"SubClassOf(:{c} DataMaxCardinality(1 {p} {rng_range(rng)}))"
    if r < 0.8:
        return f"DataPropertyAssertion({p} :{rng.choice('ab')} {lit(rng)})"
    if r < 0.88:
        return f"ClassAssertion(:{c} :{rng.choice('ab')})"
    if r < 0.95:
        return f"EquivalentClasses(:{c} DataHasValue({p} {lit(rng)}))"
    return f"SubClassOf(:{c} :{rng.choice(CLASSES)})"


for i in range(first, first + n):
    rng = random.Random(f"{kind}-{i}")
    lit, rr = (dt_literal, dt_range) if kind == 'dt' else (xml_literal, xml_range)
    body = "\n".join(axiom(rng, lit, rr) for _ in range(rng.randint(3, 7)))
    name = f"{kind}{i:04d}"
    with open(os.path.join(out, name + ".ofn"), "w") as f:
        f.write(H % name + body + "\n)\n")
