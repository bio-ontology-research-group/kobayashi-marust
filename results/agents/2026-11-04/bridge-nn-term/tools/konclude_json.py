"""Convert a Konclude OWL/XML classification output to the KM/HermiT json shape.

usage: python3 -I konclude_json.py OUT.owl [LOG] > out.json
Subsumptions are the reflexive-transitive closure of SubClassOf and
EquivalentClasses between named classes; unsatisfiable = equivalent to or
under owl:Nothing. An ontology Konclude reports inconsistent (LOG) gives
consistent=false.
"""
import json
import sys
import xml.etree.ElementTree as ET

NS = '{http://www.w3.org/2002/07/owl#}'
NOTHING = 'http://www.w3.org/2002/07/owl#Nothing'
THING = 'http://www.w3.org/2002/07/owl#Thing'
if len(sys.argv) > 2 and 'inconsistent' in open(sys.argv[2], errors='replace').read():
    print(json.dumps({'consistent': False, 'subsumptions': [], 'unsatisfiable': []}))
    sys.exit(0)
root = ET.parse(sys.argv[1]).getroot()
edges = {}
classes = set()
def add(a, b):
    edges.setdefault(a, set()).add(b)
for el in root:
    tag = el.tag.replace(NS, '')
    cs = [c.get('IRI') for c in el if c.tag == NS + 'Class']
    classes.update(cs)
    if tag == 'SubClassOf' and len(cs) == 2:
        add(cs[0], cs[1])
    elif tag == 'EquivalentClasses':
        for a in cs:
            for b in cs:
                add(a, b)
def closure(a):
    seen, todo = {a}, [a]
    while todo:
        x = todo.pop()
        for y in edges.get(x, ()):
            if y not in seen:
                seen.add(y); todo.append(y)
    return seen
unsat = sorted(c for c in classes if c not in (NOTHING,) and NOTHING in closure(c))
subs = []
for a in sorted(classes):
    if a in (NOTHING, THING) or a in unsat:
        continue
    for b in sorted(closure(a)):
        if b != a and b not in (THING, NOTHING) and b not in unsat:
            subs.append([a, b])
print(json.dumps({'consistent': True, 'subsumptions': subs, 'unsatisfiable': unsat}))
