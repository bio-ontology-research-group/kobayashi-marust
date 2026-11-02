"""Syntactic reachability module of an OFN ontology for a set of classes.

usage: python3 -I reach_module.py IN.owl OUT.ofn CLASS_IRI...
Keeps every RBox axiom, every domain/range axiom, and every SubClassOf /
EquivalentClasses / DisjointClasses axiom whose left side (any side for
equivalences and disjointness) mentions a reached class; the classes of a
kept axiom are reached. Declarations of reached names are kept; ABox axioms are dropped (the module is for TBox
satisfiability). Over-approximates the classes a subject depends on.
"""
import re, sys
src, out, *seeds = sys.argv[1:]
IRI = re.compile(r'<[^>]+>|[A-Za-z]+:[A-Za-z0-9_.:-]+')
heads, axioms, decls = [], [], []
for line in open(src):
    s = line.strip()
    if not s or s.startswith('Prefix(') or s.startswith('Ontology(') or s == ')':
        heads.append(line) if s.startswith('Prefix(') or s.startswith('Ontology(') else None
        continue
    if s.startswith('Declaration('):
        decls.append(s); continue
    if s.startswith('ClassAssertion(') or s.startswith('ObjectPropertyAssertion('):
        continue
    axioms.append(s)
def split_args(s):
    inner = s[s.index('(') + 1:-1]; depth = 0; args = []; cur = ''
    for ch in inner:
        if ch == '(': depth += 1
        if ch == ')': depth -= 1
        if ch == ' ' and depth == 0:
            if cur: args.append(cur); cur = ''
            continue
        cur += ch
    if cur: args.append(cur)
    return args
reach = set('<%s>' % c if not c.startswith('<') else c for c in seeds)
keep = [False] * len(axioms)
always = ('SubObjectPropertyOf', 'InverseObjectProperties', 'TransitiveObjectProperty',
          'ReflexiveObjectProperty', 'FunctionalObjectProperty', 'InverseFunctionalObjectProperty',
          'ObjectPropertyDomain', 'ObjectPropertyRange', 'SymmetricObjectProperty',
          'IrreflexiveObjectProperty', 'AsymmetricObjectProperty', 'EquivalentObjectProperties',
          'DisjointObjectProperties')
for i, a in enumerate(axioms):
    if a.startswith(always):
        keep[i] = True
        reach |= set(IRI.findall(a))
changed = True
while changed:
    changed = False
    for i, a in enumerate(axioms):
        if keep[i]:
            continue
        args = split_args(a)
        if a.startswith('SubClassOf('):
            trig = set(IRI.findall(args[0]))
        else:
            trig = set(IRI.findall(a))
        if trig & reach:
            keep[i] = True; changed = True
            reach |= set(IRI.findall(a))
with open(out, 'w') as f:
    f.writelines(heads)
    for d in decls:
        if set(IRI.findall(d)) & reach:
            f.write(d + '\n')
    for a, k in zip(axioms, keep):
        if k:
            f.write(a + '\n')
    f.write(')\n')
print(sum(keep), 'axioms', len(reach), 'names')
