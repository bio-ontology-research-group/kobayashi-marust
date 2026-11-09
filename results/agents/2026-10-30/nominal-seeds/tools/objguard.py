"""Object-guard rewrite of a gen_nomdata seed (yield experiment).

usage: python3 -I objguard.py IN.ofn OUT.ofn

Every class axiom whose left side may hold on an element without labels gets
the guard :OBJ; every class, object-role endpoint, data-role subject and
individual is put into :OBJ.  Restricting a model of the output to :OBJ gives
a model of the input (OBJ is closed under roles, contains every individual and
named-class member), and OBJ := Thing turns a model of the input into one of
the output, so named-class subsumptions, unsatisfiability and consistency are
the same.
"""
import re, sys

def tok(s):
    return re.findall(r'"(?:[^"\\]|\\.)*"(?:\^\^[\w:]+|@\w+)?|<[^>]*>|[()]|[^\s()]+', s)

def parse(ts, i=0):
    head = ts[i]
    if i + 1 < len(ts) and ts[i + 1] == '(':
        args, j = [], i + 2
        while ts[j] != ')':
            a, j = parse(ts, j)
            args.append(a)
        return (head, args), j + 1
    return head, i + 1

def show(t):
    if isinstance(t, str):
        return t
    return t[0] + '(' + ' '.join(show(a) for a in t[1]) + ')'

def guard(c):
    if c == 'owl:Thing':
        return ':OBJ'
    return ('ObjectIntersectionOf', [':OBJ', c])

def named(c):
    return isinstance(c, str) and c != 'owl:Thing'

src = open(sys.argv[1]).read()
lines = src.splitlines()
out, classes, oprops, dprops, inds = [], set(), set(), set(), set()
for ln in lines:
    s = ln.strip()
    for d in re.findall(r'Declaration\((\w+)\((:\w+)\)\)', s):
        {'Class': classes, 'ObjectProperty': oprops, 'DataProperty': dprops,
         'NamedIndividual': inds}[d[0]].add(d[1])
    if not s or s.startswith(('Prefix', 'Ontology', 'Declaration')) or s == ')':
        out.append(ln)
        continue
    (k, args), _ = parse(tok(s))
    if k == 'SubClassOf':
        l, r = args
        out.append(show(('SubClassOf', [l if named(l) else guard(l), r])))
    elif k == 'EquivalentClasses':
        for x in args:
            for y in args:
                if x is not y:
                    out.append(show(('SubClassOf', [x if named(x) else guard(x), y])))
    elif k == 'DisjointClasses':
        for i, x in enumerate(args):
            for y in args[i + 1:]:
                out.append(show(('SubClassOf', [('ObjectIntersectionOf', [':OBJ', x, y]), 'owl:Nothing'])))
    else:
        out.append(s)
end = out.pop()
assert end.strip() == ')'
out.append('Declaration(Class(:OBJ))')
for c in sorted(classes):
    out.append(f'SubClassOf({c} :OBJ)')
for p in sorted(oprops):
    out.append(f'ObjectPropertyDomain({p} :OBJ)')
    out.append(f'ObjectPropertyRange({p} :OBJ)')
for p in sorted(dprops):
    out.append(f'DataPropertyDomain({p} :OBJ)')
for i in sorted(inds):
    out.append(f'ClassAssertion(:OBJ {i})')
out.append(')')
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')
