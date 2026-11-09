"""Python mirror of orchestrate/inert_sorts.rs (diagnostic): prints why candidates fail."""
import json, sys, os
D = '__data__'
def is_var(t): return t['kind'] == 'var'
def csort(c):
    if c['head'] or len(c['body']) != 2: return None
    a, b = c['body']
    if a['kind'] == 'concept' and b['kind'] == 'concept' and a['term'] == b['term'] and is_var(a['term']):
        if a['concept'] == D and b['concept'] != D: return b['concept']
        if b['concept'] == D and a['concept'] != D: return a['concept']
    return None
def rsort(c):
    if c['head'] or len(c['body']) != 2: return None
    a, b = c['body']
    r, k = (a, b) if a['kind'] == 'role' else (b, a)
    if r['kind'] != 'role' or k['kind'] != 'concept' or k['concept'] != D: return None
    if r['source'] == r['target'] or not is_var(r['source']) or not is_var(r['target']): return None
    if k['term'] == r['source']: return (r['role'], True)
    if k['term'] == r['target']: return (r['role'], False)
    return None
def internal(n): return n.startswith('Q_') or n.startswith('__') or n.startswith('aux_') or n.startswith('def_')
d = json.load(open(sys.argv[1])); cl = d['clauses']
reserve = set()
if len(sys.argv) < 3 or sys.argv[2] != 'nometa':
    for c in d.get('cardinalities', []): reserve |= {c['marker'], c['filler']}
    for c in d.get('definers', []): reserve.add(c['marker']); reserve |= set(c.get('operands', []))
oc, od, orr, gc, gr = set(), set(), set(), [], []
for c in cl:
    if not c['body'] and len(c['head']) == 1:
        h = c['head'][0]
        if h['kind'] == 'concept' and h['term']['kind'] == 'ind': gc.append((h['concept'], json.dumps(h['term'])))
        if h['kind'] == 'role' and h['source']['kind'] == 'ind' and h['target']['kind'] == 'ind': gr.append((h['role'], json.dumps(h['source']), json.dumps(h['target'])))
    s = csort(c)
    if s: oc.add(s)
    else:
        r = rsort(c)
        if r: (od if r[1] else orr).add(r[0])
isdata = lambda a, t: a['kind'] == 'concept' and a['concept'] == D and a['term'] == t
rel = set()
GEN0 = os.environ.get('GEN') == '1'
for c in cl:
    for a in c['head'] + (c['body'] if GEN0 else []):
        if a['kind'] == 'concept' and a['concept'] != D and a['concept'] in oc and (GEN0 or any(isdata(o, a['term']) for o in c['head'])) and internal(a['concept']) and not a['concept'].startswith('__') and a['concept'] not in reserve:
            rel.add(a['concept'])
print('candidates', len(rel))
def pinned(rel):
    p = set(t for (k, t) in gc if k in oc and k not in rel)
    for (r, s, t) in gr:
        if r in od: p.add(s)
        if r in orr: p.add(t)
    return p
def relon(atoms, t, rel, skip=None):
    return any(a['kind'] == 'concept' and a['term'] == t and a['concept'] in rel and a is not skip for a in atoms)
def guarded(c, t, rel, pin):
    if json.dumps(t) in pin: return True
    for a in c['body']:
        if a['kind'] == 'concept' and a['term'] == t and a['concept'] in oc and a['concept'] not in rel: return True
        if a['kind'] == 'role' and ((a['source'] == t and a['role'] in od) or (a['target'] == t and a['role'] in orr)): return True
    return False
why = {}
MAXIMAL = os.environ.get('MAXIMAL') == '1'
GEN = os.environ.get('GEN') == '1'
while True:
    failed = set(); pin = pinned(rel)
    for c in cl:
        if csort(c): continue
        for a in c['body']:
            if a['kind'] == 'concept' and a['concept'] in rel and not guarded(c, a['term'], rel, pin) and not (GEN and relon(c['head'], a['term'], rel)):
                failed.add(a['concept']); why.setdefault(a['concept'], ('B', c))
        for a in c['head']:
            if a['kind'] == 'concept' and a['concept'] in rel and not any(isdata(o, a['term']) for o in c['head']) and not guarded(c, a['term'], rel, pin) and not (GEN and relon(c['body'], a['term'], rel)):
                failed.add(a['concept']); why.setdefault(a['concept'], ('H', c))
    if not failed: break
    # hard failures: no other candidate concept on the failing term in the body
    hard = set()
    for c in cl:
        if csort(c): continue
        for a in c['body'] + c['head']:
            if a['kind'] == 'concept' and a['concept'] in failed:
                t = a['term']
                others = [b for b in c['body'] if b['kind'] == 'concept' and b['term'] == t and b['concept'] in rel and b['concept'] != a['concept'] and b['concept'] in oc]
                inbody = a in c['body']
                bad = (not guarded(c, t, rel, pin)) and (inbody or not any(isdata(o, t) for o in c['head']))
                if bad and not others: hard.add(a['concept'])
    if GEN:
        hard = set()
        for c in cl:
            if csort(c): continue
            for a in c['body'] + c['head']:
                if a['kind'] == 'concept' and a['concept'] in failed:
                    t = a['term']
                    others = [b for b in c['body'] + c['head'] if b['kind'] == 'concept' and b['term'] == t and b['concept'] in rel and b['concept'] != a['concept']]
                    if not others:
                        inbody = any(a is b for b in c['body'])
                        bad = (not guarded(c, t, rel, pin)) and (inbody or not any(isdata(o, t) for o in c['head']))
                        if bad: hard.add(a['concept'])
    if MAXIMAL and not hard:
        rel.discard(max(failed))
    else:
        rel -= (hard if MAXIMAL else failed)
print('released', len(rel), sorted(rel)[:20])
for k, (kind, c) in list(why.items())[:int(sys.argv[3]) if len(sys.argv) > 3 else 10]:
    print(k, kind, json.dumps(c)[:250])
if len(sys.argv) > 4:
    out = dict(d)
    keep = [c for c in cl if not (csort(c) and csort(c) in rel)]
    nc = []
    remaining = 0
    for c in keep:
        terms = [a['term'] for a in c['head'] if a['kind'] == 'concept' and a['concept'] in rel]
        c2 = dict(c)
        c2['head'] = [a for a in c['head'] if not (a['kind'] == 'concept' and a['concept'] == D and a['term'] in terms)]
        if len(c2['head']) > 1 and any(a['kind'] == 'concept' and a['concept'] == D for a in c2['head']): remaining += 1
        nc.append(c2)
    out['clauses'] = nc
    json.dump(out, open(sys.argv[4], 'w'))
    print('remaining data-disjunct facts', remaining)
