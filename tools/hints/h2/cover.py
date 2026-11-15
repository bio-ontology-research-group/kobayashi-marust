"""cover.py REF KM ONT HINT TABLE: certified non-subsumptions (witness row) plus
km's subsumptions must cover every ordered pair of distinct requested classes;
the same for individuals and classes (non-types plus km's types)."""
import json, subprocess, sys, re
ref, km, ont, hint, table = sys.argv[1:6]
r = subprocess.run([ref, '--procedure', 'sroiq-hint', '--witness', table, '--hint', hint, ont],
                   capture_output=True, text=True)
if r.returncode != 0:
    print('NOT CERTIFIED', r.stderr.strip()); sys.exit(1)
rows = [json.loads(l) for l in r.stdout.split('\n') if l.strip()]
classes = None
pre = re.search(r'Prefix\(:=<([^>]*)>\)', open(ont).read()).group(1)
full = lambda s: pre + s[1:] if s.startswith(':') else s.strip('<>')
k = subprocess.run([km, 'classify', '--lines', '--realize', '--top', ont], capture_output=True, text=True,
                   env={'KM_THREADS': '1'})
sub, typ = set(), set()
for l in k.stdout.split('\n'):
    w = l.split('\t')
    if w[0] == 'SUB': sub.add((full(w[1]), full(w[2])))
    if w[0] == 'TYPE': typ.add((full(w[1]), full(w[2])))
names = set(); non = set(); nont = set(); inds = set()
reqs = set()
for x in rows:
    if 'class' in x and 'error' not in x:
        A = x['class']
        if 'nonsub' in x: non |= {(A, B) for B in x['nonsub']}
        else: non |= {(A, '*except', tuple(x['nonsub_except']))}
    if 'individual' in x:
        inds.add(x['individual'])
        if 'nontype' in x: nont |= {(x['individual'], C) for C in x['nontype']}
        else: nont |= {(x['individual'], '*except', tuple(x['nontype_except']))}
hdr = rows[0]
# expand the complement forms over the requested classes, taken from the km signature and the rows
allc = set()
for x in rows:
    if 'class' in x: allc.add(x['class'])
allc |= {a for p in sub for a in p}
def expand(S):
    out = set()
    for t in S:
        if len(t) == 3: out |= {(t[0], B) for B in allc if B not in t[2]}
        else: out.add(t)
    return out
non, nont = expand(non), expand(nont)
both = non & sub
miss = [(A, B) for A in allc for B in allc if A != B and (A, B) not in non and (A, B) not in sub]
missT = [(a, C) for a in inds for C in allc if (a, C) not in nont and (a, C) not in typ]
print(json.dumps({'classes': len(allc), 'km_sub': len(sub), 'certified_nonsub': len(non),
    'conflicts': len(both) + len(nont & typ), 'uncovered_pairs': miss, 'uncovered_types': missT}))
sys.exit(0 if not miss and not missT and not both else 1)
