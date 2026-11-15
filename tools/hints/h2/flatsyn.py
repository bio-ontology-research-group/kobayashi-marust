"""Flat model for a Horn normal form without at-most clauses (synthetic test only)."""
import sys
from collections import defaultdict
idx, cls, out = sys.argv[1:4]
n = 0; noms = []
for l in open(idx):
    w = l.split()
    if w[0] == 'concepts': n = int(w[1])
gby = defaultdict(list); top = []; exs = defaultdict(list); alls = defaultdict(list)
for l in open(cls):
    w = l.split()
    if not w: continue
    if w[0] == 'gci':
        k = w.index('->'); b = list(map(int, w[1:k])); h = list(map(int, w[k+1:]))
        if len(h) > 1: raise SystemExit('disjunction')
        if not b: top += h
        else: gby[b[0]].append((b, h))
    elif w[0] == 'some': exs[int(w[1])].append((w[2], int(w[3])))
    elif w[0] == 'all': alls[int(w[1])].append((w[2], int(w[3])))
    elif w[0] == 'nom': noms.append(int(w[1]))
    elif w[0] in ('atleast', 'atmost', 'chain'): raise SystemExit('unsupported ' + w[0])
def close(t):
    st = list(t)
    while st:
        a = st.pop()
        for b, h in gby[a]:
            if all(x in t for x in b):
                if not h: raise SystemExit('clash')
                if h[0] not in t: t.add(h[0]); st.append(h[0])
    return t
flip = lambda R: ('-' if R[0] == '+' else '+') + R[1:]
els = []; lab = defaultdict(set); nomel = {}
for a in noms:
    nomel[a] = len(els); els.append(close(set(top) | {a}))
anon = {}
changed = True
while changed:
    changed = False
    for e in range(len(els)):
        t = els[e]
        for a in list(t):
            for R, b in exs[a]:
                if b in nomel: f = nomel[b]
                else:
                    if b not in anon:
                        anon[b] = len(els); els.append(close(set(top) | {b})); changed = True
                    f = anon[b]
                if R not in lab[(e, f)]:
                    lab[(e, f)].add(R); lab[(f, e)].add(flip(R)); changed = True
    for (e, f), L in list(lab.items()):
        for a in list(els[e]):
            for S, c in alls[a]:
                if S in L and c not in els[f]:
                    els[f].add(c); close(els[f]); changed = True
with open(out, 'w') as o:
    o.write('blocks %d\n' % len(els))
    for i, t in enumerate(els): o.write('ty %d %s\n' % (i, ' '.join(map(str, sorted(t)))))
    for (e, f), L in lab.items():
        L2 = [R for R in L if R[0] == '+'] if e != f else sorted(L)
        if e < f or e == f: o.write('lab %d %d %s\n' % (e, f, ' '.join(sorted(L))))
print(len(els), 'elements', sum(len(t) for t in els), 'type entries', len(lab) // 2, 'edges', file=sys.stderr)
