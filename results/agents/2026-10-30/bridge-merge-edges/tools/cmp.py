# cmp.py OLD.tsv NEW.tsv: verdict counts per route, and per-file changes
import sys, collections, os
def load(p):
    d = {}
    for l in open(p):
        t = l.rstrip('\n').split('\t')
        if len(t) >= 3:
            d[(os.path.basename(t[0]), t[1])] = (t[2], float(t[3]) if len(t) > 3 and t[3] else 0.0)
    return d
a, b = load(sys.argv[1]), load(sys.argv[2])
for name, d in (('old', a), ('new', b)):
    c = collections.defaultdict(collections.Counter)
    for (f, r), (v, _) in d.items():
        c[r][v] += 1
    print(name, {r: dict(x) for r, x in sorted(c.items())})
ch = collections.Counter()
for k in sorted(set(a) | set(b)):
    va = a.get(k, ('-',))[0]; vb = b.get(k, ('-',))[0]
    if va != vb:
        ch[(k[1], va, vb)] += 1
        if vb != 'ok':
            print('  change', k, va, '->', vb)
for k, n in sorted(ch.items()):
    print('  ', k, n)
