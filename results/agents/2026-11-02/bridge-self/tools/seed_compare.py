"""seed_compare.py BASE_DIR FINAL_DIR: per pool, verdict counts and the
(file, route) rows whose verdict changed between two seed runs; WRONG rows
of either run are listed. Rows present in only one run are ignored."""
import collections, glob, os, sys
a, b = sys.argv[1:3]
def load(p):
    d = {}
    for line in open(p):
        f = line.rstrip('\n').split('\t')
        if len(f) >= 3:
            d[(os.path.basename(f[0]), f[1])] = f[2]
    return d
for fb in sorted(glob.glob(os.path.join(b, '*.tsv'))):
    name = os.path.basename(fb)
    fa = os.path.join(a, name)
    if not os.path.exists(fa):
        fa = fa.replace('.tsv', '.first2000.tsv')
    if not os.path.exists(fa):
        continue
    A, B = load(fa), load(fb)
    keys = sorted(set(A) & set(B))
    trans = collections.Counter((A[k], B[k]) for k in keys if A[k] != B[k])
    ca = collections.Counter(A[k] for k in keys); cb = collections.Counter(B[k] for k in keys)
    print(f'{name}: runs={len(keys)} before={dict(ca)} after={dict(cb)} transitions={dict(trans)}')
    for k in keys:
        if 'WRONG' in (A[k], B[k]) and A[k] != B[k]:
            print('   ', k, A[k], '->', B[k])
    wa = sum(1 for k in keys if B[k] == 'WRONG')
    if wa:
        print('    WRONG after:', [k for k in keys if B[k] == 'WRONG'][:20])
