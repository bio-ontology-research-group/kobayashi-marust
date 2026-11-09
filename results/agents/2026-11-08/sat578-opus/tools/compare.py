"""compare.py BASE_DIR FIX_DIR OUT.tsv: per pool and route, the verdicts of
pools.sh runs. Prints counts and writes every row whose verdict differs, and
every WRONG of the fix, as: pool, seed, route, base verdict, base s, fix
verdict, fix s."""
import glob
import os
import sys

base_dir, fix_dir, out = sys.argv[1:4]


def load(path):
    rows = {}
    if not os.path.exists(path):
        return rows
    for line in open(path):
        t = line.rstrip('\n').split('\t')
        if len(t) >= 4:
            rows[(t[0], t[1])] = (t[2], t[3])
    return rows


with open(out, 'w') as o:
    o.write('# pool\tseed\troute\tbase\tbase_s\tfix\tfix_s\n')
    for fp in sorted(glob.glob(os.path.join(fix_dir, '*.tsv'))):
        pool = os.path.basename(fp)[:-4]
        b = load(os.path.join(base_dir, pool + '.tsv'))
        f = load(fp)
        counts = {}
        for k, (fv, fs) in sorted(f.items()):
            bv, bs = b.get(k, ('MISSING', ''))
            key = (k[1], bv, fv)
            counts[key] = counts.get(key, 0) + 1
            if bv != fv or fv == 'WRONG':
                o.write('\t'.join([pool, k[0], k[1], bv, bs, fv, fs]) + '\n')
        print(pool, ' '.join('%s:%s->%s=%d' % (r, bv, fv, n) for (r, bv, fv), n in sorted(counts.items())))
