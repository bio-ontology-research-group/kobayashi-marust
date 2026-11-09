"""fired.py FIX_DIR BASE_TSV... : for every pool tsv in FIX_DIR (pools.sh with
GUARD=1), split the rows into those where a section 25 guard fired (marker
fired-POOL/<stem>.<route>.fired) and the rest. Rows that never fired compute
what the base computes. Writes FIX_DIR/needs-base.tsv (pool, seed, route) for
fired rows without a base verdict in the given base tsv files, and prints per
pool: rows, fired rows, and the fix verdicts of each group."""
import glob
import os
import sys

fix_dir = sys.argv[1]
base = {}
for bp in sys.argv[2:]:
    for line in open(bp):
        t = line.rstrip('\n').split('\t')
        if len(t) >= 4:
            base[(t[0], t[1])] = (t[2], t[3])
need = open(os.path.join(fix_dir, 'needs-base.tsv'), 'w')
for fp in sorted(glob.glob(os.path.join(fix_dir, '*.tsv'))):
    if fp.endswith('needs-base.tsv'):
        continue
    pool = os.path.basename(fp)[:-4]
    fired_dir = os.path.join(fix_dir, 'fired-' + pool)
    stats = {}
    for line in open(fp):
        t = line.rstrip('\n').split('\t')
        seed, route, verdict = t[0], t[1], t[2]
        stem = os.path.splitext(os.path.basename(seed))[0]
        fired = os.path.exists(os.path.join(fired_dir, stem + '.' + route + '.fired'))
        key = ('fired' if fired else 'quiet', verdict)
        stats[key] = stats.get(key, 0) + 1
        if fired and (seed, route) not in base:
            need.write('\t'.join([pool, seed, route]) + '\n')
    print(pool, ' '.join('%s/%s=%d' % (g, v, n) for (g, v), n in sorted(stats.items())))
need.close()
