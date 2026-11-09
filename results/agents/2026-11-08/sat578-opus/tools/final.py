"""final.py: base vs fix over every pool, using guard markers.

Fix verdicts: pools/fix/POOL.tsv (60 s for the three families, 20 s for the
rest), with the 20 s timeouts replaced by their 60 s reruns (runs/fix-cap60.tsv,
markers runs/fired-cap60). A completed fix run without a marker computed what
the base computes, so its base verdict is its own verdict ("quiet"). A fired
run, or a fix TIMEOUT, takes its base verdict from a base run at 60 s
(runs/base-needs.tsv, runs/base-extra.tsv, pools/base-partial-a). Writes
runs/final-rows.tsv and runs/final-diff.tsv and prints a per-pool table."""
import glob
import os
S = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus'


def stem(p):
    return os.path.splitext(os.path.basename(p))[0]


base = {}
for line in open(S + '/pools/base-partial-a/sat578-fam.tsv.part'):
    t = line.rstrip('\n').split('\t')
    base[('sat578-fam', t[0], t[1])] = (t[2], t[3])
for f in ['runs/base-needs.tsv', 'runs/base-extra.tsv']:
    p = os.path.join(S, f)
    if os.path.exists(p):
        for line in open(p):
            t = line.rstrip('\n').split('\t')
            base[(t[0], t[1], t[2])] = (t[3], t[4])
rerun = {}
p = S + '/runs/fix-cap60.tsv'
if os.path.exists(p):
    for line in open(p):
        t = line.rstrip('\n').split('\t')
        rerun[(t[0], t[1], t[2])] = (t[3], t[4])
rows = open(S + '/runs/final-rows.tsv', 'w')
diff = open(S + '/runs/final-diff.tsv', 'w')
need = open(S + '/runs/needs-base-final.tsv', 'w')
hdr = '# pool\tseed\troute\tfired\tbase\tbase_s\tfix\tfix_s\n'
rows.write(hdr); diff.write(hdr)
for fp in sorted(glob.glob(S + '/pools/fix/*.tsv')):
    pool = os.path.basename(fp)[:-4]
    if pool == 'needs-base':
        continue
    tab = {}
    for line in open(fp):
        t = line.rstrip('\n').split('\t')
        key = (pool, t[0], t[1])
        fv, fs = t[2], t[3]
        fired = os.path.exists('%s/pools/fix/fired-%s/%s.%s.fired' % (S, pool, stem(t[0]), t[1]))
        if key in rerun:
            fv, fs = rerun[key]
            fired = os.path.exists('%s/runs/fired-cap60/%s.%s.fired' % (S, stem(t[0]), t[1]))
        if fired or fv == 'TIMEOUT':
            if key in base:
                bv, bs = base[key]
            else:
                bv, bs = 'NOBASE', ''
                need.write('\t'.join(key) + '\n')
        else:
            bv, bs = fv, 'quiet'
        r = '\t'.join([pool, t[0], t[1], 'fired' if fired else 'quiet', bv, bs, fv, fs]) + '\n'
        rows.write(r)
        if bv != fv or fv == 'WRONG':
            diff.write(r)
        k = (t[1], bv, fv)
        tab[k] = tab.get(k, 0) + 1
    print(pool, ' '.join('%s:%s->%s=%d' % (r_, b_, f_, n) for (r_, b_, f_), n in sorted(tab.items())))
