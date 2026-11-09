"""final2.py: verdicts of the narrowed fix (5c0cfa67) against the base.
Runs that never fired on b1fcbb93 cannot fire on 5c0cfa67 (its guards refuse
a subset of what b1fcbb93's refuse), so they compute what the base computes.
The 7,032 fired runs were rerun on 5c0cfa67 (runs2/fired.tsv, markers in
runs2/fired). Writes runs2/diff.tsv and prints per-pool counts."""
S = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus'
import os
new = {}
for line in open(S + '/runs2/fired.tsv'):
    t = line.rstrip('\n').split('\t')
    new[(t[0], t[1], t[2])] = (t[3], t[4])
tab = {}
out = open(S + '/runs2/diff.tsv', 'w')
out.write('# pool\tseed\troute\tbase\tbase_s\tnew\tnew_s\tfired_on_new\n')
nfired = 0
for line in open(S + '/runs/final-rows.tsv'):
    if line.startswith('#'):
        continue
    t = line.rstrip('\n').split('\t')
    pool, seed, route, fired, bv, bs, fv, fs = t
    key = (pool, seed, route)
    if fired == 'fired':
        nv, ns = new[key]
        stem = os.path.splitext(os.path.basename(seed))[0]
        f2 = os.path.exists('%s/runs2/fired/%s.%s.fired' % (S, stem, route))
        nfired += f2
    else:
        nv, ns, f2 = fv, fs, False
    k = (pool, route, bv, nv)
    tab[k] = tab.get(k, 0) + 1
    if bv != nv or nv == 'WRONG':
        out.write('\t'.join([pool, seed, route, bv, bs, nv, ns, str(f2)]) + '\n')
for k in sorted(tab):
    print('\t'.join(k), tab[k])
print('fired on new:', nfired)
