"""Compare ore_time.sh streams: per file rc, seconds, signature equality.
usage: python3 -I ore_cmp.py ORE_DIR TAG_A TAG_B [TAG_C]"""
import sys, gzip, os, statistics
d = sys.argv[1]; tags = sys.argv[2:]
rows = {}
for t in tags:
    for l in open(os.path.join(d, f'times-{t}.tsv')):
        f = l.rstrip('\n').split('\t')
        if len(f) < 4: continue
        rows.setdefault(f[0], {})[t] = (int(f[2]), float(f[3]), f[4] if len(f) > 4 else '')
def sig(t, n):
    p = os.path.join(d, f'out-{t}', n + '.sig.gz')
    return gzip.open(p).read() if os.path.exists(p) else None
done = [n for n in rows if all(t in rows[n] for t in tags)]
print('files with all streams:', len(done))
a = tags[0]
for b in tags[1:]:
    both = [n for n in done if rows[n][a][0] == 0 and rows[n][b][0] == 0]
    diff = [n for n in both if sig(a, n) != sig(b, n)]
    onlya = [n for n in done if rows[n][a][0] == 0 and rows[n][b][0] != 0]
    onlyb = [n for n in done if rows[n][b][0] == 0 and rows[n][a][0] != 0]
    ratios = [rows[n][b][1] / max(rows[n][a][1], 1e-3) for n in both]
    ta = sum(rows[n][a][1] for n in both); tb = sum(rows[n][b][1] for n in both)
    print(f'{a} vs {b}: both answer {len(both)}, signature differs {len(diff)} {diff[:10]}, '
          f'only {a} {onlya}, only {b} {onlyb}, sum {ta:.1f} vs {tb:.1f} s, '
          f'mean ratio {statistics.mean(ratios) if ratios else 0:.3f}, median ratio {statistics.median(ratios) if ratios else 0:.3f}')
    slow = sorted(((rows[n][b][1] - rows[n][a][1], n) for n in both), reverse=True)[:5]
    print('  largest slowdowns (s):', [(n, round(rows[n][a][1], 2), round(rows[n][b][1], 2)) for _, n in slow])
