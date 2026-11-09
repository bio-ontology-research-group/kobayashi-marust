"""Compare two ore_one.sh streams. usage: ore_cmp.py DIR TAG_A TAG_B [OUT.tsv]"""
import gzip, os, sys
d, a, b = sys.argv[1:4]
out = open(sys.argv[4], 'w') if len(sys.argv) > 4 else None
def load(tag):
    rows = {}
    for l in open(os.path.join(d, f'times-{tag}.tsv')):
        t = l.rstrip('\n').split('\t')
        rows[t[0]] = (int(t[2]), float(t[3]), t[4], int(t[5]) if len(t) > 5 and t[5] else 0)
    return rows
def sig(tag, n):
    p = os.path.join(d, f'out-{tag}', n + '.sig.gz')
    return gzip.open(p, 'rt').read() if os.path.exists(p) else None
A, B = load(a), load(b)
both = sorted(set(A) & set(B))
stat = {'same': 0, 'diff': 0, 'a_only': 0, 'b_only': 0, 'neither': 0}
ta = tb = 0.0; rel = 0; slower = []
for n in both:
    (ra, sa, routea, _), (rb, sb, routeb, relb) = A[n], B[n]
    rel += relb > 0
    if ra == 0 and rb == 0:
        same = sig(a, n) == sig(b, n)
        stat['same' if same else 'diff'] += 1
        ta += sa; tb += sb
        if sb > 1.5 * sa and sb - sa > 5: slower.append((n, sa, sb))
        verdict = 'same' if same else 'DIFF'
    elif ra == 0: stat['a_only'] += 1; verdict = 'LOST'
    elif rb == 0: stat['b_only'] += 1; verdict = 'GAINED'
    else: stat['neither'] += 1; verdict = 'neither'
    if out: out.write(f'{n}\t{ra}\t{sa:.2f}\t{rb}\t{sb:.2f}\t{routeb}\t{relb}\t{verdict}\n')
print(len(both), stat, f'sum both-answered {a}={ta:.1f}s {b}={tb:.1f}s', 'release-fired', rel)
print('slower (>1.5x and >5s):', slower)
