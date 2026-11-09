"""Compare two scope_run.sh TSVs: route, wall, drop, verdict per input."""
import sys
def load(p):
    rows = {}
    for line in open(p):
        f = line.rstrip('\n').split('\t')
        get = lambda k: next((x.split('=', 1)[1] for x in f if x.startswith(k + '=')), '')
        rows[f[0]] = dict(rc=get('rc'), wall=float(get('wall') or 0), dropped=get('dropped') or '0',
                          route=f[5].replace('route=', ''), accepted=f[6], verdict=f[7])
    return rows
a, b = load(sys.argv[1]), load(sys.argv[2])
def state(r):
    if r['rc'] != '0': return 'timeout' if r['rc'] == '124' else 'rc' + r['rc']
    if r['dropped'] not in ('', '0'): return 'dropped'
    if '=F' in r['verdict'] and '=T' not in r['verdict']: return 'WRONG'
    return 'verified' if '=T' in r['verdict'] else 'unverified'
import collections
trans = collections.Counter((state(a[k]), state(b[k])) for k in a if k in b)
print('state transitions (v154 -> rc):')
for (x, y), n in sorted(trans.items()): print(f'  {x:>10} -> {y:<10} {n}')
both = [k for k in a if k in b and state(a[k]) == 'verified' and state(b[k]) == 'verified']
ratios = sorted(b[k]['wall'] / max(a[k]['wall'], 0.01) for k in both)
if ratios:
    print(f'inputs verified by both: {len(both)}; sum wall v154 {sum(a[k]["wall"] for k in both):.1f}s rc {sum(b[k]["wall"] for k in both):.1f}s; '
          f'median ratio {ratios[len(ratios)//2]:.3f}, mean ratio {sum(ratios)/len(ratios):.3f}')
changed = [k for k in both if a[k]['route'] != b[k]['route'] or a[k]['accepted'] != b[k]['accepted']]
print(f'route or accepting mechanism changed on {len(changed)} of them:')
for k in sorted(changed):
    print(f'  {k}: {a[k]["route"]}/{a[k]["accepted"]} {a[k]["wall"]}s -> {b[k]["route"]}/{b[k]["accepted"]} {b[k]["wall"]}s')
slow = sorted(((b[k]['wall'] - a[k]['wall']), k) for k in both)[-10:]
print('largest slowdowns (rc - v154, s):')
for d, k in reversed(slow): print(f'  {k}: {a[k]["wall"]} -> {b[k]["wall"]} ({d:+.1f})')
for k in sorted(a):
    if k in b and state(a[k]) != state(b[k]):
        print(f'  state change {k}: {state(a[k])} {a[k]["wall"]}s ({a[k]["route"]}) -> {state(b[k])} {b[k]["wall"]}s ({b[k]["route"]})')
