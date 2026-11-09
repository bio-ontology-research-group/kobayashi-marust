"""Delta debugging of a satisfiable-expander-cache miss: keep the axioms
whose removal preserves "KM with the cache misses A ⊑ B and KM without it
(KM_HT_NO_SAT_EXP_CACHE=1) derives it".

usage: python3 -I ddmin_cache.py KM_BIN SEED.ofn OUT.ofn ROUTE A B
Release flags, 30 s per KM run, two KM runs per test (sequential). Confirm
the result against HermiT afterwards (gold_batch.sh); this tool uses KM
without the cache as its oracle only to steer the reduction.
"""
import json, os, subprocess, sys, tempfile
KM, SEED, OUT, ROUTE, A, B = sys.argv[1:7]
W = tempfile.mkdtemp(dir=os.path.dirname(os.path.abspath(OUT)))
src = open(SEED).read().splitlines()
head = [l for l in src if l.startswith(('Prefix', 'Ontology', 'Declaration'))]
ax = [l for l in src if l not in head and l.strip() != ')']
loc = lambda x: x.split('#')[-1].lstrip(':')
base = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
base.update(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
            KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1', KM_THREADS='1')
if ROUTE != 'auto':
    base['KM_ROUTE'] = ROUTE
n_call = [0]
def subs(f, extra):
    env = dict(base); env.update(extra)
    try:
        p = subprocess.run([KM, 'classify', f], env=env, capture_output=True, timeout=30)
        k = json.loads(p.stdout)
    except Exception:
        return None
    if not k.get('consistent'):
        return None
    return {(loc(a), loc(b)) for a, b in k.get('subsumptions', [])}, {loc(x) for x in k.get('unsatisfiable', [])}
def bad(sub):
    n_call[0] += 1
    f = os.path.join(W, 'c%d.ofn' % n_call[0])
    open(f, 'w').write('\n'.join(head + sub + [')']) + '\n')
    with_cache = subs(f, {})
    if with_cache is None or (A, B) in with_cache[0] or A in with_cache[1]:
        return False
    without = subs(f, {'KM_HT_NO_SAT_EXP_CACHE': '1'})
    return without is not None and (A, B) in without[0]
assert bad(ax), 'the seed does not show the miss'
n = 2
while len(ax) >= 2:
    chunks = [ax[i::n] for i in range(n)]
    for c in chunks:
        comp = [a for a in ax if a not in c]
        if bad(comp):
            ax = comp; n = max(n - 1, 2); break
    else:
        if n >= len(ax):
            break
        n = min(len(ax), 2 * n)
for a in list(ax):
    r = [b for b in ax if b != a]
    if bad(r):
        ax = r
open(OUT, 'w').write('\n'.join(head + ax + [')']) + '\n')
print('\n'.join(ax))
