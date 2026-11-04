"""Delta debugging of a seed against HermiT: keep the axioms whose removal
preserves one wrong KM verdict (KM disagrees with HermiT on a named
subsumption or unsatisfiable class).

usage: python3 -I ddmin_hermit.py KM_BIN SEED.ofn OUT.ofn ROUTE KIND A [B]
KIND: miss_sub A B (HermiT has A ⊑ B, KM not), extra_sub A B (KM has it,
HermiT not), miss_unsat A (HermiT unsatisfiable, KM not). ROUTE: a
KM_ROUTE value or `auto`. Release flags, 60 s per KM run, HermiT 1.4 through
the OracleBatch class of .work/agent-scratch/bridge-nn-rule/oracle-build.
"""
import json, os, subprocess, sys, tempfile
KM, SEED, OUT, ROUTE, KIND = sys.argv[1:6]
ARGS = sys.argv[6:]
O = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/oracle'
B = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-rule/oracle-build'
CP = O + ':' + B + ':' + open(O + '/cp.txt').read().strip()
W = tempfile.mkdtemp(dir=os.path.dirname(os.path.abspath(OUT)))
src = open(SEED).read().splitlines()
head = [l for l in src if l.startswith(('Prefix', 'Ontology', 'Declaration'))]
ax = [l for l in src if l not in head and l.strip() != ')']
loc = lambda x: x.split('#')[-1].lstrip(':')
env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
env.update(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
           KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1', KM_THREADS='1')
if ROUTE != 'auto':
    env['KM_ROUTE'] = ROUTE
n_call = [0]
def answers(sub):
    n_call[0] += 1
    f = os.path.join(W, 'c%d.ofn' % n_call[0])
    open(f, 'w').write('\n'.join(head + sub + [')']) + '\n')
    try:
        p = subprocess.run([KM, 'classify', f], env=env, capture_output=True, timeout=60)
        k = json.loads(p.stdout)
    except Exception:
        return None
    subprocess.run(['timeout', '60', 'java', '-cp', CP, 'OracleBatch', W, f], capture_output=True)
    try:
        h = json.load(open(f[:-4] + '.json'))
    except Exception:
        return None
    return h, k
def bad(sub):
    r = answers(sub)
    if r is None:
        return False
    h, k = r
    if not h['consistent'] or not k.get('consistent'):
        return False
    hs = {(loc(a), loc(b)) for a, b in h['subsumptions']}
    ks = {(loc(a), loc(b)) for a, b in k.get('subsumptions', [])}
    hu = {loc(x) for x in h['unsatisfiable']}
    ku = {loc(x) for x in k.get('unsatisfiable', [])}
    if KIND == 'miss_sub':
        return tuple(ARGS) in hs and tuple(ARGS) not in ks and ARGS[0] not in ku
    if KIND == 'extra_sub':
        return tuple(ARGS) in ks and tuple(ARGS) not in hs and ARGS[0] not in hu
    if KIND == 'miss_unsat':
        return ARGS[0] in hu and ARGS[0] not in ku
    raise SystemExit('unknown kind')
assert bad(ax), 'the seed does not show the verdict'
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
