"""Greedy one-axiom-at-a-time reduction of an OFN seed while KM on one
route disagrees with HermiT (HermiT 1.4 through OracleBatch, one JVM per
candidate).

usage: python3 -I ddmin_hermit.py KM IN.ofn OUT.ofn ROUTE WORKDIR
Release flags are set; declarations are kept. The property: KM answers and
its (consistency, satisfiable-part subsumptions, unsatisfiable classes)
differ from HermiT's answer. OUT.json receives HermiT's answer on OUT.ofn.
"""
import json, os, shutil, subprocess, sys
km, src, out, route, work = sys.argv[1:6]
os.makedirs(work, exist_ok=True)
O = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/oracle'
B = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-s974/oracle-build'
CP = O + ':' + B + ':' + open(O + '/cp.txt').read().strip()
lines = open(src).read().splitlines()
head = [l for l in lines if l.startswith(('Prefix(', 'Ontology(', 'Declaration('))]
ax = [l for l in lines if l and not l.startswith(('Prefix(', 'Ontology(', 'Declaration(')) and l != ')']
env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
env.update(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
           KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1', KM_THREADS='1')
if route != 'auto':
    env['KM_ROUTE'] = route
loc = lambda x: x.split('#')[-1].split(':')[-1].strip('<>')
step = [0]


def norm(d):
    if not d['consistent']:
        return (False,)
    u = frozenset(loc(x) for x in d['unsatisfiable'])
    s = frozenset((loc(a), loc(b)) for a, b in d['subsumptions']
                  if loc(a) != loc(b) and loc(b) != 'Thing' and loc(a) != 'Nothing'
                  and loc(a) not in u and loc(b) not in u)
    return (True, s, u)


def differs(axs):
    step[0] += 1
    f = os.path.join(work, 'c%d.ofn' % step[0])
    open(f, 'w').write('\n'.join(head + axs + [')']) + '\n')
    try:
        k = json.loads(subprocess.run([km, 'classify', f], env=env, capture_output=True,
                                      text=True, timeout=30).stdout)
    except Exception:
        return False
    try:
        subprocess.run(['java', '-Xmx1g', '-XX:-CreateCoredumpOnCrash', '-cp', CP, 'OracleBatch',
                        work, f], capture_output=True, timeout=120)
        g = json.load(open(os.path.join(work, 'c%d.json' % step[0])))
    except Exception:
        return False
    return norm(k) != norm(g)


assert differs(ax), 'input does not show the difference'
changed = True
while changed:
    changed = False
    for i in range(len(ax)):
        if i >= len(ax):
            break
        cand = ax[:i] + ax[i + 1:]
        if differs(cand):
            ax = cand
            changed = True
open(out, 'w').write('\n'.join(head + ax + [')']) + '\n')
differs(ax)
shutil.copy(os.path.join(work, 'c%d.json' % step[0]), os.path.splitext(out)[0] + '.json')
print('%d axioms' % len(ax))
