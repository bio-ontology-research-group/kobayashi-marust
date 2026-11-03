"""Greedy one-axiom-at-a-time reduction of an OFN seed while the answers of
two KM routes keep differing (the reference route matching HermiT on the
input is the caller's responsibility).

usage: python3 -I ddmin_route.py KM IN.ofn OUT.ofn GOOD_ROUTE BAD_ROUTE
Release flags are set; declarations are kept. The property is: both routes
answer and their (consistency, subsumptions, unsatisfiable) differ.
"""
import json, os, subprocess, sys
km, src, out, good, bad = sys.argv[1:6]
lines = open(src).read().splitlines()
head = [l for l in lines if l.startswith(('Prefix(', 'Ontology(', 'Declaration('))]
ax = [l for l in lines if l and not l.startswith(('Prefix(', 'Ontology(', 'Declaration(')) and l != ')']
base = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
base.update(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
            KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1', KM_THREADS='1')
tmp = out + '.tmp.ofn'
def answer(axs, route):
    open(tmp, 'w').write('\n'.join(head + axs + [')']) + '\n')
    env = dict(base, KM_ROUTE=route)
    try:
        o = subprocess.run([km, 'classify', tmp], env=env, capture_output=True, text=True, timeout=30).stdout
        d = json.loads(o)
    except Exception:
        return None
    if not d['consistent']:
        return (False,)
    u = frozenset(d['unsatisfiable'])
    return (True, frozenset(tuple(p) for p in d['subsumptions'] if p[0] not in u and p[1] not in u), u)
def differs(axs):
    a, b = answer(axs, good), answer(axs, bad)
    return a is not None and b is not None and a != b
assert differs(ax), 'routes agree on the input'
i = 0
while i < len(ax):
    trial = ax[:i] + ax[i + 1:]
    if differs(trial):
        ax = trial
    else:
        i += 1
open(out, 'w').write('\n'.join(head + ax + [')']) + '\n')
os.remove(tmp)
print('\n'.join(ax))
