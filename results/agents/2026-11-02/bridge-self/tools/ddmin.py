"""Greedy delta minimisation of an OFN module for a KM expander-cache miss.

usage: python3 -I ddmin.py KM IN.ofn OUT.ofn CLASS_SUFFIX [ENV=VAL ...]
Keeps an axiom set where CLASS is UNSAT with KM_HT_NO_SAT_EXP_CACHE=1 but not
UNSAT without it (both with the given extra environment). Declarations are
kept throughout.
"""
import os, subprocess, sys
km, src, out, cls, *extra = sys.argv[1:]
lines = open(src).read().splitlines()
head = [l for l in lines if l.startswith(('Prefix(', 'Ontology(', 'Declaration('))]
ax = [l for l in lines if l and not l.startswith(('Prefix(', 'Ontology(', 'Declaration(')) and l != ')']
base = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
base.update(dict(kv.split('=', 1) for kv in extra))
tmp = out + '.tmp.ofn'
def unsat(axs, nocache):
    open(tmp, 'w').write('\n'.join(head + axs + [')']) + '\n')
    env = dict(base)
    if nocache: env['KM_HT_NO_SAT_EXP_CACHE'] = '1'
    try:
        o = subprocess.run([km, 'classify', '--lines', tmp], env=env, capture_output=True, text=True, timeout=60).stdout
    except subprocess.TimeoutExpired:
        return None
    return any(l.startswith('UNSAT') and l.endswith(cls) for l in o.splitlines())
def bad(axs):
    return unsat(axs, True) is True and unsat(axs, False) is False
assert bad(ax), 'property does not hold on the input'
n = 2
while len(ax) >= 2:
    size = max(1, len(ax) // n); removed = False
    for i in range(0, len(ax), size):
        cand = ax[:i] + ax[i + size:]
        if cand and bad(cand):
            ax = cand; n = max(n - 1, 2); removed = True; break
    if not removed:
        if size == 1: break
        n = min(len(ax), n * 2)
open(out, 'w').write('\n'.join(head + ax + [')']) + '\n')
os.remove(tmp)
print(len(ax), 'axioms')
