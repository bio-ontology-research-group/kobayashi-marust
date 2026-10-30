"""Greedy one-axiom removal: keep the file while the forced bridge answers
consistent and misses SUB :Q1 :A (r2730 reproducer)."""
import subprocess, sys
src = open(sys.argv[1]).read().splitlines()
head = [l for l in src if l.startswith(('Prefix', 'Ontology', 'Declaration'))]
ax = [l for l in src if l and not l.startswith(('Prefix', 'Ontology', 'Declaration')) and l != ')']
def bad(axs):
    open('tmp/minb.ofn', 'w').write('\n'.join(head + axs + [')']) + '\n')
    o = subprocess.run(['./km.base', 'classify', '--lines', 'tmp/minb.ofn'], capture_output=True, text=True,
                       env={'KM_ROUTE': 'ht_bridge', 'TMPDIR': 'tmp', 'PATH': '/usr/bin:/bin'}).stdout
    if 'CONSISTENT 1' not in o: return False
    h = subprocess.run(['./km.base', 'classify', '--lines', 'tmp/minb.ofn'], capture_output=True, text=True,
                       env={'KM_ROUTE': 'nominals', 'TMPDIR': 'tmp', 'PATH': '/usr/bin:/bin'}).stdout
    return 'SUB\t:Q1\t:A' in h and 'SUB\t:Q1\t:A' not in o
assert bad(ax)
i = 0
while i < len(ax):
    t = ax[:i] + ax[i+1:]
    if bad(t): ax = t
    else: i += 1
print('\n'.join(ax))
