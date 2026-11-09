# usage: python3 -I ddmin_reject.py KM CHECKERDIR ROUTE NEEDLE IN.ofn OUT.ofn
import os, subprocess, sys
km, cdir, route, needle, src, dst = sys.argv[1:7]
lines = open(src).read().splitlines()
head = [l for l in lines if l.startswith(('Prefix', 'Ontology', 'Declaration'))]
ax = [l for l in lines if l.strip() and l not in head and l.strip() != ')']
tmp = dst + '.tmp.ofn'
def write(a, p): open(p, 'w').write('\n'.join(head + a + [')']) + '\n')
def bad(a):
    write(a, tmp)
    env = dict(os.environ, KM_LEAN_CHECKERS=cdir)
    p = subprocess.run([km, 'classify', '--route', route, '--lines', tmp], env=env, capture_output=True, text=True, timeout=120)
    return p.returncode == 6 and needle in p.stderr
assert bad(ax)
i = 0
while i < len(ax):
    t = ax[:i] + ax[i+1:]
    if bad(t): ax = t
    else: i += 1
write(ax, dst); os.remove(tmp); print('\n'.join(ax))
