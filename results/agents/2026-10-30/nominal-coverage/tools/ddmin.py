"""Shrink an OFN seed (axiom lines) while `km classify` (auto) stays slower than T s.
usage: python3 -I ddmin.py KM IN.ofn OUT.ofn T"""
import os, subprocess, sys, signal
KM, IN, OUT, T = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4])
lines = open(IN).read().splitlines()
head = [l for l in lines if l.startswith(('Prefix', 'Ontology', 'Declaration'))]
axioms = [l for l in lines if l and not l.startswith(('Prefix', 'Ontology', 'Declaration')) and l != ')']
env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
def slow(ax):
    with open(OUT + '.try', 'w') as f:
        f.write('\n'.join(head + ax + [')']) + '\n')
    p = subprocess.Popen([KM, 'classify', '--lines', OUT + '.try'], stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL, env=env, start_new_session=True)
    try:
        p.wait(timeout=T); return False
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); p.wait(); return True
assert slow(axioms)
changed = True
while changed:
    changed = False
    for i in range(len(axioms)):
        cand = axioms[:i] + axioms[i+1:]
        if slow(cand):
            axioms = cand; changed = True; break
open(OUT, 'w').write('\n'.join(head + axioms + [')']) + '\n')
print('\n'.join(axioms))
