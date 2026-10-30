"""Shrink an OFN seed while the CB engine (KM_NOMINALS=1, data disjuncts dropped
from multi-literal heads when DROP=1) stays slower than T s.
usage: python3 -I ddmin2.py KM IN.ofn OUT.ofn T DROP"""
import json, os, subprocess, sys, signal
KM, IN, OUT, T, DROP = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4]), sys.argv[5] == '1'
lines = open(IN).read().splitlines()
head = [l for l in lines if l.startswith(('Prefix', 'Ontology', 'Declaration'))]
axioms = [l for l in lines if l and not l.startswith(('Prefix', 'Ontology', 'Declaration')) and l != ')']
env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
env.update({'KM_NOMINALS': '1', 'KM_THREADS': '1'})
def slow(ax):
    with open(OUT + '.try', 'w') as f:
        f.write('\n'.join(head + ax + [')']) + '\n')
    r = subprocess.run([KM, 'ofn', OUT + '.try'], capture_output=True, text=True, env=env)
    if r.returncode != 0: return False
    d = json.loads(r.stdout)
    if DROP:
        for c in d['clauses']:
            if len(c['head']) > 1:
                c['head'] = [a for a in c['head'] if not (a['kind'] == 'concept' and a['concept'] == '__data__')]
    p = subprocess.Popen([KM, 'engine'], stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env, start_new_session=True, text=True)
    try:
        p.communicate(json.dumps(d), timeout=T); return False
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); p.communicate(); return True
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
