"""Greedy one-axiom-at-a-time minimization of a seed on which KM misses a
subsumption that HermiT entails.
usage: python3 -I minimize.py KM_BIN ORACLE_DIR SEED.ofn SUB SUP OUT.ofn"""
import os, subprocess, sys, json, tempfile
KM, ORACLE, SEED, SUB, SUP, OUT = sys.argv[1:7]
S = os.path.dirname(os.path.abspath(OUT))
env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
env.update(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
           KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1', KM_THREADS='1')
lines = open(SEED).read().splitlines()
head = [l for l in lines if not (l.startswith(('SubClassOf', 'EquivalentClasses', 'ClassAssertion', 'ObjectPropertyAssertion',
         'SameIndividual', 'DifferentIndividuals', 'DisjointClasses', 'TransitiveObjectProperty', 'SubObjectPropertyOf',
         'InverseObjectProperties', 'FunctionalObjectProperty', 'InverseFunctionalObjectProperty')))]
axioms = [l for l in lines if l not in head]
def text(ax):
    body = [l for l in head if l != ')']
    return '\n'.join(body + ax + [')']) + '\n'
def check(ax):
    p = os.path.join(S, 'min-try.ofn')
    open(p, 'w').write(text(ax))
    cp = open(os.path.join(ORACLE, 'cp.txt')).read().strip()
    o = subprocess.run(['timeout', '60', 'java', '-Xmx1g', '-cp', '.:' + cp, 'Oracle', p], cwd=ORACLE,
                       capture_output=True, text=True).stdout
    try:
        d = json.loads(o)
    except ValueError:
        return False
    strip = lambda n: n.lstrip(':').split('#')[-1]
    if not d['consistent'] or [SUB, SUP] not in [[strip(a), strip(b)] for a, b in d['subsumptions']]:
        return False
    k = subprocess.run(['timeout', '60', KM, 'classify', '--lines', p], capture_output=True, text=True, env=env).stdout
    subs = {tuple(strip(x) for x in l.split('\t')[1:3]) for l in k.splitlines() if l.startswith('SUB\t')}
    return 'CONSISTENT 1' in k and (SUB, SUP) not in subs
assert check(axioms), 'seed does not reproduce'
i = 0
while i < len(axioms):
    trial = axioms[:i] + axioms[i + 1:]
    if check(trial):
        axioms = trial
    else:
        i += 1
open(OUT, 'w').write(text(axioms))
print(len(axioms), 'axioms')
