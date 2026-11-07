"""Screen seeds for the entailed-functionality pass (cb_to_ht).

The pass adds a clause only when the HT view holds an equality-headed clause
with exactly two atoms of one role and the variable shape of an at-most-1
(shared source or shared target) that is not already the plain clause
R(x,y1) ∧ R(x,y2) → y1≈y2. The converter keeps the frontend's equality
clauses, so a seed whose frontend clause files (default and KM_NOMINALS=1)
have no such clause has the same HT view on both binaries.

usage: python3 -I screen_atmost.py KM_BIN LIST_IN LIST_OUT
LIST_IN rows: name<TAB>file. LIST_OUT: the rows that may change.
"""
import json, os, subprocess, sys, tempfile
KM, LIN, LOUT = sys.argv[1:4]
def candidate(clauses):
    for c in clauses:
        h = c['head']
        if len(h) != 1 or h[0]['kind'] != 'eq':
            continue
        roles = [a for a in c['body'] if a['kind'] == 'role']
        if len(roles) != 2 or roles[0]['role'] != roles[1]['role']:
            continue
        if len(c['body']) == 2 and roles[0]['source'] == roles[1]['source']:
            continue  # already the plain functional clause
        return True
    return False
rows = [l.rstrip('\n').split('\t') for l in open(LIN) if l.strip()]
keep = []
base = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
for name, f in rows:
    hit = False
    for extra in ({}, {'KM_NOMINALS': '1'}):
        env = dict(base, KM_FAST_IRI_GRAMMAR='1', KM_THREADS='1', **extra)
        try:
            p = subprocess.run([KM, 'ofn', f], env=env, capture_output=True, timeout=60)
            d = json.loads(p.stdout)
        except Exception:
            hit = True  # unknown: rerun it
            break
        if candidate(d.get('clauses', [])):
            hit = True
            break
    if hit:
        keep.append((name, f))
with open(LOUT, 'w') as out:
    for name, f in keep:
        out.write('%s\t%s\n' % (name, f))
print('screened %d, may change %d' % (len(rows), len(keep)))
