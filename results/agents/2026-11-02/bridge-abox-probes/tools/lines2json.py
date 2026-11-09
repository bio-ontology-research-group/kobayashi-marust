"""Convert `km classify --lines` output to the km-json taxonomy shape read by
canonicalize.py (consistent, subsumptions, unsatisfiable).
usage: python3 -I lines2json.py IN.lines OUT.json"""
import json, sys
cons, subs, uns = None, [], []
for line in open(sys.argv[1]):
    t = line.rstrip('\n').split('\t')
    if t[0].startswith('CONSISTENT'):
        cons = t[0].split()[-1] == '1'
    elif t[0] == 'SUB' and len(t) == 3:
        subs.append([t[1], t[2]])
    elif t[0] == 'UNSAT' and len(t) == 2:
        uns.append(t[1])
json.dump({'consistent': cons, 'subsumptions': subs, 'unsatisfiable': uns}, open(sys.argv[2], 'w'))
