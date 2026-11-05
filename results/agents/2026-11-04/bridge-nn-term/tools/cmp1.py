def loc(x):
    return x.split('#')[-1].split(':')[-1].strip('<>')


def compare(g, k):
    if g['consistent'] != k.get('consistent'):
        return 'WRONG', 'consistency gold=%s km=%s' % (g['consistent'], k.get('consistent'))
    gs = {(loc(a), loc(b)) for a, b in g['subsumptions']}
    ks = {(loc(a), loc(b)) for a, b in k.get('subsumptions', [])}
    ks = {p for p in ks if p[0] != p[1] and p[1] != 'Thing' and p[0] != 'Nothing'}
    gu = {loc(x) for x in g['unsatisfiable']}
    ku = {loc(x) for x in k.get('unsatisfiable', [])}
    # HermiT lists no subsumption of or into an unsatisfiable class; KM
    # lists the ones it derived. Compare the satisfiable part only.
    gs = {p for p in gs if p[0] not in gu and p[1] not in gu}
    ks = {p for p in ks if p[0] not in ku and p[1] not in ku}
    if not g['consistent']:
        return 'ok', ''
    if (gs, gu) == (ks, ku):
        return 'ok', ''
    return 'WRONG', 'missing=%s extra=%s unsat_missing=%s unsat_extra=%s dropped=%s' % (
        sorted(gs - ks)[:4], sorted(ks - gs)[:4], sorted(gu - ku), sorted(ku - gu), k.get('dropped'))


import json, sys
g = json.load(open(sys.argv[1])); k = json.load(open(sys.argv[2]))
v, d = compare(g, k)
print(v, d[:200])
