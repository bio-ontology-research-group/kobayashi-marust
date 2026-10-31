# usage: qudt_cmp.py <km taxonomy json> <hermit gold json>; compares by local names
import json, sys
def local(n): return n.split('#')[-1].split('/')[-1].lstrip(':')
km = json.load(open(sys.argv[1])); gold = json.load(open(sys.argv[2]))
ku = {local(c) for c in km.get('unsatisfiable', [])}; gu = {local(c) for c in gold['unsatisfiable']}
def subs(d, uns):
    return {(local(a), local(b)) for a, b in d['subsumptions'] if local(a) != local(b) and local(a) not in uns and local(b) not in uns}
ks, gs = subs(km, ku), subs(gold, gu)
if km.get('subsumptions_are_graph_edges'):
    # graph edges: close transitively
    succ = {}
    for a, b in ks: succ.setdefault(a, set()).add(b)
    closed = set()
    for a in list(succ):
        stack, seen = list(succ[a]), set()
        while stack:
            b = stack.pop()
            if b in seen: continue
            seen.add(b); stack.extend(succ.get(b, ()))
        closed |= {(a, b) for b in seen if b != a}
    ks = closed
gs = {(a, b) for a, b in gs if b not in ('Thing', 'owl:Thing')}
ks = {(a, b) for a, b in ks if b not in ('Thing', 'owl:Thing')}
print(f"consistent km={km['consistent']} gold={gold['consistent']} dropped={km.get('dropped')}")
print(f"unsat km={len(ku)} gold={len(gu)} equal={ku == gu}")
print(f"subs km={len(ks)} gold={len(gs)} missing={len(gs - ks)} extra={len(ks - gs)}")
for p in sorted(gs - ks)[:10]: print('missing', p)
for p in sorted(ks - gs)[:10]: print('extra', p)
