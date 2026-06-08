#!/usr/bin/env python3
"""Canonicalise a reasoner's classification output into a comparable form.

All five reasoners are reduced to the SAME canonical signature:

    (consistent: bool,
     subs: frozenset[(sub_localname, sup_localname)],   # full transitive closure
     unsat: frozenset[localname])                        # classes equiv to owl:Nothing

Classes are reduced to their *local name* (fragment after the last '#' or '/'),
matching what the HermiT `Oracle` and the KM driver already emit.  owl:Thing /
owl:Nothing and reflexive pairs are dropped; equivalence is mutual subsumption.

The graph (SubClassOf edges + EquivalentClasses as bidirectional edges) is
condensed by strongly-connected component (an SCC == a maximal set of mutually
equivalent classes) and the resulting DAG is transitively closed with
memoisation.  This makes reasoners that emit only the direct hierarchy from a
chosen equivalence-class representative (ELK, Sequoia, Konclude) comparable with
those emitting the full closure (HermiT, KM), regardless of which representative
each picks.

Output formats handled:
  json        HermiT Oracle / KM owl_classify.py: {consistent, subsumptions, unsatisfiable}
  functional  ELK, Sequoia: SubClassOf(<A> <B>) / EquivalentClasses(<A> <B> ...)
  owlxml      Konclude: <SubClassOf><Class IRI="A"/><Class IRI="B"/></SubClassOf>
"""
import json
import re
import sys

sys.setrecursionlimit(1 << 20)

THING = {"thing", "Thing", "owl:Thing"}
NOTHING = {"nothing", "Nothing", "owl:Nothing"}

# guard: if the transitive closure exceeds this many pairs, stop and mark capped
CLOSURE_PAIR_CAP = 20_000_000


def localname(iri: str) -> str:
    s = iri.strip().lstrip("<").rstrip(">")
    if "#" in s:
        s = s.rsplit("#", 1)[1]
    elif "/" in s:
        s = s.rsplit("/", 1)[1]
    return s


def _is_thing(n: str) -> bool:
    return n.lower() == "thing" or n.endswith("#Thing") or n == "owl:Thing"


def _is_nothing(n: str) -> bool:
    return n.lower() == "nothing" or n.endswith("#Nothing") or n == "owl:Nothing"


# ---- format-specific extraction of raw edges + equivalence groups ----

def _parse_json(text):
    d = json.loads(text)
    consistent = bool(d.get("consistent", True))
    edges = [(localname(a), localname(b)) for a, b in d.get("subsumptions", [])]
    unsat = {localname(x) for x in d.get("unsatisfiable", [])}
    return consistent, edges, [], unsat, set()


_SUBCLASS_FUN = re.compile(r"SubClassOf\(\s*(<[^>]+>|[\w:]+)\s+(<[^>]+>|[\w:]+)\s*\)")
_EQUIV_FUN = re.compile(r"EquivalentClasses\(\s*([^)]+?)\s*\)")
_TOK_FUN = re.compile(r"<[^>]+>|[A-Za-z][\w:.\-]*")
_DECL_FUN = re.compile(r"Declaration\(\s*Class\(\s*(<[^>]+>|[\w:]+)\s*\)\s*\)")


def _parse_functional(text):
    edges = [(localname(m.group(1)), localname(m.group(2))) for m in _SUBCLASS_FUN.finditer(text)]
    groups = []
    for m in _EQUIV_FUN.finditer(text):
        names = [localname(t) for t in _TOK_FUN.findall(m.group(1))]
        if len(names) >= 2:
            groups.append(names)
    declared = {localname(m.group(1)) for m in _DECL_FUN.finditer(text)}
    return True, edges, groups, set(), declared


_SUBCLASS_XML = re.compile(
    r"<SubClassOf>\s*<Class\s+IRI=\"([^\"]+)\"\s*/>\s*<Class\s+IRI=\"([^\"]+)\"\s*/>\s*</SubClassOf>",
    re.S)
_EQUIV_XML = re.compile(r"<EquivalentClasses>(.*?)</EquivalentClasses>", re.S)
_CLASS_IRI = re.compile(r"<Class\s+IRI=\"([^\"]+)\"\s*/>")
_DECL_XML = re.compile(r"<Declaration>\s*<Class\s+IRI=\"([^\"]+)\"\s*/>\s*</Declaration>", re.S)


def _parse_owlxml(text):
    edges = [(localname(m.group(1)), localname(m.group(2))) for m in _SUBCLASS_XML.finditer(text)]
    groups = []
    for m in _EQUIV_XML.finditer(text):
        names = [localname(x) for x in _CLASS_IRI.findall(m.group(1))]
        if len(names) >= 2:
            groups.append(names)
    declared = {localname(m.group(1)) for m in _DECL_XML.finditer(text)}
    return True, edges, groups, set(), declared


PARSERS = {"json": _parse_json, "functional": _parse_functional, "owlxml": _parse_owlxml}


def _sccs(nodes, succ):
    """Iterative Tarjan SCC. Returns (comp_id dict, list of component member lists)."""
    index = {}
    low = {}
    onstack = set()
    stack = []
    comp = {}
    comps = []
    counter = [0]
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(succ.get(root, ())))]
        index[root] = low[root] = counter[0]; counter[0] += 1
        stack.append(root); onstack.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    stack.append(w); onstack.add(w)
                    work.append((w, iter(succ.get(w, ()))))
                    advanced = True
                    break
                elif w in onstack:
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            if low[v] == index[v]:
                members = []
                while True:
                    x = stack.pop(); onstack.discard(x)
                    comp[x] = len(comps); members.append(x)
                    if x == v:
                        break
                comps.append(members)
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
    return comp, comps


def canonicalize(text, fmt):
    """Return (consistent, subs_frozenset, unsat_frozenset, capped_bool)."""
    consistent, edges, groups, unsat, declared = PARSERS[fmt](text)

    succ = {}
    nodes = set()
    TOP = "owl:Thing"

    def norm(n):
        if _is_thing(n):
            return TOP
        if _is_nothing(n):
            return "owl:Nothing"
        return n

    def add(a, b):
        a, b = norm(a), norm(b)
        nodes.add(a); nodes.add(b)
        if a != b:
            succ.setdefault(a, set()).add(b)

    for a, b in edges:
        add(a, b)
    for g in groups:                       # equivalence == bidirectional edges
        g = [norm(x) for x in g]
        nodes.update(g)
        rep = g[0]
        for x in g[1:]:
            add(x, rep); add(rep, x)
    for u in {localname(x) for x in unsat}:
        nodes.add(norm(u))
    for dcl in declared:                   # declared-but-unsubsumed classes (Thing-only)
        nodes.add(norm(dcl))
    # C ⊑ owl:Thing is universally true; adding it makes classes that are
    # *equivalent* to Thing (encoded differently by each reasoner) come out as
    # supers of everything uniformly.
    for n in list(nodes):
        if n != TOP and n != "owl:Nothing":
            add(n, TOP)

    # SCC condensation: each SCC = a maximal mutually-equivalent set
    comp, comps = _sccs(nodes, succ)
    csucc = {}                              # super-component adjacency (DAG)
    for a, sups in succ.items():
        ca = comp[a]
        for b in sups:
            cb = comp[b]
            if ca != cb:
                csucc.setdefault(ca, set()).add(cb)

    # memoised reachable-component closure on the DAG
    reach = {}

    def reach_of(c):
        if c in reach:
            return reach[c]
        acc = set()
        reach[c] = acc                      # DAG: no cycles, safe to pre-seed
        for d in csucc.get(c, ()):
            acc.add(d)
            acc |= reach_of(d)
        return acc

    # any comp that reaches the owl:Nothing SCC is unsatisfiable -> dropped, listed.
    # the owl:Thing token is dropped, but named classes *equivalent* to Thing stay
    # real (they are genuine supers of everything).
    nothing_comps = {comp[n] for n in nodes if _is_nothing(n)}
    unsat_comps = set()
    for ci in range(len(comps)):
        if ci in nothing_comps or (reach_of(ci) & nothing_comps):
            unsat_comps.add(ci)
    for ci in unsat_comps:
        unsat.update(m for m in comps[ci] if not _is_nothing(m))

    real_members = {}
    for ci, members in enumerate(comps):
        if ci in unsat_comps:
            real_members[ci] = []
        else:
            real_members[ci] = [m for m in members
                                if not _is_thing(m) and not _is_nothing(m) and m not in unsat]

    subs = set()
    capped = False
    for ci, members in enumerate(comps):
        reals = real_members[ci]
        if not reals:
            continue
        sup_names = []
        for dc in reach_of(ci):
            sup_names.extend(real_members.get(dc, ()))
        for sub in reals:
            for sup in sup_names:
                subs.add((sub, sup))
            for other in reals:            # equivalents within the SCC are mutual supers
                if other != sub:
                    subs.add((sub, other))
        if len(subs) > CLOSURE_PAIR_CAP:
            capped = True
            break

    return consistent, frozenset(subs), frozenset(unsat), capped


if __name__ == "__main__":
    fmt = sys.argv[1]
    with open(sys.argv[2]) as f:
        text = f.read()
    c, subs, unsat, capped = canonicalize(text, fmt)
    print(json.dumps({"consistent": c, "n_sub": len(subs), "n_unsat": len(unsat),
                      "capped": capped, "sample": sorted(list(subs))[:5]}))
