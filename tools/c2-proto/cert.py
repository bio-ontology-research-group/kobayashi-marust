"""Certificates: realisations with an explicit finite record set
(design section 4.1, `checkCert`), and their construction from a finite
model (the finite case of the model-to-realisation direction, design
section 3.4).

A certificate is `(cty, lab, kids, recs)`:

* `cty`, `lab`: the core as in realise.py;
* `kids[c]`: list of record ids, the tree children of core element c;
* `recs[rid] = (t, par, core, children)` with `par = ('t', L, s)` or
  `('c', c, L)` (L: label from the node to its parent), `core` a dict
  d -> L (label from the node to core element d), `children` a list of
  (L, rid') (L: label from the node to the child).

`check_cert` checks every condition locally; it needs no alive set, so it
runs in time linear in the certificate. Its soundness is the soundness
direction of the characterisation: the records of a certificate form a set
that supports itself relative to the core.
"""

from __future__ import annotations

from kb import KB, flipL


def check_cert(kb: KB, cert, why=None) -> bool:
    def fail(msg):
        if why is not None:
            why.append(msg)
        return False

    cty, lab, kids, recs = cert
    k = len(cty)
    if k == 0:
        return fail("empty core")
    for a in kb.noms:
        if sum(1 for t in cty if a in t) != 1:
            return fail(f"nominal {kb.cname(a)} not in exactly one core element")
    for c in range(k):
        for d in range(k):
            if lab[c][d] != flipL(lab[d][c]):
                return fail("core labels not symmetric")
            if lab[c][d] and not kb.up_closed(lab[c][d]):
                return fail("core label not up-closed")
    # core stars
    for c in range(k):
        N = [(lab[c][d], cty[d]) for d in range(k) if lab[c][d]]
        for rid in kids[c]:
            t, par, core, ch = recs[rid]
            if par[0] != "c" or par[1] != c:
                return fail(f"core child {rid} has the wrong anchor")
            N.append((flipL(par[2]), t))
        if not kb.star_ok(cty[c], N):
            return fail(f"core star {c} fails")
    # records
    for rid, (t, par, core, ch) in recs.items():
        if t & kb.noms:
            return fail(f"record {rid} has a nominal name")
        if par[0] == "t":
            N = [(par[1], par[2])]
            anchor = None
        else:
            N = [(par[2], cty[par[1]])]
            anchor = par[1]
        for d, L in core.items():
            if d == anchor:
                return fail(f"record {rid} has a core entry to its anchor")
            if kb.counted(cty[d], flipL(L), t):
                return fail(f"record {rid}: core entry to {d} is counted there")
            N.append((L, cty[d]))
        for (L, rid2) in ch:
            t2, par2, _, _ = recs[rid2]
            if par2 != ("t", flipL(L), t):
                return fail(f"record {rid}: child {rid2} has the wrong parent entry")
            N.append((L, t2))
        if not kb.star_ok(t, N):
            return fail(f"record {rid}: star fails")
    return True


def model_to_cert(kb: KB, N, cext, rext):
    """A certificate from a finite model (design section 3.4, finite case).

    Witnesses: for every lower clause at x, k witnesses. The core starts
    with the nominal elements (or element 0) and grows by every element
    whose record, in the witness unravelling relative to the core, has a
    counted core entry (the NI step). Labels are witness labels.
    Returns (cert, number of NI promotions)."""
    D = range(N)
    typ = {x: frozenset(a for a in range(kb.n) if x in cext[a]) for x in D}
    full = {(x, y): set() for x in D for y in D}
    for r, pairs in rext.items():
        for (x, y) in pairs:
            full[(x, y)].add(2 * r)
            full[(y, x)].add(2 * r + 1)
    wit = {}
    used = {(x, y): set() for x in D for y in D}  # roles of x's needs met by y
    for x in D:
        w = []
        for (a, k, R, b) in kb.lower:
            if a in typ[x]:
                got = [y for y in D if R in full[(x, y)] and b in typ[y]][:k]
                assert len(got) == k, "not a model"
                for y in got:
                    used[(x, y)].add(R)
                    if y not in w:
                        w.append(y)
        wit[x] = w
    # witness labels (design section 3.4): the roles of the needs the edge
    # serves, in both directions, up-closed; a subset of the model label
    lab = {(x, y): kb.up_close(frozenset(used[(x, y)]) | flipL(frozenset(used[(y, x)])))
           for x in D for y in D}
    K = [x for x in D if typ[x] & kb.noms] or [0]
    promotions = 0
    while True:
        Ks = set(K)
        recs = {}
        bad = None
        stack = []
        for c in K:
            for x in wit[c]:
                if x not in Ks:
                    stack.append((x, ("c", c)))
        while stack and bad is None:
            x, p = stack.pop()
            if (x, p) in recs:
                continue
            py = p[1]
            core = {}
            for d in wit[x]:
                if d in Ks and d != py:
                    # a core entry carries the node's own needs only (design 3.4)
                    Lc = kb.up_close(frozenset(used[(x, d)]))
                    if kb.counted(typ[d], flipL(Lc), typ[x]):
                        bad = x
                        break
                    core[K.index(d)] = Lc
            if bad is not None:
                break
            ch = [(lab[(x, w)], (w, ("t", x))) for w in wit[x] if w not in Ks and w != py]
            if p[0] == "c":
                par = ("c", K.index(py), lab[(x, py)])
            else:
                par = ("t", lab[(x, py)], typ[py])
            recs[(x, p)] = (typ[x], par, core, ch)
            for (_, rid2) in ch:
                stack.append(rid2)
        if bad is None:
            break
        K.append(bad)
        promotions += 1
    cty = [typ[c] for c in K]
    clab = [[lab[(c, d)] for d in K] for c in K]
    kids = [[(x, ("c", c)) for x in wit[c] if x not in set(K)] for c in K]
    return (cty, clab, kids, recs), promotions
