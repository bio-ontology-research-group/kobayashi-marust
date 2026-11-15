"""A Python mirror of `checkRealisationN` with a certificate (`CertOK`),
lean/ContextCalculus/SRIQN/Procedure.lean. Untrusted: it only explains why
the proved checker would reject a hint, so a rejected hint does not send the
checker into its exhaustive search. A record is
`(t, ('a', c, L))` (anchored at core element c, label L from the record to
c) or `(t, ('p', L, tp))` (child of a tree node of type tp, label L to it).
"""


class Hint:
    def __init__(self, k):
        self.k = k
        self.ty = [frozenset() for _ in range(k)]
        self.lab = {}            # (b, c) -> frozenset, kept symmetric
        self.kids = [[] for _ in range(k)]   # per core: list of (L, t)
        self.recs = []           # list of (key, ce: dict d -> L, kids: list of (L, t))

    def add_lab(self, b, c, L):
        L = frozenset(L)
        self.lab[(b, c)] = self.lab.get((b, c), frozenset()) | L
        self.lab[(c, b)] = self.lab.get((c, b), frozenset()) | frozenset(R ^ 1 for R in L)


def flip(L):
    return frozenset(R ^ 1 for R in L)


def closed(ix, t):
    for g, (b, h) in enumerate(ix.gci):
        if all(a in t for a in b) and not any(x in t for x in h):
            return 'gci %d %s|%s' % (g, b, h)
    return None


def closed_fast(ix, t):
    # every gci whose body holds has a head in t: check gcis indexed by a body name in t
    for g in ix.gci_empty:
        if not any(x in t for x in ix.gci[g][1]):
            return 'gci %d (empty body)' % g
    seen = set()
    for a in t:
        for g in ix.gci_by_body[a]:
            if g in seen:
                continue
            seen.add(g)
            b, h = ix.gci[g]
            if all(x in t for x in b) and not any(x in t for x in h):
                return 'gci %d %s|%s' % (g, b, h)
    return None


def star_ok(ix, t, N):
    """`StarOK B t N`; N a list of (L, t')."""
    r = closed_fast(ix, t)
    if r:
        return 'closed: ' + r
    for (L, s) in N:
        for R in L:
            if not ix.up[R] <= L:
                return 'label not up-closed'
        for a in t:
            for (S, c) in ix.all_by.get(a, ()):
                if S in L and c not in s:
                    return 'edge fwd all %d %d %d' % (a, S, c)
        for a in s:
            for (S, c) in ix.all_by.get(a, ()):
                if (S ^ 1) in L and c not in t:
                    return 'edge bwd all %d %d %d' % (a, S, c)

    def cnt(R, b):
        return sum(1 for (L, s) in N if R in L and b in s)
    for a in t:
        for (R, b) in ix.ex_by.get(a, ()):
            if cnt(R, b) < 1:
                return 'ex %d %d %d' % (a, R, b)
        for (k, R, b) in ix.ge_by.get(a, ()):
            if cnt(R, b) < k:
                return 'ge %d %d %d %d' % (a, k, R, b)
        for (k, R, b) in ix.le_by.get(a, ()):
            if cnt(R, b) > k:
                return 'le %d %d %d %d (count %d)' % (a, k, R, b, cnt(R, b))
    return None


def counted(ix, u, L, t):
    for a in u:
        for (k, R, b) in ix.le_by.get(a, ()):
            if R in L and b in t:
                return True
    return False


def check(ix, h):
    """None if the hint passes `checkRealisationN` by the certificate route,
    else the first reason found."""
    if h.k <= 0:
        return 'empty core'
    for a in ix.noms:
        c = [b for b in range(h.k) if a in h.ty[b]]
        if len(c) != 1:
            return 'nominal %d in %d core types' % (a, len(c))

    def nbrs(b):
        return [(h.lab[(b, c)], h.ty[c]) for c in range(h.k) if h.lab.get((b, c))]
    for b in range(h.k):
        r = star_ok(ix, h.ty[b], nbrs(b) + h.kids[b])
        if r:
            return 'core %d: %s' % (b, r)
    if all(not h.kids[b] for b in range(h.k)):
        return None
    keys = set(k for (k, _, _) in h.recs)
    for b in range(h.k):
        for (L, t) in h.kids[b]:
            if (t, ('a', b, flip(L))) not in keys:
                return 'core %d: anchor record of a kid missing' % b
    for i, (key, ce, kids) in enumerate(h.recs):
        t, par = key
        if t & ix.nomset:
            return 'rec %d: nominal name in a tree type' % i
        if par[0] == 'a':
            c, L = par[1], par[2]
            if ce.get(c):
                return 'rec %d: core entry to its anchor' % i
            pe = (L, h.ty[c])
        else:
            pe = (par[1], par[2])
        for d, Ld in ce.items():
            if Ld and counted(ix, h.ty[d], flip(Ld), t):
                return 'rec %d: core entry to %d is counted there' % (i, d)
        N = [pe] + [(Ld, h.ty[d]) for d, Ld in sorted(ce.items()) if Ld] + list(kids)
        r = star_ok(ix, t, N)
        if r:
            return 'rec %d: %s' % (i, r)
        for (L, s) in kids:
            if (s, ('p', flip(L), t)) not in keys:
                return 'rec %d: child record missing' % i
    return None


def write(h, path, comment=None):
    from nf import rts
    out = []
    if comment:
        out.append('# ' + comment)
    out.append('blocks %d' % h.k)
    for b in range(h.k):
        out.append('ty %d %s' % (b, ' '.join(map(str, sorted(h.ty[b])))))
    for (b, c), L in sorted(h.lab.items()):
        if b <= c and L:
            out.append('lab %d %d %s' % (b, c, ' '.join(rts(R) for R in sorted(L))))
    for b in range(h.k):
        for (L, t) in h.kids[b]:
            out.append('kid %d %s / %s' % (b, ' '.join(rts(R) for R in sorted(L)),
                                           ' '.join(map(str, sorted(t)))))
    for i, (key, ce, kids) in enumerate(h.recs):
        t, par = key
        out.append('rec %d %s' % (i, ' '.join(map(str, sorted(t)))))
        if par[0] == 'a':
            out.append('ranc %d %d %s' % (i, par[1], ' '.join(rts(R) for R in sorted(par[2]))))
        else:
            out.append('rpar %d %s / %s' % (i, ' '.join(rts(R) for R in sorted(par[1])),
                                            ' '.join(map(str, sorted(par[2])))))
        for d, Ld in sorted(ce.items()):
            if Ld:
                out.append('rce %d %d %s' % (i, d, ' '.join(rts(R) for R in sorted(Ld))))
        for (L, s) in kids:
            out.append('rkid %d %s / %s' % (i, ' '.join(rts(R) for R in sorted(L)),
                                            ' '.join(map(str, sorted(s)))))
    with open(path, 'w') as f:
        f.write('\n'.join(out) + '\n')
