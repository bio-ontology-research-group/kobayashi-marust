"""Realisations with a core (stage C2 prototype, design sections 2 to 4).

A core is a list of core types `cty` (one per core element) and a symmetric
label matrix `lab` (`lab[c][d]` = label from c to d, `flipL` of
`lab[d][c]`; the empty label means no edge).

Records relative to a core (design section 2.3):

* tree record   `(t, ('t', L, s))`: a tree node of type t whose parent is a
  tree node of type s, L the label from the node to its parent;
* anchor record `(t, ('c', c, L))`: a child of core element c, L the label
  from the node to c.

A record is supported in a set G when there are core entries E (at most one
per core element other than the anchor, each uncounted at the core end) and
children C (child records in G) such that StarOK holds for the parent or
anchor entry, E and C. `alive(kb, cty)` is the greatest self-supporting set
(elimination from all valid records). Goodness relative to a core depends on
the core types only.
"""

from __future__ import annotations

from functools import lru_cache
from itertools import product

from kb import KB, flipL


# ---------------------------------------------------------------------------
# Support search: is there a choice of core entries and children with StarOK?
# ---------------------------------------------------------------------------

_contrib_cache: dict = {}


def _contrib(kb: KB, t, L, s):
    cache = kb.cache
    key = ("contrib", t, L, s)
    v = cache.get(key)
    if v is None:
        lows = [(k, R, b) for (a, k, R, b) in kb.lower if a in t]
        ups = [(k, R, b) for (a, k, R, b) in kb.upper if a in t]
        v = (tuple(1 if (R in L and b in s) else 0 for (k, R, b) in lows),
             tuple(1 if (R in L and b in s) else 0 for (k, R, b) in ups))
        cache[key] = v
    return v


def _support(kb: KB, t, fixed, core_opts, child_opts):
    """`fixed`: list of entries (L, s) that are present. `core_opts`: dict
    d -> list of (L, s) (choose at most one per d). `child_opts`: list of
    (L, s), each usable any number of times. Returns a witness
    (core choice dict, children list) or None.

    Only entries that count for some at-least or existential clause firing
    at t are tried (pruning lemma `support_bound`: dropping the other entries
    keeps StarOK)."""
    lows = [(k, R, b) for (a, k, R, b) in kb.lower if a in t]
    ups = [(k, R, b) for (a, k, R, b) in kb.upper if a in t]
    if not kb.closed(t):
        return None
    for (L, s) in fixed:
        if not kb.up_closed(L) or not kb.edge_ok(t, L, s):
            return None

    def contrib(L, s):
        return _contrib(kb, t, L, s)

    lo0 = [0] * len(lows)
    up0 = [0] * len(ups)
    for (L, s) in fixed:
        cl, cu = contrib(L, s)
        lo0 = [x + y for x, y in zip(lo0, cl)]
        up0 = [x + y for x, y in zip(up0, cu)]
    if any(up0[j] > ups[j][0] for j in range(len(ups))):
        return None
    need = [k for (k, R, b) in lows]

    copts = []  # (d, L, s, cl, cu)
    for d, opts in core_opts.items():
        for (L, s) in opts:
            cl, cu = contrib(L, s)
            if any(cl):
                copts.append((d, L, s, cl, cu))
    kopts = []
    for (L, s) in child_opts:
        cl, cu = contrib(L, s)
        if any(cl):
            kopts.append((L, s, cl, cu))

    seen = set()

    def dfs(lo, up, used, chosen_core, kids):
        lo_c = tuple(min(x, n) for x, n in zip(lo, need))
        key = (lo_c, tuple(up), used)
        if key in seen:
            return None
        seen.add(key)
        i = next((i for i in range(len(lows)) if lo[i] < need[i]), None)
        if i is None:
            return (dict(chosen_core), list(kids))
        for (d, L, s, cl, cu) in copts:
            if d in used or not cl[i]:
                continue
            nup = [x + y for x, y in zip(up, cu)]
            if any(nup[j] > ups[j][0] for j in range(len(ups))):
                continue
            chosen_core[d] = L
            r = dfs([x + y for x, y in zip(lo, cl)], nup, used | frozenset([d]), chosen_core, kids)
            del chosen_core[d]
            if r is not None:
                return r
        for (L, s, cl, cu) in kopts:
            if not cl[i]:
                continue
            nup = [x + y for x, y in zip(up, cu)]
            if any(nup[j] > ups[j][0] for j in range(len(ups))):
                continue
            kids.append((L, s))
            r = dfs([x + y for x, y in zip(lo, cl)], nup, used, chosen_core, kids)
            kids.pop()
            if r is not None:
                return r
        return None

    return dfs(lo0, up0, frozenset(), {}, [])


# ---------------------------------------------------------------------------
# Alive records relative to core types
# ---------------------------------------------------------------------------

def all_records(kb: KB, cty):
    recs = []
    TT = kb.tree_types
    for t in TT:
        for s in TT:
            for L in kb.labels:
                if kb.edge_ok(t, L, s):
                    recs.append((t, ("t", L, s)))
        for c, ct in enumerate(cty):
            for L in kb.labels:
                if kb.edge_ok(t, L, ct):
                    recs.append((t, ("c", c, L)))
    return recs


def core_options(kb: KB, cty, t, anchor):
    key = ("copts", tuple(cty), t, anchor)
    hit = kb.cache.get(key)
    if hit is not None:
        return hit
    out = _core_options(kb, cty, t, anchor)
    kb.cache[key] = out
    return out


def _core_options(kb: KB, cty, t, anchor):
    out = {}
    for d, dt in enumerate(cty):
        if d == anchor:
            continue
        opts = [(L, dt) for L in kb.labels
                if kb.edge_ok(t, L, dt) and not kb.counted(dt, flipL(L), t)]
        if opts:
            out[d] = opts
    return out


def child_options(kb: KB, G, t):
    return [(flipL(par[1]), s) for (s, par) in G if par[0] == "t" and par[2] == t]


def record_support(kb: KB, cty, G, rec, kids_by_parent=None):
    t, par = rec
    if par[0] == "t":
        fixed = [(par[1], par[2])]
        anchor = None
    else:
        fixed = [(par[2], cty[par[1]])]
        anchor = par[1]
    kids = kids_by_parent.get(t, []) if kids_by_parent is not None else child_options(kb, G, t)
    return _support(kb, t, fixed, core_options(kb, cty, t, anchor), kids)


_alive_cache: dict = {}


def alive(kb: KB, cty) -> frozenset:
    """Greatest self-supporting set relative to the core types `cty`
    (elimination with a worklist: removing a tree record with parent type
    t can only affect records whose centre type is t)."""
    key = ("alive", tuple(cty))
    if key in kb.cache:
        return kb.cache[key]
    G = set(all_records(kb, cty))
    by_centre: dict = {}
    for r in G:
        by_centre.setdefault(r[0], []).append(r)
    kids_by_parent: dict = {}
    for (s, par) in G:
        if par[0] == "t":
            kids_by_parent.setdefault(par[2], set()).add((flipL(par[1]), s))
    work = set(G)
    while work:
        rec = work.pop()
        if rec not in G:
            continue
        t = rec[0]
        if record_support(kb, cty, G, rec, {t: list(kids_by_parent.get(t, ()))}) is None:
            G.discard(rec)
            s, par = rec
            if par[0] == "t":
                kids_by_parent[par[2]].discard((flipL(par[1]), s))
                work.update(r for r in by_centre.get(par[2], ()) if r in G)
    res = frozenset(G)
    kb.cache[key] = res
    return res


# ---------------------------------------------------------------------------
# Core stars
# ---------------------------------------------------------------------------

def core_nbrs(cty, lab, c):
    return [(lab[c][d], cty[d]) for d in range(len(cty)) if lab[c][d]]


def anchor_options(kb: KB, G, c):
    return [(flipL(par[2]), t) for (t, par) in G if par[0] == "c" and par[1] == c]


def core_support(kb: KB, cty, lab, G, c):
    return _support(kb, cty[c], core_nbrs(cty, lab, c), {}, anchor_options(kb, G, c))


def nominal_ok(kb: KB, cty) -> bool:
    return all(sum(1 for t in cty if a in t) == 1 for a in kb.noms)


# ---------------------------------------------------------------------------
# The hinted checker (design section 4.1)
# ---------------------------------------------------------------------------

def check_realisation(kb: KB, hint) -> bool:
    """`hint = (cty, lab, kids)`; kids[c] is a list of (L, s): label from c
    to the child and the child's type. Sound for every hint: true means
    the knowledge base has a model (theorem `checkRealisationN_sound`)."""
    cty, lab, kids = hint
    k = len(cty)
    if k == 0:
        return False
    if not nominal_ok(kb, cty):
        return False
    for c in range(k):
        for d in range(k):
            if lab[c][d] != flipL(lab[d][c]):
                return False
            if lab[c][d] and not kb.up_closed(lab[c][d]):
                return False
    G = alive(kb, cty)
    for c in range(k):
        if not kb.star_ok(cty[c], core_nbrs(cty, lab, c) + list(kids[c])):
            return False
        for (L, s) in kids[c]:
            if (s, ("c", c, flipL(L))) not in G:
                return False
    return True


# ---------------------------------------------------------------------------
# Exhaustive search over cores of at most kmax elements (design section 4.2)
# ---------------------------------------------------------------------------

def _label_choices(kb: KB, tc, td, diag):
    out = [frozenset()]
    for L in kb.labels:
        if diag and L != flipL(L):
            continue
        if kb.edge_ok(tc, L, td):
            out.append(L)
    return out


def search(kb: KB, kmax: int, core_types_filter=None, stats=None, extra_max=None):
    """Return a hint (cty, lab, kids) for the first realisation found with
    at most kmax core elements, or None.

    Enumeration: a partition of the nominal names into blocks (one core
    element per block, whose type contains exactly the block's nominal
    names), then j extra core elements with types free of nominal names,
    taken in nondecreasing order (permuting core elements is an
    isomorphism). Every core of at most kmax elements that satisfies the
    nominal condition arises this way up to isomorphism.
    `core_types_filter` restricts the types; `extra_max` the number of
    extra elements (C2a: 0)."""
    noms = sorted(kb.noms)
    types = [t for t in kb.types if core_types_filter is None or core_types_filter(t)]
    free = [t for t in types if not (t & kb.noms)]
    for j in range(0, kmax + 1):
        if extra_max is not None and j > extra_max:
            break
        for blocks in _partitions(noms):
            if len(blocks) + j > kmax or len(blocks) + j == 0:
                continue
            per_block = [[t for t in types if (t & kb.noms) == frozenset(b)] for b in blocks]
            if any(not x for x in per_block):
                continue
            for btypes in product(*per_block):
                for idx in _nondecreasing(len(free), j):
                    cty = list(btypes) + [free[i] for i in idx]
                    if stats is not None:
                        stats["cores"] = stats.get("cores", 0) + 1
                    G = alive(kb, cty)
                    res = _search_labels(kb, cty, G)
                    if res is not None:
                        lab, kids = res
                        return (cty, lab, kids)
    return None


def _partitions(xs):
    if not xs:
        yield []
        return
    first, rest = xs[0], xs[1:]
    for p in _partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def _nondecreasing(nt, k, start=0):
    if k == 0:
        yield ()
        return
    for i in range(start, nt):
        for rest in _nondecreasing(nt, k - 1, i):
            yield (i,) + rest


def _search_labels(kb: KB, cty, G):
    """Backtracking over the core labels pair by pair (rows in order),
    pruning on the at-most clauses at both ends; a core element's star is
    checked when its row is complete."""
    k = len(cty)
    lab = [[frozenset()] * k for _ in range(k)]
    kids = [None] * k
    pairs = [(c, d) for c in range(k) for d in range(c, k)]
    choices = {(c, d): _label_choices(kb, cty[c], cty[d], c == d) for (c, d) in pairs}
    ups = [[(kk, R, b) for (a, kk, R, b) in kb.upper if a in cty[c]] for c in range(k)]
    cnt = [[0] * len(ups[c]) for c in range(k)]
    anchors = [anchor_options(kb, G, c) for c in range(k)]

    def add(c, L, t, sign):
        ok = True
        for j, (kk, R, b) in enumerate(ups[c]):
            if R in L and b in t:
                cnt[c][j] += sign
                if cnt[c][j] > kk:
                    ok = False
        return ok

    def go(i):
        if i == len(pairs):
            return True
        c, d = pairs[i]
        for L in choices[(c, d)]:
            lab[c][d] = L
            lab[d][c] = flipL(L)
            ok = True
            if L:
                ok = add(c, L, cty[d], 1)
                if c != d:
                    ok = add(d, flipL(L), cty[c], 1) and ok
            if ok:
                row_done = (d == k - 1)
                w = None
                if row_done:
                    w = _support(kb, cty[c], core_nbrs(cty, lab, c), {}, anchors[c])
                if not row_done or w is not None:
                    if row_done:
                        kids[c] = w[1]
                    if go(i + 1):
                        return True
            if L:
                add(c, L, cty[d], -1)
                if c != d:
                    add(d, flipL(L), cty[c], -1)
        lab[c][d] = frozenset()
        lab[d][c] = frozenset()
        return False

    if go(0):
        return ([row[:] for row in lab], [list(x) for x in kids])
    return None


def show_hint(kb: KB, hint) -> str:
    cty, lab, kids = hint

    def T(t):
        return "{" + ",".join(kb.cname(a) for a in sorted(t)) + "}"

    def Lb(L):
        return "{" + ",".join(kb.rname(R) for R in sorted(L)) + "}"

    out = []
    for c, t in enumerate(cty):
        out.append(f"core {c}: {T(t)}")
        for d in range(len(cty)):
            if lab[c][d] and d >= c:
                out.append(f"  edge {c}->{d}: {Lb(lab[c][d])}")
        for (L, s) in kids[c]:
            out.append(f"  child {Lb(L)} {T(s)}")
    return "\n".join(out)
