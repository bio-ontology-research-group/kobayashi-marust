"""Model finder over the normal form of the sroiq-c2a route (stage H1).

An untrusted producer: a completion-graph construction with anywhere
pairwise blocking whose blocked nodes share the record of their blocker, so
the record table of the certificate (`rec`/`ranc`/`rpar`/`rce`/`rkid`
lines) is the set of records of the unblocked tree nodes. Types are closed
by Horn propagation with depth-first choice on disjunctive gcis; at-most
clauses are met by merging successors. The proved checker judges every
hint; `hintcheck.check` mirrors it to explain rejections.
"""

import time
from collections import deque

from hintcheck import Hint, flip


class Fail(Exception):
    def __init__(self, msg, blame=()):
        super().__init__(msg)
        self.blame = list(blame)


class Node:
    __slots__ = ('id', 'core', 'parent', 'plab', 'ty', 'kids', 'ce', 'alive', 'blocked')

    def __init__(self, nid, core, parent, plab, ty):
        self.id = nid
        self.core = core          # core index, or None for a tree node
        self.parent = parent      # parent node id (tree nodes)
        self.plab = plab          # label from the parent to this node
        self.ty = ty
        self.kids = []
        self.ce = {}              # core index -> label from this node to it
        self.alive = True
        self.blocked = False


class Finder:
    def __init__(self, ix, max_nodes=200000, max_close=200000, prefer=None, bad=None, deadline=None):
        self.ix = ix
        self.deadline = deadline
        self.bad = bad if bad is not None else set()
        self.cur = None
        self.cache = {}
        self.close_calls = 0
        self.max_close = max_close
        self.max_nodes = max_nodes
        self.nodes = []
        self.lab = {}
        self.rep = {}
        self.blocked_by = {}
        self.ce_in = {}           # core index -> set of tree node ids with a core entry to it
        self.queue = deque()
        self.queued = set()
        self.prefer = prefer      # optional key function on head names
        self.stats = {}

    # ---- types ----
    def close(self, seed):
        key = frozenset(seed)
        r = self.cache.get(key, 0)
        if r != 0:
            return r
        r = self._close(key)
        self.cache[key] = r
        return r

    def close_core(self, b, seed):
        """Close a core type; choosing another nominal name o brings in the
        current type of o's core element (they will be identified)."""
        imp = {}
        for o, d in self.nom_core.items():
            if d != b and d in self.cores:
                imp[o] = self.nodes[self.core_node[d]].ty
        if not imp:
            return self.close(seed)
        # first avoid identifying two other core elements with each other
        self._owner = {o: d for o, d in self.nom_core.items() if o in imp}
        r = self._close(frozenset(seed), imp, strict=True)
        if r is None:
            r = self._close(frozenset(seed), imp)
        return r

    def close_tree(self, seed):
        """Close a tree type: no nominal name allowed."""
        key = (frozenset(seed), 'tree')
        r = self.cache.get(key, 0)
        if r != 0:
            return r
        r = self._close(frozenset(seed), forbid=self.ix.nomset)
        self.cache[key] = r
        return r

    def _close(self, seed, imp=None, strict=False, forbid=None):
        self.close_calls += 1
        if self.close_calls > self.max_close:
            raise Fail('closure budget')
        if self.deadline and self.close_calls % 64 == 0 and time.time() > self.deadline:
            raise Fail('time budget')
        ix = self.ix
        T = set()
        cnt = {}
        pend = []
        q = []

        bad = [False]

        def add(a):
            if a not in T:
                if forbid and a in forbid:
                    bad[0] = True
                T.add(a)
                q.append(a)
                if imp and a in imp:
                    for x in imp[a]:
                        add(x)
        for g in ix.gci_empty:
            h = ix.gci[g][1]
            if not h:
                return None
            if len(h) == 1:
                add(h[0])
            else:
                pend.append(g)
        for a in seed:
            add(a)
        gci, blen, byb = ix.gci, ix.body_len, ix.gci_by_body
        while q:
            if bad[0]:
                return None
            a = q.pop()
            for g in byb[a]:
                c = cnt.get(g, 0) + 1
                cnt[g] = c
                if c == blen[g]:
                    h = gci[g][1]
                    if not h:
                        return None
                    if len(h) == 1:
                        add(h[0])
                    else:
                        pend.append(g)
        if bad[0]:
            return None
        if not pend and self.bad and frozenset(T) in self.bad:
            return None
        if strict and len(set(self._owner[o] for o in T if o in imp)) > 1:
            return None
        for g in pend:
            h = gci[g][1]
            if any(x in T for x in h):
                continue
            heads = sorted(set(h), key=self.prefer) if self.prefer else list(dict.fromkeys(h))
            for x in heads:
                r = self._close(frozenset(T) | {x}, imp, strict, forbid)
                if r is not None:
                    return r
            return None
        T = frozenset(T)
        if self.bad and T in self.bad:
            return None
        return T

    # ---- graph ----
    def new_node(self, core, parent, plab, ty):
        if len(self.nodes) >= self.max_nodes:
            raise Fail('node budget')
        v = Node(len(self.nodes), core, parent, plab, ty)
        self.nodes.append(v)
        self.push(v.id)
        return v

    def push(self, i):
        if i not in self.queued:
            self.queued.add(i)
            self.queue.append(i)

    def key(self, v):
        if v.core is not None:
            return None
        p = self.nodes[v.parent]
        if p.core is not None:
            return (v.ty, ('a', p.core, flip(v.plab)))
        return (v.ty, ('p', flip(v.plab), p.ty))

    def kill(self, i):
        st = [i]
        while st:
            v = self.nodes[st.pop()]
            if not v.alive:
                continue
            v.alive = False
            for d in v.ce:
                self.ce_in.get(d, set()).discard(v.id)
            for b in self.blocked_by.pop(v.id, ()):
                self.push(b)
            st.extend(v.kids)

    def touched(self, v):
        """Requeue everything whose star or record mentions v."""
        self.push(v.id)
        if v.parent is not None:
            self.push(v.parent)
        for k in v.kids:
            self.push(k)
        for b in self.blocked_by.pop(v.id, ()):
            self.push(b)
        if v.core is not None:
            for c in self.adj.get(v.core, ()):
                self.push(self.core_node[c])
            for t in list(self.ce_in.get(v.core, ())):
                self.push(t)

    def grow(self, v, names):
        if names <= v.ty:
            return False
        t = self.close_tree(v.ty | names) if v.core is None else self.close_core(v.core, v.ty | names)
        if t is None:
            bl = [v.ty] + ([self.cur.ty] if self.cur is not None else [])
            if v.core is None and self.close(v.ty | names) is not None:
                raise Fail('a tree type must hold a nominal name', bl)
            raise Fail('clash when growing a %s type' % ('core' if v.core is not None else 'tree'), bl)
        noms = t & self.ix.nomset
        if v.core is None and noms:
            raise Fail('nominal name in a tree type')
        v.ty = t
        self.touched(v)
        for o in noms:
            c = self.nom_core.get(o)
            if c is not None and c != v.core:
                self.merge_core(v.core, c)
                return True
        return True

    def merge_core(self, b, c):
        """Identify core elements b and c (they share a nominal name)."""
        if b == c:
            return
        self.stats['core_merges'] = self.stats.get('core_merges', 0) + 1
        vb, vc = self.nodes[self.core_node[b]], self.nodes[self.core_node[c]]
        t = self.close_core(b, vb.ty | vc.ty)
        if t is None:
            raise Fail('clash when identifying two core elements', [vb.ty, vc.ty])
        vb.ty = t
        vc.alive = False
        self.cores.remove(c)
        for o, d in list(self.nom_core.items()):
            if d == c:
                self.nom_core[o] = b
        # labels
        for d in list(self.adj.get(c, ())):
            L = self.lab.pop((c, d), frozenset())
            self.lab.pop((d, c), None)
            self.adj.get(d, set()).discard(c)
            dd = b if d == c else d
            if L:
                self.add_core_lab(b, dd, L)
        self.adj.pop(c, None)
        # kids
        for k in vc.kids:
            self.nodes[k].parent = vb.id
            vb.kids.append(k)
        vc.kids = []
        # core entries of tree nodes
        for i in list(self.ce_in.pop(c, ())):
            w = self.nodes[i]
            L = w.ce.pop(c, frozenset())
            if not w.alive:
                continue
            if self.nodes[w.parent].core == b:
                w.plab = w.plab | flip(L)
            else:
                w.ce[b] = w.ce.get(b, frozenset()) | L
                self.ce_in.setdefault(b, set()).add(i)
            self.touched(w)
        self.touched(vb)
        for k in vb.kids:
            self.touched(self.nodes[k])
        for o in t & self.ix.nomset:
            d = self.nom_core.get(o)
            if d is not None and d != b:
                return self.merge_core(b, d)

    def add_core_lab(self, b, c, L):
        old = self.lab.get((b, c), frozenset())
        if L <= old:
            return False
        self.lab[(b, c)] = old | L
        self.lab[(c, b)] = self.lab.get((c, b), frozenset()) | flip(L)
        self.adj.setdefault(b, set()).add(c)
        self.adj.setdefault(c, set()).add(b)
        self.touched(self.nodes[self.core_node[b]])
        self.touched(self.nodes[self.core_node[c]])
        return True

    def entries(self, v):
        """The star of v: (L, ty, kind, ref)."""
        out = []
        if v.core is not None:
            for c in sorted(self.adj.get(v.core, ())):
                L = self.lab.get((v.core, c))
                if L:
                    out.append((L, self.nodes[self.core_node[c]].ty, 'core', c))
        else:
            p = self.nodes[v.parent]
            out.append((flip(v.plab), p.ty, 'par', v.parent))
            for d, L in v.ce.items():
                if L:
                    out.append((L, self.nodes[self.core_node[d]].ty, 'ce', d))
        for k in v.kids:
            w = self.nodes[k]
            out.append((w.plab, w.ty, 'kid', k))
        return out

    def target(self, e):
        kind, ref = e[2], e[3]
        if kind in ('core', 'ce'):
            return self.nodes[self.core_node[ref]]
        return self.nodes[ref]

    def fwd(self, t, L):
        out = set()
        alls = self.ix.all_by
        for a in t:
            for (S, c) in alls.get(a, ()):
                if S in L:
                    out.add(c)
        return out

    # ---- setup ----
    def setup(self, extra_core=()):
        ix = self.ix
        # one core element per nominal name
        self.k = len(ix.noms)
        if self.k == 0:
            self.k = 1          # a core of one element when there is no nominal
        self.core_node = []
        self.nom_core = {}
        self.adj = {}
        for b in range(self.k):
            seed = {ix.noms[b]} if ix.noms else set()
            t = self.close(seed)
            if t is None:
                raise Fail('clash in a core type')
            v = self.new_node(b, None, None, t)
            self.core_node.append(v.id)
            if ix.noms:
                self.nom_core[ix.noms[b]] = b
        self.cores = list(range(self.k))
        for b in range(self.k):
            v = self.nodes[self.core_node[b]]
            t = self.close_core(b, {ix.noms[b]} if ix.noms else set())
            if t is None:
                raise Fail('clash in a core type')
            v.ty = t
        for b in range(self.k):
            v = self.nodes[self.core_node[b]]
            if not v.alive:
                continue
            for o in v.ty & ix.nomset:
                d = self.nom_core[o]
                if d != b and d in self.cores and b in self.cores:
                    self.merge_core(min(b, d), max(b, d))

    # ---- expansion ----
    def process(self, v):
        ix = self.ix
        if not v.alive:
            return
        self.cur = v
        if v.core is None:
            if self.nodes[v.parent].blocked or not self.nodes[v.parent].alive:
                return
            k = self.key(v)
            r = self.rep.get(k)
            if r is not None and r != v.id:
                rv = self.nodes[r]
                if rv.alive and not rv.blocked and self.key(rv) == k:
                    if not v.blocked:
                        v.blocked = True
                        for c in v.kids:
                            self.kill(c)
                        v.kids = []
                    self.blocked_by.setdefault(r, set()).add(v.id)
                    return
            self.rep[k] = v.id
            v.blocked = False
        E = self.entries(v)
        # universals across every edge, both directions
        for e in E:
            w = self.target(e)
            L = e[0]
            f = self.fwd(v.ty, L) - w.ty
            if f:
                self.grow(w, f)
                return self.push(v.id)
            b = self.fwd(w.ty, flip(L)) - v.ty
            if b:
                self.grow(v, b)
                return
        # existentials and at-least
        for a in v.ty:
            for (R, b) in ix.ex_by.get(a, ()):
                if not any(R in e[0] and b in e[1] for e in E):
                    self.satisfy(v, R, b)
                    return self.push(v.id)
            for (k, R, b) in ix.ge_by.get(a, ()):
                c = sum(1 for e in E if R in e[0] and b in e[1])
                if c < k:
                    for _ in range(k - c):
                        self.new_kid(v, R, b)
                    return self.push(v.id)
        # at-most
        for a in v.ty:
            for (k, R, b) in ix.le_by.get(a, ()):
                S = [e for e in E if R in e[0] and b in e[1]]
                if len(S) > k:
                    self.merge(v, S)
                    return self.push(v.id)

    def satisfy(self, v, R, b):
        L = self.ix.up[R]
        seed = {b} | self.fwd(v.ty, L)
        t = self.close_tree(seed)
        if t is not None:
            return self.new_kid(v, R, b, t)
        if self.close(seed) is None:
            raise Fail('no type for a successor')
        d = self.pick_core(seed, (), v, L)
        if d is None:
            raise Fail('no core element can be the nominal successor')
        self.link_core(v, d, L, seed)

    def pick_core(self, seed, exclude, v=None, L=None):
        """A core element that can take the names `seed` and whose
        universals back across the edge fit v's type."""
        def back_ok(tc):
            if v is None:
                return True
            b = self.fwd(tc, flip(L)) - v.ty
            if not b:
                return True
            t = self.close(v.ty | b) if v.core is None else self.close_core(v.core, v.ty | b)
            return t is not None and (v.core is not None or not (t & self.ix.nomset))
        for c in self.cores:
            if c in exclude:
                continue
            tc = self.nodes[self.core_node[c]].ty
            if seed <= tc and back_ok(tc):
                return c
        for c in self.cores:
            if c in exclude:
                continue
            tc = self.close_core(c, self.nodes[self.core_node[c]].ty | seed)
            if tc is not None and back_ok(tc):
                return c
        return None

    def link_core(self, v, d, L, seed):
        dn = self.nodes[self.core_node[d]]
        if v.core is not None:
            self.add_core_lab(v.core, d, L)
        elif self.nodes[v.parent].core == d:
            v.plab = v.plab | flip(L)
            self.touched(v)
            self.push(v.parent)
        else:
            old = v.ce.get(d, frozenset())
            v.ce[d] = old | L
            self.ce_in.setdefault(d, set()).add(v.id)
            self.touched(v)
            self.push(dn.id)
        self.grow(dn, frozenset(seed))

    def new_kid(self, v, R, b, t=None):
        L = self.ix.up[R]
        if t is None:
            seed = {b} | self.fwd(v.ty, L)
            t = self.close_tree(seed)
            if t is None:
                # an at-least successor that must be a nominal: a core element not yet counted
                used = set()
                for e in self.entries(v):
                    if R in e[0] and b in e[1] and e[2] in ('core', 'ce'):
                        used.add(e[3])
                d = self.pick_core(seed, used, v, L)
                if d is None:
                    raise Fail('at-least: no further core element for a nominal successor')
                return self.link_core(v, d, L, seed)
        w = self.new_node(None, v.id, L, t)
        v.kids.append(w.id)
        return w

    def merge(self, v, S):
        kids = [e for e in S if e[2] == 'kid']
        others = [e for e in S if e[2] != 'kid']
        # merge a kid into another entry
        for i, e1 in enumerate(kids):
            w1 = self.nodes[e1[3]]
            for e2 in kids[i + 1:] + others:
                w2 = self.target(e2)
                if e2[2] == 'kid':
                    L = self.ix.upL(e1[0] | e2[0])
                    t = self.close_tree(w1.ty | w2.ty | self.fwd(v.ty, L))
                    if t is None:
                        continue
                    w2.plab = L
                    w2.ty = t
                    v.kids.remove(w1.id)
                    self.kill(w1.id)
                    self.touched(w2)
                    return
                t = self.close(w2.ty | w1.ty | self.fwd(v.ty, e1[0]))
                if t is None:
                    continue
                if e2[2] == 'par':
                    v.kids.remove(w1.id)
                    self.kill(w1.id)
                    v.plab = self.ix.upL(v.plab | flip(e1[0]))
                    self.touched(v)
                    self.grow(w2, t)
                    return
                d = e2[3]
                v.kids.remove(w1.id)
                self.kill(w1.id)
                if v.core is not None:
                    self.add_core_lab(v.core, d, e1[0])
                else:
                    v.ce[d] = v.ce.get(d, frozenset()) | e1[0]
                    self.ce_in.setdefault(d, set()).add(v.id)
                    self.touched(v)
                self.grow(w2, t)
                return
        raise Fail('at-most: no merge possible (%d kids, %d other entries)' % (len(kids), len(others)))

    def run(self, max_steps=5000000):
        steps = 0
        while True:
            while self.queue:
                i = self.queue.popleft()
                self.queued.discard(i)
                try:
                    self.process(self.nodes[i])
                except Fail as e:
                    if self.cur is not None and not e.blame:
                        e.blame = [self.cur.ty]
                    raise
                steps += 1
                if self.deadline and steps % 256 == 0 and time.time() > self.deadline:
                    raise Fail('time budget')
                if steps > max_steps:
                    raise Fail('step budget')
            # recheck blocked nodes whose blocker changed
            again = False
            for v in self.nodes:
                if v.alive and v.blocked:
                    r = self.rep.get(self.key(v))
                    if r is None or r == v.id or not self.nodes[r].alive or self.nodes[r].blocked:
                        self.push(v.id)
                        again = True
            if not again:
                break
        self.stats.update({'nodes': len(self.nodes), 'alive': sum(1 for v in self.nodes if v.alive),
                      'steps': steps, 'closures': self.close_calls})

    # ---- hint ----
    def hint(self):
        live = sorted(self.cores)
        num = {b: i for i, b in enumerate(live)}
        h = Hint(len(live))
        for b in live:
            h.ty[num[b]] = self.nodes[self.core_node[b]].ty
        for (b, c), L in self.lab.items():
            if L and b in num and c in num:
                h.lab[(num[b], num[c])] = L
        for b in live:
            v = self.nodes[self.core_node[b]]
            h.kids[num[b]] = [(self.nodes[k].plab, self.nodes[k].ty) for k in v.kids]
        seen = set()
        for v in self.nodes:
            if not v.alive or v.core is not None or v.blocked:
                continue
            k = self.key(v)
            if k in seen:
                continue
            seen.add(k)
            t, par = k
            if par[0] == 'a':
                k = (t, ('a', num[par[1]], par[2]))
            h.recs.append((k, {num[d]: L for d, L in v.ce.items() if L},
                           [(self.nodes[c].plab, self.nodes[c].ty) for c in v.kids]))
        return h


def solve(ix, restarts=40, **kw):
    """Run the finder, restarting with the types blamed for each failure
    forbidden (they are dropped as nogoods; an unsound nogood only costs
    completeness of the producer)."""
    bad = set()
    last = None
    for r in range(restarts):
        F = Finder(ix, bad=bad, **kw)
        try:
            F.setup()
            F.run()
            F.stats['restarts'] = r
            return F
        except Fail as e:
            last = e
            new = [t for t in e.blame if t not in bad]
            if not new or str(e) in ('node budget', 'step budget', 'closure budget', 'time budget'):
                break
            bad.update(new)
    raise last


def flat_hint(F):
    """A hint without tree children: every live core element and unblocked
    tree node is a core element; an edge to a blocked node goes to its
    blocker (folding), and identical siblings get copies of their target.
    Valid only when the folded stars still hold, which the caller checks;
    needed because the checker decides certificates in exponential time
    today (see the design note)."""
    live = sorted(F.cores)
    ids = [F.core_node[b] for b in live]
    tree = [v.id for v in F.nodes if v.alive and v.core is None and not v.blocked
            and F.nodes[v.parent].alive and not F.nodes[v.parent].blocked]
    num = {}
    for i in ids + tree:
        num[i] = len(num)
    coreidx = {b: num[F.core_node[b]] for b in live}
    tys = [F.nodes[i].ty for i in ids + tree]

    def target(i):
        v = F.nodes[i]
        if v.blocked:
            return num.get(F.rep.get(F.key(v)))
        return num.get(i)
    down = {}      # element -> list of (target element, label)
    for i in ids + tree:
        v = F.nodes[i]
        lst = []
        for k in v.kids:
            w = F.nodes[k]
            if not w.alive:
                continue
            t = target(k)
            if t is None:
                return None
            lst.append((t, w.plab))
        down[num[i]] = lst
    side = []
    for i in ids + tree:
        for d, L in F.nodes[i].ce.items():
            if L:
                side.append((num[i], coreidx[d], L))
    # copies for repeated targets of one element
    edges = []
    for e, lst in list(down.items()):
        seen = {}
        for (t, L) in lst:
            if t in seen or t == e:
                c = len(tys)
                tys.append(tys[t])
                edges.append((e, c, L))
                for (t2, L2) in down.get(t, []):
                    edges.append((c, t2, L2))
                for (a, d, L3) in side:
                    if a == t:
                        edges.append((c, d, L3))
            else:
                seen[t] = 1
                edges.append((e, t, L))
    h = Hint(len(tys))
    h.ty = tys
    for (b, c), L in F.lab.items():
        if L and b in coreidx and c in coreidx:
            h.lab[(coreidx[b], coreidx[c])] = L
    for (a, b, L) in edges + side:
        h.add_lab(a, b, L)
    h.kids = [[] for _ in range(len(tys))]
    return h
