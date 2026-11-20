#!/usr/bin/env python3
"""Refutation producer for `km-owl-reference --procedure refute` (untrusted).

Reads the clause dump of `km-owl-reference --procedure refute --print-clauses`
(the `dosnC` clauses of the chain route, the nominal names, the data atoms and
the cell table of the data oracle) and searches for a ground refutation:
Horn saturation over the named individuals (plus anonymous successors up to a
depth bound), equality by rewriting, data values with the cell oracle, and a
bounded case split on disjunctions. It prints a certificate in the text format
of `parseRefuteCert` (`lean/KMOWLReferenceCheck.lean`). Only the Lean checker's
acceptance certifies anything; this tool's verdicts are unchecked.

Usage: produce.py DUMP [--out CERT] [--max-depth D] [--time-limit S]
"""

import argparse
import subprocess
import sys
import time


class Clash(Exception):
    def __init__(self, info):
        super().__init__("clash")
        self.info = info


class GiveUp(Exception):
    pass


def role(t):
    return (t[0] == '+', int(t[1:]))


class Dump:
    def __init__(self, path):
        self.clauses = []
        self.noms = []
        self.names = {}
        self.nominal_iri = {}
        self.role_iri = {}
        self.atoms = {}
        self.cg = []
        self.supported = False
        opener = open
        if path.endswith('.gz'):
            import gzip
            opener = gzip.open
        with opener(path, 'rt') as f:
            for line in f:
                ws = line.split()
                if not ws:
                    continue
                h = ws[0]
                if h == 'cl':
                    self.clauses.append(self.parse_clause(ws[1:]))
                elif h == 'nom':
                    self.noms.append(int(ws[1]))
                elif h == 'concept':
                    self.names[int(ws[1])] = ws[2] if len(ws) > 2 else ''
                elif h == 'nominal':
                    self.nominal_iri[int(ws[1])] = ws[2] if len(ws) > 2 else ''
                elif h == 'role':
                    self.role_iri[int(ws[1])] = ws[2] if len(ws) > 2 else ''
                elif h == 'atom':
                    self.atoms[int(ws[1])] = ' '.join(ws[2:])
                elif h == 'supported':
                    self.supported = ws[1] == 'true'
                elif h in ('concepts', 'roles', 'dprops', 'atoms', 'dprop', 'cells'):
                    pass
        self.nomset = set(self.noms)
        # the data oracle: literal sets (frozensets of (atom, bool)) -> empty?
        # answered by `km-owl-reference --procedure refute --emp`; unknown sets
        # count as nonempty and are queued for the next round.
        self.emp_known = {}
        self.queries = set()

    @staticmethod
    def parse_clause(ws):
        k = ws[0]
        if k == 'gci':
            i = ws.index('->')
            return ('gci', tuple(int(x) for x in ws[1:i]), tuple(int(x) for x in ws[i + 1:]))
        if k == 'some':
            return ('some', int(ws[1]), role(ws[2]), int(ws[3]))
        if k == 'all':
            return ('all', int(ws[1]), role(ws[2]), int(ws[3]))
        if k == 'atleast':
            return ('atleast', int(ws[1]), int(ws[2]), role(ws[3]), int(ws[4]))
        if k == 'atmost':
            return ('atmost', int(ws[1]), int(ws[2]), role(ws[3]), int(ws[4]))
        if k == 'chain':
            rs = [role(t) for t in ws[1:]]
            return ('chain', tuple(rs[:-1]), rs[-1])
        if k in ('dsome', 'datleast', 'datmost'):
            if k == 'dsome':
                a, u, rest = int(ws[1]), int(ws[2]), ws[3:]
                n = None
            else:
                a, n, u, rest = int(ws[1]), int(ws[2]), int(ws[3]), ws[4:]
            i = rest.index('/')
            pos = tuple(int(x) for x in rest[:i])
            neg = tuple(int(x) for x in rest[i + 1:])
            if k == 'dsome':
                return ('dsome', a, u, pos, neg)
            return (k, a, n, u, pos, neg)
        if k == 'dall':
            lits = tuple((int(t[1:]), False) if t.startswith('~') else (int(t), True) for t in ws[3:])
            return ('dall', int(ws[1]), int(ws[2]), lits)
        if k == 'dsub':
            return ('dsub', int(ws[1]), int(ws[2]))
        return ('?',)

    def emp(self, lits):
        if not self.supported:
            return False
        lits = frozenset(lits)
        r = self.emp_known.get(lits)
        if r is None:
            self.queries.add(lits)
            return False
        return r


def rtkey(R, x, y):
    pos, k = R
    return ('r', x, k, y) if pos else ('r', y, k, x)


def mkline(keys):
    keys = tuple(keys)
    if len(keys) == 1:
        return keys[0]
    return ('disj', keys)


def pairs_of(ys):
    out = []
    for i in range(len(ys)):
        for j in range(i + 1, len(ys)):
            out.append((ys[i], ys[j]))
    return out


def subst_o(key, y, x):
    def s(i):
        return x if i == y else i
    t = key[0]
    if t == 'c':
        return ('c', s(key[1]), key[2])
    if t == 'r':
        return ('r', s(key[1]), key[2], s(key[3]))
    if t in ('eq', 'ne'):
        return (t, s(key[1]), s(key[2]))
    if t == 'd':
        return ('d', s(key[1]), key[2], key[3])
    return key


def subst_v(key, y, x):
    def s(i):
        return x if i == y else i
    t = key[0]
    if t == 'd':
        return ('d', key[1], key[2], s(key[3]))
    if t == 'lit':
        return ('lit', s(key[1]), key[2], key[3])
    if t in ('veq', 'vne'):
        return (t, s(key[1]), s(key[2]))
    return key


def key_elems(key):
    t = key[0]
    if t == 'c':
        return [key[1]]
    if t == 'r':
        return [key[1], key[3]]
    if t in ('eq', 'ne', 'veq', 'vne'):
        return [key[1], key[2]]
    if t == 'd':
        return [key[1], key[3]]
    if t == 'lit':
        return [key[1]]
    if t == 'disj':
        out = []
        for k in key[1]:
            out.extend(key_elems(k))
        return out
    return []


class Log:
    """Append-only record of steps (shared by all branches)."""

    def __init__(self):
        self.steps = []      # dict(kind, args, prem, outs, ctx)
        self.fact_step = []  # fid -> (step index, out index)
        self.fact_key = []   # fid -> key
        self.creator = {}    # element -> step index
        self.next_id = 0
        self.ctx_parent = [None]

    def new_id(self):
        x = self.next_id
        self.next_id += 1
        return x


class State:
    def __init__(self, dump, log, ctx, max_depth):
        self.D = dump
        self.L = log
        self.ctx = ctx
        self.max_depth = max_depth
        self.fact = {}          # key -> fid
        self.label = {}         # x -> set of concepts
        self.out = {}           # x -> {k: set(y)}
        self.inn = {}           # y -> {k: set(x)}
        self.dvals = {}         # x -> {u: set(w)}
        self.vlits = {}         # w -> {(j, b)}
        self.depth = {}
        self.parent = {}        # union-find for objects
        self.vparent = {}
        self.nomelem = {}
        self.pending = []       # disjunction fids
        self.agenda = []
        self.dead = set()
        self.vdead = set()

    def copy(self, ctx):
        s = State(self.D, self.L, ctx, self.max_depth)
        s.fact = dict(self.fact)
        s.label = {k: set(v) for k, v in self.label.items()}
        s.out = {k: {r: set(ys) for r, ys in v.items()} for k, v in self.out.items()}
        s.inn = {k: {r: set(ys) for r, ys in v.items()} for k, v in self.inn.items()}
        s.dvals = {k: {u: set(ws) for u, ws in v.items()} for k, v in self.dvals.items()}
        s.vlits = {k: set(v) for k, v in self.vlits.items()}
        s.depth = dict(self.depth)
        s.nomelem = dict(self.nomelem)
        s.pending = list(self.pending)
        s.dead = set(self.dead)
        s.vdead = set(self.vdead)
        return s

    # ---- recording -------------------------------------------------------
    def step(self, kind, args, prem, outs, fresh=()):
        L = self.L
        si = len(L.steps)
        L.steps.append({'kind': kind, 'args': args, 'prem': list(prem), 'outs': list(outs),
                        'ctx': self.ctx})
        for x in fresh:
            L.creator[x] = si
        fids = []
        for i, key in enumerate(outs):
            fid = len(L.fact_key)
            L.fact_key.append(key)
            L.fact_step.append((si, i))
            fids.append(fid)
        for key, fid in zip(outs, fids):
            if key not in self.fact:
                self.fact[key] = fid
                self.agenda.append(key)
        return fids

    def has(self, key):
        return key in self.fact

    # ---- element management ----------------------------------------------
    def nominal_element(self, a):
        x = self.nomelem.get(a)
        if x is not None and x not in self.dead:
            return x
        x = self.L.new_id()
        self.depth[x] = 0
        self.nomelem[a] = x
        self.step('nom', (x, a), [], [('c', x, a)], fresh=[x])
        self.new_element(x)
        return x

    def new_element(self, x):
        self.label.setdefault(x, set())
        for ci in self.D.gci_empty:
            self.apply_gci(ci, x)

    # ---- rules -----------------------------------------------------------
    def apply_gci(self, ci, x):
        _, body, head = self.D.clauses[ci]
        prem = []
        for a in body:
            f = self.fact.get(('c', x, a))
            if f is None:
                return
            prem.append(f)
        keys = [('c', x, h) for h in head]
        if any(self.has(k) for k in keys) and len(keys) > 1:
            return
        line = mkline(keys)
        if self.has(line):
            return
        fids = self.step('gci', (ci, x), prem, [line])
        if line[0] == 'disj':
            if not keys:
                raise Clash(('empty', fids[0]))
            self.pending.append(fids[0])

    def add_c(self, x, a):
        D = self.D
        for ci in D.gci_by.get(a, ()):
            self.apply_gci(ci, x)
        if a in D.nomset:
            z = self.nomelem.get(a)
            if z is None or z in self.dead:
                self.nomelem[a] = x
            elif z != x:
                self.merge(z, x, a)
                return
        for ci in D.some_by.get(a, ()):
            self.apply_some(ci, x)
        for ci in D.all_by.get(a, ()):
            _, _, R, b = D.clauses[ci]
            for y in self.neighbours(x, R):
                self.apply_all(ci, x, y)
        for ci in D.atmost_by.get(a, ()):
            self.apply_atmost(ci, x)
        for ci in D.dsome_by.get(a, ()):
            self.apply_dsome(ci, x)
        for ci in D.dall_by.get(a, ()):
            u = D.clauses[ci][2]
            for w in list(self.dvals.get(x, {}).get(u, ())):
                self.apply_dall(ci, x, w)
        for ci in D.datmost_by.get(a, ()):
            self.apply_datmost(ci, x)

    def neighbours(self, x, R):
        pos, k = R
        ys = self.out.get(x, {}).get(k, ()) if pos else self.inn.get(x, {}).get(k, ())
        return [y for y in ys if y not in self.dead]

    def apply_some(self, ci, x):
        _, a, R, b = self.D.clauses[ci]
        fa = self.fact.get(('c', x, a))
        if fa is None:
            return
        if b in self.D.nomset:
            y = self.nominal_element(b)
            fb = self.fact.get(('c', y, b))
            key = rtkey(R, x, y)
            if not self.has(key):
                self.step('exnom', (ci, x, y), [fa, fb], [key])
            return
        # already satisfied by an existing neighbour with b
        for y in self.neighbours(x, R):
            if self.has(('c', y, b)):
                return
        if self.depth.get(x, 0) >= self.max_depth:
            return
        y = self.L.new_id()
        self.depth[y] = self.depth.get(x, 0) + 1
        self.label.setdefault(y, set())
        self.step('ex', (ci, x, y), [fa], [rtkey(R, x, y), ('c', y, b)], fresh=[y])
        self.new_element(y)

    def apply_all(self, ci, x, y):
        _, a, R, b = self.D.clauses[ci]
        key = ('c', y, b)
        if self.has(key):
            return
        fa = self.fact.get(('c', x, a))
        fr = self.fact.get(rtkey(R, x, y))
        if fa is None or fr is None:
            return
        self.step('all', (ci, x, y), [fa, fr], [key])

    def apply_atmost(self, ci, x):
        _, a, k, R, b = self.D.clauses[ci]
        fa = self.fact.get(('c', x, a))
        if fa is None:
            return
        ys = [y for y in self.neighbours(x, R) if self.has(('c', y, b))]
        if len(ys) <= k:
            return
        ys = sorted(ys)[:k + 1]
        prem = [fa]
        triples = []
        for y in ys:
            fr = self.fact[rtkey(R, x, y)]
            fc = self.fact[('c', y, b)]
            prem += [fr, fc]
            triples.append((y, fr, fc))
        keys = [('eq', p, q) for p, q in pairs_of(ys)]
        line = mkline(keys)
        if self.has(line):
            return
        fids = self.step('atmost', (ci, x, triples), prem, [line])
        if line[0] == 'disj':
            if not keys:
                raise Clash(('empty', fids[0]))
            self.pending.append(fids[0])

    def apply_dsome(self, ci, x):
        _, a, u, pos, neg = self.D.clauses[ci]
        fa = self.fact.get(('c', x, a))
        if fa is None:
            return
        # satisfied by an existing value with these literals
        for w in self.dvals.get(x, {}).get(u, ()):
            if all(self.has(('lit', w, j, True)) for j in pos) and \
                    all(self.has(('lit', w, j, False)) for j in neg):
                return
        w = self.L.new_id()
        outs = [('d', x, u, w)] + [('lit', w, j, True) for j in pos] + \
            [('lit', w, j, False) for j in neg]
        self.vlits[w] = set()
        self.step('dex', (ci, x, w), [fa], outs, fresh=[w])

    def apply_dall(self, ci, x, w):
        _, a, u, head = self.D.clauses[ci]
        fa = self.fact.get(('c', x, a))
        fd = self.fact.get(('d', x, u, w))
        if fa is None or fd is None:
            return
        keys = [('lit', w, j, b) for j, b in head]
        if len(keys) > 1 and any(self.has(k) for k in keys):
            return
        line = mkline(keys)
        if self.has(line):
            return
        fids = self.step('dall', (ci, x, w), [fa, fd], [line])
        if line[0] == 'disj':
            if not keys:
                raise Clash(('empty', fids[0]))
            self.pending.append(fids[0])

    def entail_lit(self, w, j, b):
        """A `dlit` step when the literals of `w` entail `(j, b)`."""
        key = ('lit', w, j, b)
        if self.has(key):
            return True
        if not self.D.supported:
            return False
        cur = self.vlits.get(w, set())
        if self.D.emp(set(cur) | {(j, not b)}):
            refs = [self.fact[('lit', w, j2, b2)] for (j2, b2) in sorted(cur)]
            self.step('dlit', (w, j, b, refs), refs, [key])
            return True
        return False

    def apply_datmost(self, ci, x):
        _, a, k, u, pos, neg = self.D.clauses[ci]
        fa = self.fact.get(('c', x, a))
        if fa is None:
            return
        ws = []
        for w in sorted(self.dvals.get(x, {}).get(u, ())):
            if all(self.entail_lit(w, j, True) for j in pos) and \
                    all(self.entail_lit(w, j, False) for j in neg):
                ws.append(w)
        if len(ws) <= k:
            return
        ws = ws[:k + 1]
        prem = [fa]
        triples = []
        for w in ws:
            fd = self.fact[('d', x, u, w)]
            lr = [self.fact[('lit', w, j, True)] for j in pos] + \
                [self.fact[('lit', w, j, False)] for j in neg]
            prem += [fd] + lr
            triples.append((w, fd, lr))
        keys = [('veq', p, q) for p, q in pairs_of(ws)]
        line = mkline(keys)
        if self.has(line):
            return
        fids = self.step('datmost', (ci, x, triples), prem, [line])
        if line[0] == 'disj':
            if not keys:
                raise Clash(('empty', fids[0]))
            self.pending.append(fids[0])

    def add_r(self, x, k, y):
        self.out.setdefault(x, {}).setdefault(k, set()).add(y)
        self.inn.setdefault(y, {}).setdefault(k, set()).add(x)
        D = self.D
        # x --(+k)--> y and y --(-k)--> x
        for (src, dst, R) in ((x, y, (True, k)), (y, x, (False, k))):
            for ci in D.all_by_role.get(R, ()):
                a = D.clauses[ci][1]
                if self.has(('c', src, a)):
                    self.apply_all(ci, src, dst)
            for ci in D.atmost_by_role.get(R, ()):
                a = D.clauses[ci][1]
                if self.has(('c', src, a)):
                    self.apply_atmost(ci, src)
            for ci in D.some_by_role.get(R, ()):
                pass
        for ci, pos_i in D.chain_by_role.get(k, ()):
            self.apply_chain_at(ci, pos_i, x, y)

    def apply_chain_at(self, ci, i, x, y):
        _, body, S = self.D.clauses[ci]
        R = body[i]
        # the edge read along R: from s to t
        s, t = (x, y) if R[0] else (y, x)
        if not self.has(rtkey(R, s, t)):
            return
        lefts = self.paths_back(body[:i], s)
        if not lefts:
            return
        rights = self.paths_fwd(body[i + 1:], t)
        if not rights:
            return
        f_mid = self.fact[rtkey(R, s, t)]
        count = 0
        for (lxs, lrefs) in lefts:
            for (rxs, rrefs) in rights:
                xs = lxs + [s] + [t] + rxs
                start, end = xs[0], xs[-1]
                key = rtkey(S, start, end)
                if self.has(key):
                    continue
                refs = lrefs + [f_mid] + rrefs
                self.step('chain', (ci, xs, refs), refs, [key])
                count += 1
                if count > 10000:
                    return

    def paths_back(self, rs, t):
        """Paths ending at t along rs: list of (xs without t, refs)."""
        if not rs:
            return [([], [])]
        out = []
        R = rs[-1]
        flip = (not R[0], R[1])
        for s in self.neighbours(t, flip):
            f = self.fact.get(rtkey(R, s, t))
            if f is None:
                continue
            for (xs, refs) in self.paths_back(rs[:-1], s):
                out.append((xs + [s], refs + [f]))
                if len(out) > 1000:
                    return out
        return out

    def paths_fwd(self, rs, s):
        if not rs:
            return [([], [])]
        out = []
        R = rs[0]
        for t in self.neighbours(s, R):
            f = self.fact.get(rtkey(R, s, t))
            if f is None:
                continue
            for (xs, refs) in self.paths_fwd(rs[1:], t):
                out.append(([t] + xs, [f] + refs))
                if len(out) > 1000:
                    return out
        return out

    def add_d(self, x, u, w):
        self.dvals.setdefault(x, {}).setdefault(u, set()).add(w)
        D = self.D
        for ci in D.dsub_by.get(u, ()):
            v = D.clauses[ci][2]
            key = ('d', x, v, w)
            if not self.has(key):
                self.step('dsub', (ci, x, w), [self.fact[('d', x, u, w)]], [key])
        for a in list(self.label.get(x, ())):
            for ci in D.dall_by.get(a, ()):
                if D.clauses[ci][2] == u:
                    self.apply_dall(ci, x, w)
            for ci in D.datmost_by.get(a, ()):
                if D.clauses[ci][3] == u:
                    self.apply_datmost(ci, x)

    def add_lit(self, w, j, b):
        self.vlits.setdefault(w, set()).add((j, b))
        cur = self.vlits[w]
        if self.D.supported and self.D.emp_known.get(frozenset(cur)):
            raise Clash(('lits', w, [self.fact[('lit', w, j2, b2)] for (j2, b2) in sorted(cur)]))

    def data_clash(self):
        """At saturation: a value whose literal set the oracle declares
        empty (unknown sets are queued for the next round)."""
        for w, cur in self.vlits.items():
            if w in self.vdead or not cur:
                continue
            if self.D.emp(cur):
                raise Clash(('lits', w, [self.fact[('lit', w, j2, b2)] for (j2, b2) in sorted(cur)]))

    def merge(self, keep, gone, a):
        """eq keep gone from the nominal a, then rewrite the facts of `gone`."""
        f1 = self.fact[('c', keep, a)]
        f2 = self.fact[('c', gone, a)]
        fe = self.step('nomeq', (a, keep, gone), [f1, f2], [('eq', keep, gone)])[0]
        self.merge_eq(keep, gone, fe)

    def merge_eq(self, keep, gone, fe):
        if gone in self.dead:
            return
        self.dead.add(gone)
        for key, fid in list(self.fact.items()):
            if key[0] == 'disj' or gone not in key_elems(key) or key[0] in ('lit', 'veq', 'vne'):
                continue
            if key[0] == 'eq' and key[1] == keep and key[2] == gone:
                continue
            nk = subst_o(key, gone, keep)
            if not self.has(nk):
                self.step('eqrw', (fe, fid), [fe, fid], [nk])
        for a, z in list(self.nomelem.items()):
            if z == gone:
                self.nomelem[a] = keep

    def merge_veq(self, keep, gone, fe):
        if gone in self.vdead:
            return
        self.vdead.add(gone)
        for key, fid in list(self.fact.items()):
            if key[0] not in ('d', 'lit', 'veq', 'vne'):
                continue
            if key[0] == 'd' and key[3] != gone:
                continue
            if key[0] != 'd' and gone not in key_elems(key):
                continue
            if key[0] == 'veq' and key[1] == keep and key[2] == gone:
                continue
            nk = subst_v(key, gone, keep)
            if not self.has(nk):
                self.step('veqrw', (fe, fid), [fe, fid], [nk])

    # ---- agenda ----------------------------------------------------------
    def run(self, deadline):
        self.run1(deadline)
        self.data_clash()

    def run1(self, deadline):
        n = 0
        while self.agenda:
            n += 1
            if n % 2000 == 0 and time.time() > deadline:
                raise GiveUp()
            key = self.agenda.pop()
            t = key[0]
            if t == 'c':
                x, a = key[1], key[2]
                if x in self.dead:
                    continue
                if a in self.label.setdefault(x, set()):
                    continue
                self.label[x].add(a)
                self.add_c(x, a)
            elif t == 'r':
                x, k, y = key[1], key[2], key[3]
                if x in self.dead or y in self.dead:
                    continue
                self.add_r(x, k, y)
            elif t == 'eq':
                x, y = key[1], key[2]
                if x == y or x in self.dead or y in self.dead:
                    continue
                self.merge_eq(x, y, self.fact[key])
            elif t == 'd':
                x, u, w = key[1], key[2], key[3]
                if x in self.dead or w in self.vdead:
                    continue
                self.add_d(x, u, w)
            elif t == 'lit':
                w, j, b = key[1], key[2], key[3]
                if w in self.vdead:
                    continue
                self.add_lit(w, j, b)
            elif t == 'veq':
                w1, w2 = key[1], key[2]
                if w1 == w2 or w1 in self.vdead or w2 in self.vdead:
                    continue
                self.merge_veq(w1, w2, self.fact[key])


def index(D):
    D.gci_by, D.gci_empty = {}, []
    D.some_by, D.all_by, D.atmost_by = {}, {}, {}
    D.dsome_by, D.dall_by, D.datmost_by, D.dsub_by = {}, {}, {}, {}
    D.all_by_role, D.atmost_by_role, D.some_by_role = {}, {}, {}
    D.chain_by_role = {}
    for ci, cl in enumerate(D.clauses):
        k = cl[0]
        if k == 'gci':
            if not cl[1]:
                D.gci_empty.append(ci)
            for a in set(cl[1]):
                D.gci_by.setdefault(a, []).append(ci)
        elif k == 'some':
            D.some_by.setdefault(cl[1], []).append(ci)
            D.some_by_role.setdefault(cl[2], []).append(ci)
        elif k == 'all':
            D.all_by.setdefault(cl[1], []).append(ci)
            D.all_by_role.setdefault(cl[2], []).append(ci)
        elif k == 'atmost':
            D.atmost_by.setdefault(cl[1], []).append(ci)
            D.atmost_by_role.setdefault(cl[3], []).append(ci)
        elif k == 'chain':
            for i, R in enumerate(cl[1]):
                D.chain_by_role.setdefault(R[1], []).append((ci, i))
        elif k == 'dsome':
            D.dsome_by.setdefault(cl[1], []).append(ci)
        elif k == 'dall':
            D.dall_by.setdefault(cl[1], []).append(ci)
        elif k == 'datmost':
            D.datmost_by.setdefault(cl[1], []).append(ci)
        elif k == 'dsub':
            D.dsub_by.setdefault(cl[1], []).append(ci)


# ---- search ---------------------------------------------------------------

def disj_alts(log, fid):
    key = log.fact_key[fid]
    return list(key[1])


def search(st, deadline, budget):
    """Saturate; on a clash return a tree, otherwise split on a pending
    disjunction. Returns a tree or None."""
    try:
        st.run(deadline)
    except Clash as c:
        return ('close', st.ctx, c.info)
    if budget[0] <= 0:
        return None
    # pick a pending disjunction none of whose alternatives holds
    for fid in st.pending:
        alts = disj_alts(st.L, fid)
        if any(st.has(a) for a in alts):
            continue
        budget[0] -= 1
        subs = []
        for i, a in enumerate(alts):
            ctx = len(st.L.ctx_parent)
            st.L.ctx_parent.append(st.ctx)
            child = st.copy(ctx)
            child.pending = [f for f in child.pending if f != fid]
            # the assumption line: atom a (recorded as a step of kind 'assume')
            child.step('assume', (fid, i), [], [a])
            sub = search(child, deadline, budget)
            if sub is None:
                return None
            subs.append(sub)
        return ('split', st.ctx, fid, subs)
    return None


# ---- emission ---------------------------------------------------------------

def needed_steps(log, tree):
    need = set()
    stack = []

    def add_fid(fid):
        stack.append(log.fact_step[fid][0])

    def walk(t):
        if t[0] == 'close':
            info = t[2]
            if info[0] == 'empty':
                add_fid(info[1])
            elif info[0] == 'lits':
                for f in info[2]:
                    add_fid(f)
        else:
            add_fid(t[2])
            for s in t[3]:
                walk(s)
    walk(tree)
    while stack:
        si = stack.pop()
        if si in need:
            continue
        need.add(si)
        stp = log.steps[si]
        for f in stp['prem']:
            stack.append(log.fact_step[f][0])
        for key in stp['outs']:
            for x in key_elems(key):
                c = log.creator.get(x)
                if c is not None and c != si:
                    stack.append(c)
    return need


def step_text(log, stp, lm):
    k, a = stp['kind'], stp['args']
    L = lambda f: lm[f]
    p = stp['prem']
    if k == 'nom':
        return f"nom {a[0]} {a[1]}"
    if k == 'gci':
        return "gci {} {} {}".format(a[0], a[1], ' '.join(str(L(f)) for f in p)).rstrip()
    if k == 'ex':
        return f"ex {a[0]} {a[1]} {L(p[0])} {a[2]}"
    if k == 'exnom':
        return f"exnom {a[0]} {a[1]} {a[2]} {L(p[0])} {L(p[1])}"
    if k == 'all':
        return f"all {a[0]} {a[1]} {a[2]} {L(p[0])} {L(p[1])}"
    if k == 'chain':
        ci, xs, refs = a
        return "chain {} {} {} {}".format(ci, len(refs), ' '.join(map(str, xs)),
                                          ' '.join(str(L(f)) for f in refs)).rstrip()
    if k == 'atmost':
        ci, x, triples = a
        body = ' '.join(f"{y} {L(fr)} {L(fc)}" for y, fr, fc in triples)
        return f"atmost {ci} {x} {L(p[0])} {len(triples)} {body}"
    if k == 'nomeq':
        return f"nomeq {a[0]} {a[1]} {a[2]} {L(p[0])} {L(p[1])}"
    if k == 'eqrw':
        return f"eqrw {L(p[0])} {L(p[1])}"
    if k == 'dex':
        return f"dex {a[0]} {a[1]} {L(p[0])} {a[2]}"
    if k == 'dall':
        return f"dall {a[0]} {a[1]} {a[2]} {L(p[0])} {L(p[1])}"
    if k == 'datmost':
        ci, x, triples = a
        body = ' '.join("{} {} {} {}".format(w, L(fd), len(lr), ' '.join(str(L(f)) for f in lr)).rstrip()
                        for w, fd, lr in triples)
        return f"datmost {ci} {x} {L(p[0])} {len(triples)} {body}"
    if k == 'dsub':
        return f"dsub {a[0]} {a[1]} {a[2]} {L(p[0])}"
    if k == 'veqrw':
        return f"veqrw {L(p[0])} {L(p[1])}"
    if k == 'dlit':
        w, j, b, refs = a
        return "dlit {} {} {} {}".format(w, j, 1 if b else 0, ' '.join(str(L(f)) for f in refs)).rstrip()
    raise ValueError(k)


def emit(log, tree, need):
    out = []
    by_ctx = {}
    for si in sorted(need):
        by_ctx.setdefault(log.steps[si]['ctx'], []).append(si)

    def fids_of(si):
        return [f for f in range(len(log.fact_key)) if log.fact_step[f][0] == si]

    # fact ids per step, computed once
    step_fids = {}
    for f, (si, i) in enumerate(log.fact_step):
        if si in need:
            step_fids.setdefault(si, []).append(f)

    def emit_ctx(t, lm, nl):
        ctx = t[1]
        for si in by_ctx.get(ctx, []):
            stp = log.steps[si]
            if stp['kind'] == 'assume':
                continue
            out.append(step_text(log, stp, lm))
            for f in step_fids.get(si, []):
                lm[f] = nl
                nl += 1
        if t[0] == 'close':
            info = t[2]
            if info[0] == 'empty':
                out.append(f"close empty {lm[info[1]]}")
            elif info[0] == 'lits':
                w = info[1]
                out.append("close lits {} {}".format(w, ' '.join(str(lm[f]) for f in info[2])).rstrip())
            return
        _, _, dfid, subs = t
        ref = lm[dfid]
        nalts = len(subs)
        # split chain: split ref -> left alt0, right disj(rest) -> split ...
        cur = ref
        for i, sub in enumerate(subs):
            out.append(f"split {cur}")
            lm2 = dict(lm)
            # the assumption fact of the child context
            for si in by_ctx.get(sub[1], []):
                if log.steps[si]['kind'] == 'assume':
                    for f in step_fids.get(si, []):
                        lm2[f] = nl
            emit_ctx(sub, lm2, nl + 1)
            # right branch: the rest is pushed at line nl
            cur = nl
            nl += 1
        out.append(f"close empty {cur}")

    emit_ctx(tree, {}, 0)
    return out


def attempt(D, args, deadline):
    """One round: iterative deepening of the anonymous successors. Returns
    (log, tree, depth) with tree None when no refutation was found."""
    tree, log, depth = None, None, 0
    for depth in range(0, args.max_depth + 1):
        log = Log()
        st = State(D, log, 0, depth)
        try:
            for a in D.noms:
                st.nominal_element(a)
            tree = search(st, deadline, [args.branches])
        except Clash as c:
            tree = ('close', 0, c.info)
        except GiveUp:
            print(f"produce: time limit at depth {depth}", file=sys.stderr)
            return log, None, depth, True
        except RecursionError:
            print(f"produce: recursion limit at depth {depth}", file=sys.stderr)
            return log, None, depth, True
        if tree is not None:
            break
    return log, tree, depth, False


def ask_oracle(D, args, qs):
    """Decide the literal sets `qs` with `km-owl-reference --emp` (untrusted
    use of the checker's data oracle: only the checker's verdict on the
    final certificate counts)."""
    qs = sorted(qs, key=lambda L: sorted(L))
    qpath = (args.out or 'refute') + '.emp.q'
    with open(qpath, 'w') as f:
        for L in qs:
            f.write(' '.join(f"{j} {1 if b else 0}" for j, b in sorted(L)) + '\n')
    r = subprocess.run([args.oracle, '--procedure', 'refute', '--emp', qpath, args.ofn],
                       capture_output=True, text=True, timeout=args.oracle_timeout)
    ans = r.stdout.split()
    if r.returncode != 0 or len(ans) != len(qs):
        print(f"produce: oracle failed (rc {r.returncode}): {r.stderr[:200]}", file=sys.stderr)
        return False
    for L, a in zip(qs, ans):
        D.emp_known[L] = (a == '1')
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('dump')
    ap.add_argument('--out')
    ap.add_argument('--max-depth', type=int, default=3)
    ap.add_argument('--time-limit', type=float, default=240)
    ap.add_argument('--branches', type=int, default=2000)
    ap.add_argument('--oracle', help='km-owl-reference binary for --emp queries')
    ap.add_argument('--ofn', help='the ontology (for --emp queries)')
    ap.add_argument('--rounds', type=int, default=4)
    ap.add_argument('--oracle-timeout', type=float, default=280)
    args = ap.parse_args()
    t0 = time.time()
    D = Dump(args.dump)
    index(D)
    deadline = t0 + args.time_limit
    log, tree, depth = None, None, 0
    for rnd in range(args.rounds):
        D.queries = set()
        log, tree, depth, stop = attempt(D, args, deadline)
        if tree is not None or stop:
            break
        new = {L for L in D.queries if L not in D.emp_known}
        if not new or not args.oracle or not args.ofn:
            break
        print(f"produce: round {rnd}: {len(new)} oracle queries", file=sys.stderr)
        try:
            if not ask_oracle(D, args, new):
                break
        except subprocess.TimeoutExpired:
            print("produce: oracle timeout", file=sys.stderr)
            break
        print(f"produce: round {rnd}: {sum(1 for L in new if D.emp_known[L])} empty", file=sys.stderr)
    if tree is None:
        print("produce: no refutation found (unchecked)", file=sys.stderr)
        sys.exit(1)
    need = needed_steps(log, tree)
    lines = emit(log, tree, need)
    text = '\n'.join(lines) + '\n'
    if args.out:
        with open(args.out, 'w') as f:
            f.write(text)
    else:
        sys.stdout.write(text)
    print(f"produce: refutation with {len(lines)} lines, depth {depth}, "
          f"{len(log.steps)} steps explored, {time.time() - t0:.1f}s (unchecked)", file=sys.stderr)


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    main()
